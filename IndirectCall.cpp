#include <map>
#include <random>
#include <set>
#include <vector>

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

namespace sllvm {

struct IndirectCall : llvm::PassInfoMixin<IndirectCall> {

    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        static std::random_device device;
        static std::mt19937 rng(device());
        static std::uniform_int_distribution<std::mt19937::result_type> distribution(0xfffff, 0xffffffff);

        std::map<llvm::Function *, size_t> functions2key;
        std::map<llvm::Function *, size_t> functions2index;
        std::vector<llvm::Constant *> globalFunctionArray;

        for (auto &F : M) {
            // for each function, replace it's use
            llvm::Function *function = &F;
            functions2key[function] = distribution(rng);

            auto *funcPtr = llvm::ConstantExpr::getBitCast(function, llvm::Type::getInt8PtrTy(F.getContext()));
            funcPtr = llvm::ConstantExpr::getPtrToInt(funcPtr, llvm::Type::getInt64Ty(F.getContext()), false);
            funcPtr = llvm::ConstantExpr::getAdd(funcPtr, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), functions2key[function]));

            functions2index[function] = globalFunctionArray.size();
            globalFunctionArray.push_back(funcPtr);
        }
        auto *arrayType = llvm::ArrayType::get(llvm::Type::getInt64Ty(M.getContext()), globalFunctionArray.size());
        auto *funcArray = llvm::ConstantArray::get(arrayType, llvm::ArrayRef<llvm::Constant *>(globalFunctionArray));
        auto *globFuncArray = new llvm::GlobalVariable(M, arrayType, false, llvm::GlobalValue::LinkageTypes::PrivateLinkage, funcArray, "");
        replaceUse(M, functions2key, globFuncArray, functions2index);

        return llvm::PreservedAnalyses::all();
    }

    void replaceUse(llvm::Module &M, std::map<llvm::Function *, size_t> &functions2key, llvm::GlobalVariable *globFuncArray, std::map<llvm::Function *, size_t> &functions2index) {
        
        for (auto &F : M) {
            for (auto &BB : F) {
                for (auto &instr : BB) {
                    if (auto *callInstr = dyn_cast<llvm::CallInst>(&instr)) {
                        if (auto *intrinsic = dyn_cast<llvm::IntrinsicInst>(&instr)) {
                            continue;
                        }
                        // get call instruction, check callee
                        if (auto *callee = callInstr->getCalledFunction()) {
                            // replace origin callee with array[idx]
                            if (functions2key.count(callee) == 0) {
                                // no key
                                continue;
                            }
                            llvm::IRBuilder<> builder(callInstr);

                            auto *indexGlob = new llvm::GlobalVariable(M, llvm::Type::getInt64Ty(F.getContext()), false, llvm::GlobalValue::LinkageTypes::PrivateLinkage, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), functions2index[callee] * 8), "");

                            auto *arrayStart = builder.CreatePointerCast(globFuncArray, llvm::Type::getInt64Ty(F.getContext()));
                            auto *index = builder.CreateLoad(llvm::Type::getInt64Ty(F.getContext()), indexGlob);
                            auto *funcArrayPtrInt = builder.CreateAdd(arrayStart, index);
                            auto *funcArrayPtr = builder.CreateIntToPtr(funcArrayPtrInt, llvm::Type::getInt64PtrTy(F.getContext()));
                            auto *funcPtrInt = builder.CreateLoad(llvm::Type::getInt64Ty(F.getContext()), funcArrayPtr);
                            auto *funcPtrIntVal = builder.CreateSub(funcPtrInt, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), functions2key[callee]));
                            auto *funcPtr = builder.CreateIntToPtr(funcPtrIntVal, llvm::PointerType::get(callee->getFunctionType(), 0));
                            callInstr->replaceUsesOfWith(callee, funcPtr);
                        }
                    }
                }
            }
        }
    }
};

}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "IndirectCall", LLVM_VERSION_STRING, [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef Name, llvm::ModulePassManager &MPM,
                   llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                    if (Name == "indircall") {
                        MPM.addPass(sllvm::IndirectCall());
                        return true;
                    }
                    return false;
                });
        }};
}
