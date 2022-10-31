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
    llvm::Type *largestIntType;
    int largestIntSize;

    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        auto datalayout = llvm::DataLayout(&M);
        largestIntType = datalayout.getLargestLegalIntType(M.getContext());
        assert(largestIntType != nullptr);
        largestIntSize = datalayout.getTypeStoreSize(largestIntType);
        assert(largestIntSize != 0);

        static std::random_device device;
        static std::mt19937 rng(device());
        static std::uniform_int_distribution<std::mt19937::result_type> distribution(0x100, 0xfffff);

        std::map<llvm::Function *, size_t> functions2key;
        std::map<llvm::Function *, size_t> functions2index;
        std::vector<llvm::Constant *> globalFunctionArray;

        for (auto &F : M) {
            // for each function, replace it's use
            llvm::Function *function = &F;
            if (function->isIntrinsic()) continue;
            functions2key[function] = distribution(rng);

            auto *funcPtr = llvm::ConstantExpr::getBitCast(function, llvm::Type::getInt8PtrTy(F.getContext()));
            funcPtr = llvm::ConstantExpr::getPtrToInt(funcPtr, llvm::Type::getInt64Ty(F.getContext()), false);
            funcPtr = llvm::ConstantExpr::getAdd(funcPtr, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), functions2key[function]));

            functions2index[function] = globalFunctionArray.size();
            globalFunctionArray.push_back(funcPtr);
        }
        auto *arrayType = llvm::ArrayType::get(largestIntType, globalFunctionArray.size());
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

                            auto *indexGlob = new llvm::GlobalVariable(M, largestIntType, false, llvm::GlobalValue::LinkageTypes::PrivateLinkage, llvm::ConstantInt::get(largestIntType, functions2index[callee] * largestIntSize), "");
                            auto *arrayStart = builder.CreatePointerCast(globFuncArray, largestIntType);
                            auto *index = builder.CreateLoad(largestIntType, indexGlob);
                            auto *funcArrayPtrInt = builder.CreateAdd(arrayStart, index);
                            auto *funcArrayPtr = builder.CreateIntToPtr(funcArrayPtrInt, largestIntType);
                            auto *funcPtrInt = builder.CreateLoad(largestIntType, funcArrayPtr);
                            auto *funcPtrIntVal = builder.CreateSub(funcPtrInt, llvm::ConstantInt::get(largestIntType, functions2key[callee]));
                            auto *funcPtr = builder.CreateIntToPtr(funcPtrIntVal, llvm::PointerType::get(callee->getFunctionType(), 0));
                            callInstr->replaceUsesOfWith(callee, funcPtr);
                        }
                    }
                }
            }
        }
    }
};

}  // namespace sllvm

extern "C" void buildIndirectCall(llvm::ModulePassManager &MPM) {
    MPM.addPass(sllvm::IndirectCall());
}
