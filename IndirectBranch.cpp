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
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Local.h"

namespace sllvm {

struct IndirectBranch : llvm::PassInfoMixin<IndirectBranch> {
    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        static std::random_device device;
        static std::mt19937 rng(device());
        static std::uniform_int_distribution<std::mt19937::result_type> distribution(0xfffff, 0xffffffff);

        std::map<llvm::BasicBlock *, size_t> blocks2key;
        std::map<llvm::BasicBlock *, size_t> blocks2index;
        std::vector<llvm::Constant *> globalBlocksArray;

        for (auto &F : M) {
            for (auto &BB : F) {
                llvm::BasicBlock *b = &BB;
                if (b == &F.getEntryBlock()) continue;
                blocks2key[b] = distribution(rng);

                auto *bbPtr = llvm::BlockAddress::get(&BB);
                auto *bbPtrInt = llvm::ConstantExpr::getPtrToInt(bbPtr, llvm::Type::getInt64Ty(F.getContext()), false);
                bbPtrInt = llvm::ConstantExpr::getAdd(bbPtrInt, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), blocks2key[b]));

                blocks2index[b] = globalBlocksArray.size();
                globalBlocksArray.push_back(bbPtrInt);
            }
        }
        auto *arrayType = llvm::ArrayType::get(llvm::Type::getInt64Ty(M.getContext()), globalBlocksArray.size());
        auto *bArray = llvm::ConstantArray::get(arrayType, llvm::ArrayRef<llvm::Constant *>(globalBlocksArray));
        auto *globBlockArray = new llvm::GlobalVariable(M, arrayType, false, llvm::GlobalValue::LinkageTypes::PrivateLinkage, bArray, "");
        replaceUse(M, blocks2key, globBlockArray, blocks2index);

        return llvm::PreservedAnalyses::all();
    }

    void replaceUse(llvm::Module &M, 
                    std::map<llvm::BasicBlock *, size_t> &blocks2key, 
                    llvm::GlobalVariable *globBlockArray, 
                    std::map<llvm::BasicBlock *, size_t> &functions2index) {
        for (auto &F : M) {
            for (auto &BB : F) {
                auto *instr = BB.getTerminator();
                if (auto *branchInstr = dyn_cast<llvm::BranchInst>(instr)) {
                    auto num = branchInstr->getNumSuccessors();
                    std::vector<llvm::Value *> successorAddress;
                    llvm::IndirectBrInst *idr = nullptr;
                    for (unsigned int i = 0; i < num; ++i) {
                        llvm::BasicBlock *b = branchInstr->getSuccessor(i);
                        if (blocks2key.count(b) == 0) {
                            goto nextiter;
                        }
                        llvm::IRBuilder<> builder(branchInstr);
                        
                        auto *indexGlob = new llvm::GlobalVariable(M, llvm::Type::getInt64Ty(F.getContext()), false, llvm::GlobalValue::LinkageTypes::PrivateLinkage, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), functions2index[b] * 8), "");
                        auto *arrayStart = builder.CreatePointerCast(globBlockArray, llvm::Type::getInt64Ty(F.getContext()));
                        auto *index = builder.CreateLoad(llvm::Type::getInt64Ty(F.getContext()), indexGlob);
                        auto *blockArrayPtrInt = builder.CreateAdd(arrayStart, index);
                        auto *blockArrayPtr = builder.CreateIntToPtr(blockArrayPtrInt, llvm::Type::getInt64PtrTy(F.getContext()));
                        auto *blockPtrInt = builder.CreateLoad(llvm::Type::getInt64Ty(F.getContext()), blockArrayPtr);
                        auto *blockPtrIntVal = builder.CreateSub(blockPtrInt, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), blocks2key[b]));
                        auto *blockPtr = builder.CreateIntToPtr(blockPtrIntVal, llvm::Type::getInt8PtrTy(F.getContext()));
                        successorAddress.push_back(blockPtr);
                    }
                    
                    if (successorAddress.size() == 1) {
                        llvm::IRBuilder<> builder(branchInstr);
                        idr = builder.CreateIndirectBr(successorAddress[0], 1);
                    } else if (branchInstr->isConditional()) {
                        llvm::IRBuilder<> builder(branchInstr);
                        auto *select = builder.CreateSelect(branchInstr->getCondition(), successorAddress[0], successorAddress[1]);
                        idr = builder.CreateIndirectBr(select, 2);
                    }
                    for (unsigned int i = 0; i < num; ++i) {
                        idr->addDestination(branchInstr->getSuccessor(i));
                    }
                    
                    branchInstr->eraseFromParent();
                nextiter:
                    continue;
                }
            }
        }
    }
};

}  // namespace sllvm

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "IndirectBranch", LLVM_VERSION_STRING, [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef Name, llvm::ModulePassManager &MPM,
                   llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                    if (Name == "indirBr") {
                        MPM.addPass(sllvm::IndirectBranch());
                        return true;
                    }
                    return false;
                });
        }};
}
