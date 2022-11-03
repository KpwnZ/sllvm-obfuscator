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
#include "llvm/IR/DataLayout.h"

namespace sllvm {

struct IndirectBranch : llvm::PassInfoMixin<IndirectBranch> {
    llvm::Type *largestIntType;
    
    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {

        auto datalayout = llvm::DataLayout(&M);
        largestIntType = datalayout.getLargestLegalIntType(M.getContext());
        assert(largestIntType != nullptr);
        
        static std::random_device device;
        static std::mt19937 rng(device());
        static std::uniform_int_distribution<std::mt19937::result_type> distribution(0x100, 0xfffff);

        std::map<llvm::BasicBlock *, size_t> blocks2key;
        std::map<llvm::BasicBlock *, size_t> blocks2index;
        std::vector<llvm::Constant *> globalBlocksArray;

        for (auto &F : M) {
            if (F.getBasicBlockList().size() <= 2) continue;    // we don't need to obfuscate the function with only one and two block
            for (auto &BB : F) {
                auto *instr = BB.getTerminator();
                if (auto *branchInstr = dyn_cast<llvm::BranchInst>(instr)) {
                    // now get the succesor
                    auto cnt = branchInstr->getNumSuccessors();
                    for (unsigned int i = 0; i < cnt; ++i) {
                        auto *b = branchInstr->getSuccessor(i);
                        
                        if(blocks2index.count(b) == 0) {
                            // add to vector
                            if (b == &F.getEntryBlock()) continue;
                            blocks2key[b] = distribution(rng);

                            auto *bbPtr = llvm::BlockAddress::get(&BB);
                            auto *bbPtrInt = llvm::ConstantExpr::getPtrToInt(bbPtr, largestIntType, false);
                            bbPtrInt = llvm::ConstantExpr::getAdd(bbPtrInt, llvm::ConstantInt::get(largestIntType, blocks2key[b]));

                            blocks2index[b] = globalBlocksArray.size();
                            globalBlocksArray.push_back(bbPtrInt);

                        }
                    }
                }
            }
        }
        auto *arrayType = llvm::ArrayType::get(largestIntType, globalBlocksArray.size());
        auto *bArray = llvm::ConstantArray::get(arrayType, llvm::ArrayRef<llvm::Constant *>(globalBlocksArray));
        auto *globBlockArray = new llvm::GlobalVariable(M, arrayType, false, llvm::GlobalValue::LinkageTypes::PrivateLinkage, bArray, "");
        replaceUse(M, blocks2key, globBlockArray, blocks2index);

        return llvm::PreservedAnalyses::all();
    }

    void replaceUse(llvm::Module &M, 
                    std::map<llvm::BasicBlock *, size_t> &blocks2key, 
                    llvm::GlobalVariable *globBlockArray, 
                    std::map<llvm::BasicBlock *, size_t> &blocks2index) {
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
                        
                        auto *indexGlob = new llvm::GlobalVariable(M, largestIntType, false, llvm::GlobalValue::LinkageTypes::PrivateLinkage, llvm::ConstantInt::get(largestIntType, blocks2index[b] * 8), "");
                        auto *arrayStart = builder.CreatePointerCast(globBlockArray, largestIntType);
                        auto *index = builder.CreateLoad(largestIntType, indexGlob);
                        auto *blockArrayPtrInt = builder.CreateAdd(arrayStart, index);
                        auto *blockArrayPtr = builder.CreateIntToPtr(blockArrayPtrInt, largestIntType);
                        auto *blockPtrInt = builder.CreateLoad(largestIntType, blockArrayPtr);
                        auto *blockPtrIntVal = builder.CreateSub(blockPtrInt, llvm::ConstantInt::get(largestIntType, blocks2key[b]));
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

extern "C" void buildIndirectBranch(llvm::ModulePassManager &MPM) {
    MPM.addPass(sllvm::IndirectBranch());
}

