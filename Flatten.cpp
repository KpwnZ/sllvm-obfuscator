#include <map>
#include <random>
#include <set>
#include <vector>

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Local.h"

static llvm::cl::opt<bool> DebugFlatten(
    "dbg-flatten", llvm::cl::init(false),
    llvm::cl::desc("Debug flatten pass"));

namespace sllvm {

// xorshift*
uint64_t gen() {
    static uint64_t x = 1;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    return x * 0x2545F4914F6CDD1DULL;
}

struct Flatten : llvm::PassInfoMixin<Flatten> {

    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        std::vector<llvm::BasicBlock *> blocks;

        for (auto &F : M) {
            if (DebugFlatten) llvm::errs() << "Handle " << F.getName() << "\n";
            handleFunction(F);
        }

        return llvm::PreservedAnalyses::all();
    }

    void handleFunction(llvm::Function &F) {
        if (F.getInstructionCount() <= 1) return;
        std::vector<llvm::BasicBlock *> blocks;      // all blocks

        for (auto &BB : F) {
            if (isa<llvm::InvokeInst>(BB.getTerminator())) {
                return;
            }
            blocks.push_back(&BB);
        }

        auto size = blocks.size();
        for (auto i = 1ul; i < size; ++i) {
            auto *b = blocks[i];
            auto in = b->getFirstNonPHIOrDbgOrLifetime();
            auto *bb = b->splitBasicBlock(in);
            blocks.push_back(bb);
        }

        if (blocks.size() <= 1) return;

        if (DebugFlatten) {
            llvm::errs() << "Got " << blocks.size() << " blocks\n";
        }

        blocks.erase(blocks.begin());
        auto *insert = &(*F.begin());
        
        auto *br = dyn_cast<llvm::BranchInst>(insert->getTerminator());

        if((br != nullptr && br->isConditional()) || insert->getTerminator()->getNumSuccessors() > 1) {
            auto i = insert->end();
            --i;
            if(insert->size() > 1) --i;

            auto *tmpBB = insert->splitBasicBlock(i, "");
            blocks.insert(blocks.begin(), tmpBB);
        }
        insert->getTerminator()->eraseFromParent();

        // now build the main dispatcher
        if (DebugFlatten) {
            llvm::errs() << "build main dispatcher\n";  
        }

        auto val1 = gen();
        auto *switchVar = new llvm::AllocaInst(llvm::Type::getInt64Ty(F.getContext()), 0, "", insert);
        new llvm::StoreInst(llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), val1), switchVar, insert);

        auto *loopEntry = llvm::BasicBlock::Create(F.getContext(), "", &F, insert);
        auto *loopEnd = llvm::BasicBlock::Create(F.getContext(), "", &F, insert);

        auto *load = new llvm::LoadInst(llvm::Type::getInt64Ty(F.getContext()), switchVar, "", loopEntry);

        insert->moveBefore(loopEntry);
        llvm::BranchInst::Create(loopEntry, insert);

        auto *swDefault = llvm::BasicBlock::Create(F.getContext(), "", &F, loopEnd);
        llvm::BranchInst::Create(loopEnd, swDefault);

        auto *switchInst = llvm::SwitchInst::Create(&*F.begin(), swDefault, 0, loopEntry);
        switchInst->setCondition(load);

        insert->getTerminator()->eraseFromParent();
        llvm::BranchInst::Create(loopEntry, &*F.begin()); 

        if (DebugFlatten) {
            llvm::errs() << "create switch cases\n";
        }

        // int casenum = 0;

        switchInst->addCase(dyn_cast<llvm::ConstantInt>(llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), val1)), blocks[0]);
        for (auto i = 1ul; i < blocks.size(); ++i) {
            auto *b = blocks[i];
            b->moveBefore(loopEnd);
            auto labelValue = llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), gen());
            switchInst->addCase(dyn_cast<llvm::ConstantInt>(labelValue), b);
        }

        if (DebugFlatten) {
            llvm::errs() << "update switch cases\n";
        }
        for (auto *b : blocks) {
            if (b->getTerminator()->getNumSuccessors() == 0) continue;

            if (b->getTerminator()->getNumSuccessors() == 1) {
                auto *successor = b->getTerminator()->getSuccessor(0);
                b->getTerminator()->eraseFromParent();

                auto *label = switchInst->findCaseDest(successor);

                if (label == nullptr) {
                    label = dyn_cast<llvm::ConstantInt>(llvm::ConstantInt::get(switchInst->getCondition()->getType(), gen()));
                }

                new llvm::StoreInst(label, load->getPointerOperand(), b);

                llvm::BranchInst::Create(loopEnd, b);
            } else if (b->getTerminator()->getNumSuccessors() == 2) {
                auto *casetrue =
                    switchInst->findCaseDest(b->getTerminator()->getSuccessor(0));
                auto *casefalse =
                    switchInst->findCaseDest(b->getTerminator()->getSuccessor(1));

                if (casetrue == nullptr) {
                    casetrue = dyn_cast<llvm::ConstantInt>(llvm::ConstantInt::get(switchInst->getCondition()->getType(), gen()));
                } 
                if (casefalse == nullptr) {
                    casefalse = dyn_cast<llvm::ConstantInt>(llvm::ConstantInt::get(switchInst->getCondition()->getType(), gen()));
                }

                auto *br = cast<llvm::BranchInst>(b->getTerminator());
                auto *sel = llvm::SelectInst::Create(br->getCondition(), casetrue, casefalse, "", b->getTerminator());
                
                b->getTerminator()->eraseFromParent();
                
                new llvm::StoreInst(sel, load->getPointerOperand(), b);
                llvm::BranchInst::Create(loopEnd, b);
            }
        }

        auto *loadInstEnd = new llvm::LoadInst(llvm::Type::getInt64Ty(F.getContext()), switchVar, "", loopEnd);
        auto *switchInstEnd = llvm::SwitchInst::Create(&*F.begin(), loopEntry, 0, loopEnd);
        switchInstEnd->setCondition(loadInstEnd);

        for(auto *b : blocks) {
            auto *label = switchInst->findCaseDest(b);
            if(label != nullptr) {
                switchInstEnd->addCase(dyn_cast<llvm::ConstantInt>(label), b);
            }
        }
        if (DebugFlatten) {
            llvm::errs() << "done\n";
        }

        demotePhi(F);
        while(fixValue(F)) { };
    }

    void demotePhi(llvm::Function &F) {
        
        // flattening will break the order relation between basic block
        // but phi instruction depends on its precursor
        // so we need to demote phi node to stack 

        std::vector<llvm::PHINode *> phi;

        for (auto &BB : F) {
            for (auto &i : BB) {
                if (auto *p = dyn_cast<llvm::PHINode>(&i)) {
                    phi.push_back(p);
                }
            }
        }

        for (auto *i : phi) {
            llvm::DemotePHIToStack(i, F.begin()->getTerminator());
        }

        return;
    }

    size_t fixValue(llvm::Function &F) {

        // fix "Instruction does not dominate all uses"

        std::vector<llvm::Instruction *> alloca;

        for (auto && BB : F) {
            for (auto &i : BB) {
                if (isa<llvm::AllocaInst>(&i) || i.getParent() == &F.getEntryBlock()) {
                    continue;
                }
                if (i.isUsedOutsideOfBlock(&BB)) {
                    alloca.push_back(&i);
                }
            }
        }
        if (!alloca.size()) return 0;
        
        for (auto *i : alloca) {
            llvm::DemoteRegToStack(*i, false, F.begin()->getTerminator());
        }

        return alloca.size();

    }
};

}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "Flatten", LLVM_VERSION_STRING, [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef Name, llvm::ModulePassManager &MPM,
                   llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                    if (Name == "flatten") {
                        MPM.addPass(sllvm::Flatten());
                        return true;
                    }
                    return false;
                });
        }};
}
