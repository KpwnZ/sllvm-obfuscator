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

struct InstructionObf : llvm::PassInfoMixin<InstructionObf> {

    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        llvm::errs() << "run instruction substitution\n";
        for(auto &F : M) {
            for(auto &BB : F) {
                for(auto instr = BB.begin(); instr != BB.end(); ++instr) {
                    // perform substitution for each instruction
                    auto *binop = dyn_cast<llvm::BinaryOperator>(instr);
                    performSubstitution(F, binop);
                }
            }
        }

        return llvm::PreservedAnalyses::all();        
    }

    void performSubstitution(llvm::Function &F, llvm::BinaryOperator *instr) {
        // auto *binop = dyn_cast<llvm::BinaryOperator>(instr);
        if(!instr) return;
        switch(instr->getOpcode()) {
        case llvm::Instruction::And:
            handleAND(F, instr);
            break;
        case llvm::Instruction::Or:
            handleOR(F, instr);
            break;
        case llvm::Instruction::Xor:
            handleXOR(F, instr);
            break;
        case llvm::Instruction::Add:
            handleADD(F, instr);
            break;
        case llvm::Instruction::Sub:
            handleSUB(F, instr);
            break;
        default:
            return;
        }
    }

    void handleAND(llvm::Function &F, llvm::BinaryOperator *instr) {
        // replace a & b with a = (a ^ ~b) & a
        auto &ctx = F.getContext();
        llvm::IRBuilder<> builder(instr);

        auto *op1 = instr->getOperand(0);
        auto *op2 = instr->getOperand(1);

        auto *v1 = builder.CreateNot(op2);
        auto *v2 = builder.CreateXor(op1, v1);
        auto *v3 = builder.CreateAnd(v2, op1);

        instr->replaceAllUsesWith(v3);
    }

    void handleOR(llvm::Function &F, llvm::BinaryOperator *instr) {
        // replace a | b with (a & b) | (!a & b) | (a & !b)
        auto &ctx = F.getContext();
        llvm::IRBuilder<> builder(instr);

        auto *op1 = instr->getOperand(0);
        auto *op2 = instr->getOperand(1);

        auto *v1 = builder.CreateNot(op1);
        auto *v2 = builder.CreateNot(op2);
        auto *v3 = builder.CreateAnd(op1, op2);
        auto *v4 = builder.CreateAnd(v2, op1);
        auto *v5 = builder.CreateAnd(v1, op2);
        auto *v6 = builder.CreateOr(v3, v4);
        auto *v7 = builder.CreateOr(v5, v6);

        instr->replaceAllUsesWith(v7);
    }

    void handleXOR(llvm::Function &F, llvm::BinaryOperator *instr) {
        // replace a ^ b with (!a & b) | (a & !b)
        auto &ctx = F.getContext();
        llvm::IRBuilder<> builder(instr);

        auto *op1 = instr->getOperand(0);
        auto *op2 = instr->getOperand(1);

        auto *v1 = builder.CreateNot(op1);
        auto *v2 = builder.CreateNot(op2);
        auto *v3 = builder.CreateAnd(v1, op2);
        auto *v4 = builder.CreateAnd(op1, v2);
        auto *v5 = builder.CreateOr(v3, v4);

        instr->replaceAllUsesWith(v5);
    }

    void handleADD(llvm::Function &F, llvm::BinaryOperator *instr) {
        // replace a + b with -(-a - b)
        // random mode a + b => -(-(a + r) - (b - r))
        auto &ctx = F.getContext();
        llvm::IRBuilder<> builder(instr);

        auto *op1 = instr->getOperand(0);
        auto *op2 = instr->getOperand(1);

        auto *v1 = builder.CreateNeg(op1);
        auto *v2 = builder.CreateSub(v1, op2);
        auto *v3 = builder.CreateNeg(v2);

        instr->replaceAllUsesWith(v3);
    }

    void handleSUB(llvm::Function &F, llvm::BinaryOperator *instr) {
        // replace a - b with -(-a + b)
        // random mode a - b => -(-a - r + b + r)
        auto &ctx = F.getContext();
        llvm::IRBuilder<> builder(instr);

        auto *op1 = instr->getOperand(0);
        auto *op2 = instr->getOperand(1);
        
        auto *v1 = builder.CreateNeg(op1);
        auto *v2 = builder.CreateAdd(v1, op2);
        auto *v3 = builder.CreateNeg(v2);

        instr->replaceAllUsesWith(v3);
    }
};

}  // namespace sllvm

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
    return {
        LLVM_PLUGIN_API_VERSION, "InstructionObf", LLVM_VERSION_STRING, [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef Name, llvm::ModulePassManager &FPM,
                   llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                    if (Name == "instrobf") {
                        FPM.addPass(sllvm::InstructionObf());
                        return true;
                    }
                    return false;
                });
        }};
}
