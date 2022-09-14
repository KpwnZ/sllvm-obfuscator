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
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/ValueMapper.h"

static llvm::cl::opt<int> bcfIt("bcf-iteration", llvm::cl::init(1), llvm::cl::desc("run bcf for x[=1] times"));

namespace sllvm {

static const uint32_t prime_array[] = {
    2,   3,   5,   7,   11,  13,  17,  19,  23,  29,
    31,  37,  41,  43,  47,  53,  59,  61,  67,  71,
    73,  79,  83,  89,  97,  101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173,
    179, 181, 191, 193, 197, 199, 211, 223, 227, 229,
    233, 239, 241, 251, 257, 263, 269, 271, 277, 281,
    283, 293, 307, 311, 313, 317, 331, 337, 347, 349,
    353, 359, 367, 373, 379, 383, 389, 397, 401, 409,
    419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
    467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
    547, 557, 563, 569, 571, 577, 587, 593, 599, 601,
    607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733,
    739, 743, 751, 757, 761, 769, 773, 787, 797, 809,
    811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
    877, 881, 883, 887, 907, 911, 919, 929, 937, 941,
    947, 953, 967, 971, 977, 983, 991, 997
};

struct BogusControlFlow : llvm::PassInfoMixin<BogusControlFlow> {

    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        std::vector<llvm::BasicBlock *> blocks;

        llvm::errs() << "run bcf for " << M.getName() << "\n";
        for(int i = 0; i < bcfIt; ++i) {
            for (auto &F : M) {
                handleFunction(M, F);
            }
        }

        return llvm::PreservedAnalyses::all();
    }

    void handleFunction(llvm::Module &M, llvm::Function &F) {
        if (!F.getInstructionCount()) return;
        std::vector<llvm::BasicBlock *> blocks;      // all blocks
        std::vector<llvm::BasicBlock *> candidates;  // all jmp candidates

        // collect AllocaInsts
        std::vector<llvm::AllocaInst *> allocaCandidates;

        for (auto &BB : F) {
            blocks.push_back(&BB);
        }

        for (auto &BB : F) {
            if (isa<llvm::InvokeInst>(BB.getTerminator())) {
                return;
            }
            if (&BB != &*(F.begin())) {
                // not begin block
                candidates.push_back(&BB);
            }
        }

        for (auto bptr : blocks) {
            createBogusFlow(M, F, bptr, candidates);
        }
    }

    uint32_t getPrime(uint32_t avoid = 0) {
        static std::random_device dev;
        static std::mt19937 rng(dev());
        std::uniform_int_distribution<std::mt19937::result_type> dist(0, sizeof(prime_array) / sizeof(uint32_t));

        uint32_t p = 0;
        do {
            p = prime_array[dist(rng)];
        } while (p == avoid);

        return p;
    }

    llvm::Value *createComparison(llvm::Module &M, llvm::Function &F, llvm::BasicBlock *b) {
        llvm::IRBuilder<> builder(b);

        std::vector<llvm::Instruction *> allocaCandidates;

        for (auto &inst : *b) {
            if (inst.getType()->isIntegerTy()) {
                allocaCandidates.push_back(&inst);
            }
        }

        uint32_t p1 = getPrime(), p2 = getPrime(p1);

        auto *prime1 = llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), p1);
        auto *prime2 = llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), p2);

        // choose variable from allocaCandidates
        static std::random_device dev;
        static std::mt19937 rng(dev());
        std::uniform_int_distribution<std::mt19937::result_type> dist(0, 0xfffff);

        llvm::Value *value1 = allocaCandidates.size() 
                              ? (llvm::Value *)(allocaCandidates[dist(rng) % allocaCandidates.size()]) 
                              : new llvm::GlobalVariable(M, llvm::Type::getInt64Ty(F.getContext()), false, llvm::GlobalValue::PrivateLinkage, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), dist(rng), false), ""); // llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), dist(rng));

        llvm::Value *value2 = allocaCandidates.size() 
                              ? (llvm::Value *)(allocaCandidates[dist(rng) % allocaCandidates.size()]) 
                              : new llvm::GlobalVariable(M, llvm::Type::getInt64Ty(F.getContext()), false, llvm::GlobalValue::PrivateLinkage, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), dist(rng), false), "");
        
        if (!allocaCandidates.size()) {
            value1 = builder.CreateLoad(llvm::Type::getInt64Ty(F.getContext()), value1, "");
            value2 = builder.CreateLoad(llvm::Type::getInt64Ty(F.getContext()), value2, "");
        }

        auto *a1 = llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), dist(rng));
        auto *a2 = llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), dist(rng));
        
        auto *v1 = builder.CreateIntCast(value1, llvm::Type::getInt64Ty(F.getContext()), true);
        auto *v2 = builder.CreateIntCast(value2, llvm::Type::getInt64Ty(F.getContext()), true);
        
        auto *v1low = builder.CreateAnd(v1, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), 0xfff));
        auto *v11   = builder.CreateOr(v1low, a1);
        auto *v12   = builder.CreateMul(v11, v11);
        auto *v13   = builder.CreateMul(prime1, v12);

        auto *v2low = builder.CreateAnd(v2, llvm::ConstantInt::get(llvm::Type::getInt64Ty(F.getContext()), 0xfff));
        auto *v21   = builder.CreateOr(v2low, a2);
        auto *v22   = builder.CreateMul(v21, v21);
        auto *v23   = builder.CreateMul(prime2, v22);

        auto *condition = new llvm::ICmpInst(*b, llvm::ICmpInst::ICMP_NE, v13, v23);
        return condition;
    }

    void createBogusFlow(llvm::Module &M, llvm::Function &F, llvm::BasicBlock *b, std::vector<llvm::BasicBlock *> &jmpCandidates) {
        static std::random_device dev;
        static std::mt19937 rng(dev());
        std::uniform_int_distribution<std::mt19937::result_type> dist(0, 0xfffff);

        // split the block
        auto in = b->getFirstNonPHIOrDbgOrLifetime();
        auto bb = b->splitBasicBlock(in);

        // create a fake block
        llvm::BasicBlock *cloneBB = nullptr;
        buildFakeBlock(bb, &cloneBB);
        assert(cloneBB != nullptr);

        // remove terminator from cloneBB and b
        b->getTerminator()->eraseFromParent();
        cloneBB->getTerminator()->eraseFromParent();

        auto *condition = createComparison(M, F, b);

        llvm::BranchInst::Create(bb, cloneBB, condition, b);
        llvm::BranchInst::Create(bb, cloneBB);

        auto instr2 = bb->end();
        auto bp2 = bb->splitBasicBlock(--instr2);

        bb->getTerminator()->eraseFromParent();
        
        // auto *condition2 = new llvm::FCmpInst(*bb, llvm::FCmpInst::FCMP_TRUE, LHS, RHS);
        auto *condition2 = createComparison(M, F, bb);
        llvm::BranchInst::Create(bp2, cloneBB, condition2, bb);
    }

    void buildFakeBlock(llvm::BasicBlock *target, llvm::BasicBlock **block) {
        llvm::ValueToValueMapTy vmap;
        *block = llvm::CloneBasicBlock(target, vmap, "clone", target->getParent());

        // remap value and phi node
        for (auto &inst : **block) {
            // remap value
            for (auto op = inst.op_begin(); op != inst.op_end(); op++) {
                auto *v = MapValue(*op, vmap, llvm::RF_None, 0);
                if (v != 0) *op = v;
            }

            // remap phi nodes
            if (llvm::PHINode *p = dyn_cast<llvm::PHINode>(&inst)) {
                for (unsigned int i = 0; i != p->getNumIncomingValues(); ++i) {
                    auto *v = MapValue(p->getIncomingBlock(i), vmap, llvm::RF_None, 0);
                    if (v != nullptr) {
                        p->setIncomingBlock(i, cast<llvm::BasicBlock>(v));
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
        LLVM_PLUGIN_API_VERSION, "BogusControlFlow", LLVM_VERSION_STRING, [](llvm::PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](llvm::StringRef Name, llvm::ModulePassManager &MPM,
                   llvm::ArrayRef<llvm::PassBuilder::PipelineElement>) {
                    if (Name == "bcf") {
                        MPM.addPass(sllvm::BogusControlFlow());
                        return true;
                    }
                    return false;
                });
        }};
}
