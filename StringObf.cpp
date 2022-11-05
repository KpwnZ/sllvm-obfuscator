#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instruction.h"

#include <random>
#include <vector>
#include <set>
#include <map>

static llvm::cl::opt<bool> DebugStringObf(
    "dbg-stringobf", llvm::cl::init(false),
    llvm::cl::desc("Debug string obfuscation pass"));
    
namespace sllvm {

class GlobalStringVariable {
private:
    std::vector<uint8_t> enc;
    std::vector<uint8_t> key;
    std::vector<uint8_t> str;
    llvm::GlobalVariable *glob;
    llvm::Instruction *referInstruction;
public:
    GlobalStringVariable(std::vector<uint8_t> &v1, std::vector<uint8_t> &v2, llvm::GlobalVariable *g) 
        : enc(v1), key(v2), glob(g) { }
    GlobalStringVariable(std::vector<uint8_t> &v1, std::vector<uint8_t> &v2, llvm::GlobalVariable *g, llvm::Instruction *i) 
        : enc(v1), key(v2), glob(g), referInstruction(i) { }
    GlobalStringVariable(std::vector<uint8_t> &v1, std::vector<uint8_t> &v2, llvm::GlobalVariable *g, llvm::Instruction *i, std::vector<uint8_t> &buf)
        : enc(v1), key(v2), str(buf), glob(g), referInstruction(i) { }
    llvm::GlobalVariable *getGlob() { return glob; }
    std::vector<uint8_t> &getEnc()  { return enc;  }
    std::vector<uint8_t> &getKey()  { return key;  }
    llvm::Instruction *getReferInstruction() { return referInstruction; }
};

bool isStringVariable(llvm::GlobalVariable *glob) {
    if (!glob->hasInitializer() || glob->hasExternalLinkage()) return false;
    
    llvm::StringRef section = glob->getSection();
    if (section == "llvm.metadata") return false;

    llvm::Constant *initializer = glob->getInitializer();
    if (!initializer) return false;

    if (isa<llvm::ConstantDataArray>(initializer)) {
        auto arr = cast<llvm::ConstantDataArray>(initializer);
        if (arr->isString()) return true;
    }
    return false;
}

bool isStringLinkage(llvm::GlobalVariable *glob) {
    if (!glob->hasExternalLinkage()) return false;

    llvm::Constant *initializer = glob->getInitializer();
    if (!initializer) return false;

    for (auto &op : initializer->operands()) {
        auto *g = dyn_cast<llvm::GlobalVariable>(op->stripPointerCasts());
        if(g && isStringVariable(g)) {
            return true;
        }
    }
    return false;
}

llvm::GlobalVariable *getStructString(llvm::GlobalVariable *glob) {
    if (glob->hasExternalLinkage()) return nullptr;
    if (!glob->hasInitializer()) return nullptr;
    llvm::Constant *initializer = glob->getInitializer();

    if (!isa<llvm::ConstantStruct>(initializer)) return nullptr;
    auto *structVar = dyn_cast<llvm::ConstantStruct>(initializer);

    for (auto &op : structVar->operands()) {
        auto *g = dyn_cast<llvm::GlobalVariable>(op->stripPointerCasts());
        if (g && isStringVariable(g)) {
            return g;
        }
    }
    return nullptr;
}

struct StringObf : llvm::PassInfoMixin<StringObf> {

    llvm::PreservedAnalyses run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
        std::set<llvm::GlobalVariable *> processed;
        std::map<llvm::GlobalVariable *, llvm::GlobalVariable *> mapEnc2Key;
        for(auto &F : M) {
            if (DebugStringObf) llvm::errs() << "run string obfuscation for " << F.getName() << "\n";
            processFunction(F, M, processed, mapEnc2Key);
        }
        return llvm::PreservedAnalyses::all();
    }

    void processFunction(llvm::Function &F, llvm::Module &M, 
                         std::set<llvm::GlobalVariable *> &processed, 
                         std::map<llvm::GlobalVariable *, llvm::GlobalVariable *> &mapEnc2Key) {

        std::vector<GlobalStringVariable> globalStrings;

        static std::random_device device;
        static std::mt19937 rng(device());
        static std::uniform_int_distribution<std::mt19937::result_type> distribution(0, 0xff);

        for(auto &BB : F) {
            for (auto &inst : BB) {
                for(auto &op : inst.operands()) {
                    auto *glob = dyn_cast<llvm::GlobalVariable>(op->stripPointerCasts());
                    const char *buf = nullptr;
                    size_t len = 0;
                    if(glob) {
                        if(isStringVariable(glob)) {
                            llvm::Constant *initializer = glob->getInitializer();
                            auto arr = cast<llvm::ConstantDataArray>(initializer);

                            buf = arr->getAsString().begin();
                            len = arr->getAsString().size();
                        } else if(isStringLinkage(glob)) {
                            // check operands
                            llvm::Constant *initializer = glob->getInitializer();
                            for(auto &op : initializer->operands()) {
                                auto *g = dyn_cast<llvm::GlobalVariable>(op->stripPointerCasts());
                                if(g) {
                                    if(isStringVariable(g)) {
                                        auto arr = cast<llvm::ConstantDataArray>(g->getInitializer());
                                        buf = arr->getAsString().begin();
                                        len = arr->getAsString().size();
                                        glob = g;
                                        break;
                                    }
                                }
                            }
                        } else if(auto *g = getStructString(glob)) {
                            llvm::ConstantDataArray *arr = dyn_cast<llvm::ConstantDataArray>(g->getInitializer());
                            buf = arr->getAsString().begin();
                            len = arr->getAsString().size();
                            glob = g;
                        }
                        if(!buf || !len) continue;

                        // generate xor key and encode the string
                        std::vector<uint8_t> enc_str, xor_key, ori;
                        for(size_t i = 0; i < len; ++i) {
                            uint8_t key = distribution(rng);
                            ori.push_back(buf[i]);
                            xor_key.push_back(key);
                            enc_str.push_back(buf[i] ^ key);
                        }

                        globalStrings.push_back(
                            {
                                enc_str, xor_key, glob, &inst, ori
                            }
                        );
                        llvm::Constant *enc_dt = llvm::ConstantDataArray::get(glob->getParent()->getContext(),
                                                                      llvm::ArrayRef<uint8_t>(enc_str));
                        // glob->setInitializer();
                        glob->setConstant(false);
                    }
                }
            }
        }
        // inject decode instruction for current function F
        injectDecodeInst(F, M, globalStrings, processed, mapEnc2Key);
    }

    void injectDecodeInst(llvm::Function &F, llvm::Module &M, 
                          std::vector<GlobalStringVariable> &globalStrings, 
                          std::set<llvm::GlobalVariable *> &processed, 
                          std::map<llvm::GlobalVariable *, llvm::GlobalVariable *> &mapEnc2Key) {
        // inject decode instruction
        auto &ctx = F.getContext();
        for(auto &g : globalStrings) {
            llvm::IRBuilder<> builder(g.getReferInstruction());

            auto *glob = g.getGlob();
            llvm::GlobalVariable *key_glob = nullptr;

            if(processed.find(glob) == processed.end()) {
                llvm::Constant *enc_dt = llvm::ConstantDataArray::get(glob->getParent()->getContext(),
                                                                      llvm::ArrayRef<uint8_t>(g.getEnc()));
                glob->setInitializer(enc_dt);
                processed.insert(glob);
                key_glob = new llvm::GlobalVariable(
                    M,
                    glob->getType()->getPointerElementType(),
                    false, 
                    glob->getLinkage(),
                    nullptr, 
                    glob->getName(),
                    nullptr,
                    glob->getThreadLocalMode(),
                    glob->getType()->getAddressSpace()
                );
                mapEnc2Key[glob] = key_glob;
                key_glob->setInitializer(llvm::ConstantDataArray::get(glob->getParent()->getContext(),
                                                                  llvm::ArrayRef<uint8_t>(g.getKey())));

            } else {
                key_glob = mapEnc2Key[glob];
            }
            auto *enc_str = builder.CreatePointerCast(glob, llvm::Type::getInt8PtrTy(ctx));
            auto *key_str = builder.CreatePointerCast(key_glob, llvm::Type::getInt8PtrTy(ctx));

            for (size_t i = 0; i < g.getEnc().size(); ++i) {
                auto *cur_p = builder.CreateGEP(llvm::Type::getInt8Ty(ctx), enc_str, llvm::ConstantInt::getSigned(llvm::IntegerType::get(ctx, 64), i));
                auto *cur_key_p = builder.CreateGEP(llvm::Type::getInt8Ty(ctx), key_str, llvm::ConstantInt::getSigned(llvm::IntegerType::get(ctx, 64), i));
                auto *cur = builder.CreateLoad(llvm::Type::getInt8Ty(ctx), cur_p, false);
                auto *cur_key = builder.CreateLoad(llvm::Type::getInt8Ty(ctx), cur_key_p, false);
                auto *cur32 = builder.CreateSExt(cur, llvm::Type::getInt32Ty(ctx));
                auto *cur_key32 = builder.CreateSExt(cur_key, llvm::Type::getInt32Ty(ctx));
                auto *xored = builder.CreateXor(cur32, cur_key32);
                auto *xored8 = builder.CreateTrunc(xored, llvm::Type::getInt8Ty(ctx));
                builder.CreateStore(xored8, cur_p);
                builder.CreateStore(llvm::ConstantInt::getSigned(llvm::IntegerType::get(ctx, 8), 0), cur_key_p);
            }

        }
    }
    
};

}

extern "C" void buildStringObf(llvm::ModulePassManager &MPM) {
    MPM.addPass(sllvm::StringObf());
}
