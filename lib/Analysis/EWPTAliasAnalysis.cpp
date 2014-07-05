#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"

using namespace llvm;

class EWPTConstraint {
public:
    /** The index of the variable this constraint applies to. */
    const int appliedVariable;

    /** The temporary index that we constrain this variable to.
    *  Temporary indexes represent either `i` or `i-`.
    */
    const int appliedIndex;

    EWPTConstraint(int appliedVariable, int appliedIndex)
        : appliedVariable(appliedVariable), appliedIndex(appliedIndex) { }
};


class EWPTIndexConstraint {
public:
    const bool isPreviousIndex;

    EWPTIndexConstraint(bool isPreviousIndex) : isPreviousIndex(isPreviousIndex) {

    }
};

class EWPTTableEntry {
public:
    /**
     * The statement describing the memory object we're
     * referincing in this mapping, for instance this could
     * be a `malloc()` call.
     */
    const llvm::Value* Statement;

    /**
     * The nesting level of the loops containing @Statement
     */
    const int nestingLevel;

    /**
     * The rank of the ewpt mapping, that is, the amount of its
     * parameters. For instance, in p(x1, x2), the rank would be
     * 2.
     */
    const int rank;

    std::vector<EWPTConstraint> constraints;
    std::vector<EWPTIndexConstraint> indexConstraints;

    int getSubscriptVariable(int index) const {
        return index;
    }

    int getParameterVariable(int index) const {
        return nestingLevel + index;
    }

    EWPTTableEntry(const llvm::Value* Statement, int nestingLevel, int rank)
        : Statement(Statement), nestingLevel(nestingLevel), rank(rank) { }

    void addConstraint(int variableIndex, EWPTIndexConstraint indexConstraint) {
        indexConstraints.push_back(indexConstraint);
        // indexConstraints.size() - 1 refers to the last inserted `b` index variable.
        constraints.push_back(EWPTConstraint(variableIndex, indexConstraints.size() - 1));
    }
};

class ElementWisePointsToMapping {
public:
    std::vector<EWPTTableEntry> tableEntries;
};

Value *getPointerOperand(Instruction &Inst) {
  if (LoadInst *load = dyn_cast<LoadInst>(&Inst))
    return load->getPointerOperand();
  else if (StoreInst *store = dyn_cast<StoreInst>(&Inst))
    return store->getPointerOperand();
  else if (GetElementPtrInst *gep = dyn_cast<GetElementPtrInst>(&Inst))
    return gep->getPointerOperand();

  return 0;
}

class EWPTAliasAnalysis: public FunctionPass {
public:
    static char ID;

    std::map<const llvm::Value*, ElementWisePointsToMapping*> ewpts;

    /// @brief Analysis passes used.
    //@{
    ScalarEvolution *SE;
    LoopInfo *LI;
    //@}

    EWPTAliasAnalysis() : FunctionPass(ID) { }

    virtual bool runOnFunction(Function& F) {
        // Initialization.
        SE = &getAnalysis<ScalarEvolution>();
        LI = &getAnalysis<LoopInfo>();

        // The actual analysis.
        for(BasicBlock& Block : F) {
            runOnBlock(Block);
        }

        return true;
    }

    Value *getBasePointer(Instruction* MemoryAccess) {
        Value *Ptr = getPointerOperand(*MemoryAccess);
        Loop *L = LI->getLoopFor(MemoryAccess->getParent());
        const SCEV *AccessFunction = SE->getSCEVAtScope(Ptr, L);
        const SCEVUnknown *BasePointer;
        Value *BaseValue;

        BasePointer = dyn_cast<SCEVUnknown>(SE->getPointerBase(AccessFunction));

        if (!BasePointer)
          return NULL;

        BaseValue = BasePointer->getValue();
        return BaseValue;
    }

    void runOnBlock(BasicBlock& block) {
        for(Instruction& CurrentInstruction : block.getInstList()) {
            if(llvm::isIdentifiedObject(&CurrentInstruction)) {
                // If it's a malloc() call or similar.
                ElementWisePointsToMapping *newMapping = new ElementWisePointsToMapping();
                EWPTTableEntry tableEntry(&CurrentInstruction, 0, 0);
                newMapping->tableEntries.push_back(tableEntry);
                ewpts[&CurrentInstruction] = newMapping;
                llvm::outs() << "Found malloc instance: " << CurrentInstruction << "\n";
            } else if (StoreInst* CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                // Check if we're storing to something that we also allocated.
                llvm::Value* storeTo = getBasePointer(CurrentStoreInst);

                while(1) {
                    for(auto valuePair : ewpts) {
                        const llvm::Value* compareTo = valuePair.first;
                        llvm::outs() << "Comparing " << *storeTo << " to " << *compareTo << "\n";
                        if(storeTo == compareTo) {
                            llvm::outs() << "Found store to existing EWPT: " << CurrentInstruction << "\n";
                        }
                    }


                    if (LoadInst *Ld = dyn_cast<LoadInst>(storeTo)) {
                        storeTo = getBasePointer(Ld);
                    } else {
                        break;
                    }
                }
            }
        }
    }

    void getAnalysisUsage(AnalysisUsage &AU) const {
        AU.addRequired<LoopInfo>();
        AU.addRequired<ScalarEvolution>();
        AU.setPreservesAll();
    }
};

char EWPTAliasAnalysis::ID = 0;

static RegisterPass<EWPTAliasAnalysis> X("ewpt-aa", "Element-Wise-Points-To-Mapping Alias Analysis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);