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
        : Statement(Statement), nestingLevel(nestingLevel), rank(rank) {
        
        assert(llvm::isNoAliasCall(Statement) && 
            "Trying to create EWPT table entry with a value that is not an alias call!");    
    }

    void addConstraint(int variableIndex, EWPTIndexConstraint indexConstraint) {
        indexConstraints.push_back(indexConstraint);
        // indexConstraints.size() - 1 refers to the last inserted `b` index variable.
        constraints.push_back(EWPTConstraint(variableIndex, indexConstraints.size() - 1));
    }
};

class ElementWisePointsToMapping {
public:
    /**
     * Assumption: We are strongly typed, so e.g. int** a, the depth
     * of the ewpt mapping for a would be 2, as 2 pointers have to be followed
     * to get to the "outer part"(value)
     */
    int depth;
    std::vector<EWPTTableEntry> tableEntries;

    static const int DEPTH_UNINITIALIZED = -1;

    ElementWisePointsToMapping() : depth(DEPTH_UNINITIALIZED) {
    }
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

    void runOnBlock2(BasicBlock& block) {
        Loop *loop = LI->getLoopFor(&block);
        llvm::outs() << "BB: " << &block << " loop: ";
        if(loop) {
            llvm::outs() << *loop << "Induction variable " << loop->getCanonicalInductionVariable()->getName();
        } else {
            llvm::outs() << "none";
        }
        llvm::outs() << "\n";

        for(Instruction& CurrentInstruction : block.getInstList()) {
            if(llvm::isNoAliasCall(&CurrentInstruction)) {
                // If it's a malloc() call or similar.
                ElementWisePointsToMapping *newMapping = new ElementWisePointsToMapping();
                EWPTTableEntry tableEntry(&CurrentInstruction, 0, 0);
                newMapping->tableEntries.push_back(tableEntry);
                ewpts[&CurrentInstruction] = newMapping;
                llvm::outs() << "Found malloc instance: " << CurrentInstruction << "\n";
            } else if (StoreInst* CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                // Check if we're storing to something that we also allocated.
                llvm::Value* storeTo = getBasePointer(CurrentStoreInst);

                int depth = 0;
                while(1) {
                    for(auto valuePair : ewpts) {
                        const llvm::Value* compareTo = valuePair.first;
                        llvm::outs() << "Comparing " << *storeTo << " to " << *compareTo << "\n";
                        if(storeTo == compareTo) {
                            // If it's the "outer part", set the depth of the EWPT
                            if(!llvm::isIdentifiedObject(CurrentStoreInst->getValueOperand())) {
                                llvm::outs() << "Found store to outer part " << *CurrentStoreInst << "\n";
                                ElementWisePointsToMapping *match = valuePair.second;
                                if(match->depth != ElementWisePointsToMapping::DEPTH_UNINITIALIZED &&
                                    match->depth != depth) {
                                        llvm::errs() << "Found something we couldn't handle, sorry. (Trying to assign depth " << depth << " but depth is already " << match->depth << ")\n";
                                } else {
                                    match->depth = depth;
                                }
                            }
                            llvm::outs() << "Found store to existing EWPT: " << CurrentInstruction << "\n";
                        }
                    }


                    if (LoadInst *Ld = dyn_cast<LoadInst>(storeTo)) {
                        storeTo = getBasePointer(Ld);
                        depth++;
                    } else {
                        break;
                    }
                }
            }
        }
    }

    void runOnBlock(BasicBlock& block) {
        for(Instruction& CurrentInstruction : block.getInstList()) {
            if (StoreInst* CurrentStoreInst = dyn_cast<StoreInst>(&CurrentInstruction)) {
                // Recursively via GEPs find out what we're storing to,
                // e.g. in foo[x][y] = z we want foo, not &foo[x][y]
                //
                // Once we found the base, check if it's an EWPT.
                // If it's not, create a new EWPT associated with the base.
                //
                // "depth" is the number of GEPs/loads we had to go through to find the base.
                // Also figure out the indices of the GEPs/loads used.
                //
                // Check if the value of the store is a malloc or a different value.
                // If it's a different value, but the number of GEPs/loads does not match
                // the depth of the EWPT, error.
                //
                // Create a new EWPT table entry, at the found depth, with constraints for
                // the found indices.
                std::vector<Value*> Indices;
                findBaseEWPT(*CurrentStoreInst->getPointerOperand(), Indices);

                // Debug: print the indices.
                llvm::outs() << "Finding EWPT for store " << *CurrentStoreInst << " [";
                for(Value* value : Indices) {
                    llvm::outs() << *value << ", ";
                }
                llvm::outs() << "]";
            }
        }
    }

    /**
     * Try to follow a GEP/load chain to find the base EWPT.
     *
     * Anything that isn't itself retrieved from a load can be
     * considered an EWPT.
     *
     * @param myPointer The pointer for which to get the base EWPT.
     * @param indices A reference to a vector in which we'll store the indices used.
     */
    Value* findBaseEWPT(Value& myPointer, std::vector<Value*>& Indices) {
        if (GetElementPtrInst* CurrentGEPInst = dyn_cast<GetElementPtrInst>(&myPointer)) {
            // Remember the index of the GEP
            for(User::op_iterator IndexIterator = CurrentGEPInst->idx_begin(); IndexIterator != CurrentGEPInst->idx_end(); IndexIterator++) {
                Value* Index = IndexIterator->get();
                Indices.push_back(Index);
            }

            // Check what we're GEP'ing into
            if(LoadInst* CurrentLoadInst = dyn_cast<LoadInst>(CurrentGEPInst->getPointerOperand()->stripPointerCasts())) {
                // Okay, it's a load, recursively try to find the root EWPT.
                return findBaseEWPT(*CurrentLoadInst->getPointerOperand()->stripPointerCasts(), Indices);
            } else {
                // Nope, not a load, treat this as root EWPT.
                return CurrentGEPInst->getPointerOperand()->stripPointerCasts();
            }
        }

        // Not a GEP, we can't follow this pointer!
        return NULL;
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
