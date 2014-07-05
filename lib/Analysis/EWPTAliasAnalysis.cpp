#include "llvm/Analysis/AliasAnalysis.h"
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

class EWPTAliasAnalysis: public FunctionPass {
public:
    static char ID;

    std::map<const llvm::Value*, ElementWisePointsToMapping*> ewpts;

    EWPTAliasAnalysis() : FunctionPass(ID) { }

    virtual bool runOnFunction(Function& F) {
        for(const BasicBlock& Block : F) {
            runOnBlock(Block);
        }

        return true;
    }

    void runOnBlock(const BasicBlock& block) {
        for(const Instruction& CurrentInstruction : block.getInstList()) {
            if(llvm::isIdentifiedObject(&CurrentInstruction)) {
                // If it's a malloc() call or similar.
                ElementWisePointsToMapping *newMapping = new ElementWisePointsToMapping();
                EWPTTableEntry tableEntry(&CurrentInstruction, 0, 0);
                newMapping->tableEntries.push_back(tableEntry);
                ewpts[&CurrentInstruction] = newMapping;
                llvm::outs() << "Found malloc instance: " << CurrentInstruction << "\n";
            }
        }
    }
};

char EWPTAliasAnalysis::ID = 0;

static RegisterPass<EWPTAliasAnalysis> X("ewpt-aa", "Element-Wise-Points-To-Mapping Alias Analysis",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);