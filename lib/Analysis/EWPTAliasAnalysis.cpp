#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Pass.h"
#include "llvm/Analysis/RegionInfo.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Instruction.h"

using namespace llvm;

/**
 * @brief Describes a unique region of memory.
 */
class EWPTMemoryRegion {
private:
    const Value* IdentifiedValue;
public:
    EWPTMemoryRegion(const Value& IdentifiedValue)
        : IdentifiedValue(&IdentifiedValue) {
        // TODO: add iteration vector to constructor
    }
};

class EWPTConstraint {
};

class ElementWisePointsToMapping {
public:
    std::vector<EWPTMemoryRegion> mapping;
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
                newMapping->mapping.push_back(EWPTMemoryRegion(CurrentInstruction));
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