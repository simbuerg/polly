//===- Dependences.cpp - Calculate dependency information for a Scop. -----===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Calculate the data dependency relations for a Scop using ISL.
//
// The integer set library (ISL) from Sven, has a integrated dependency analysis
// to calculate data dependences. This pass takes advantage of this and
// calculate those dependences a Scop.
//
// The dependences in this pass are exact in terms that for a specific read
// statement instance only the last write statement instance is returned. In
// case of may writes a set of possible write instances is returned. This
// analysis will never produce redundant dependences.
//
//===----------------------------------------------------------------------===//
//
#include "polly/Dependences.h"
#include "polly/LinkAllPasses.h"
#include "polly/Options.h"
#include "polly/ScopInfo.h"
#include "polly/Support/GICHelper.h"
#include "llvm/Support/Debug.h"

#include <isl/Context.h>
#include <isl/PwAff.hpp>
#include <isl/Space.hpp>
#include <isl/Set.hpp>
#include <isl/Map.hpp>
#include <isl/UnionMap.hpp>
#include <isl/UnionSet.hpp>
#include <isl/Printer.hpp>

using namespace isl;
using namespace polly;
using namespace llvm;

#define DEBUG_TYPE "polly-dependence"

static cl::opt<int> OptComputeOut(
    "polly-dependences-computeout",
    cl::desc("Bound the dependence analysis by a maximal amount of "
             "computational steps"),
    cl::Hidden, cl::init(250000), cl::ZeroOrMore, cl::cat(PollyCategory));

static cl::opt<bool> LegalityCheckDisabled(
    "disable-polly-legality", cl::desc("Disable polly legality check"),
    cl::Hidden, cl::init(false), cl::ZeroOrMore, cl::cat(PollyCategory));

enum AnalysisType { VALUE_BASED_ANALYSIS, MEMORY_BASED_ANALYSIS };

static cl::opt<enum AnalysisType> OptAnalysisType(
    "polly-dependences-analysis-type",
    cl::desc("The kind of dependence analysis to use"),
    cl::values(clEnumValN(VALUE_BASED_ANALYSIS, "value-based",
                          "Exact dependences without transitive dependences"),
               clEnumValN(MEMORY_BASED_ANALYSIS, "memory-based",
                          "Overapproximation of dependences"),
               clEnumValEnd),
    cl::Hidden, cl::init(VALUE_BASED_ANALYSIS), cl::ZeroOrMore,
    cl::cat(PollyCategory));

//===----------------------------------------------------------------------===//
Dependences::Dependences() : ScopPass(ID) {
  Raw.reset(nullptr);
  War.reset(nullptr);
  Waw.reset(nullptr);
  Red.reset(nullptr);
  TcRed.reset(nullptr);
}

void Dependences::collectInfo(Scop &S, isl::UnionMap &Read,
                              isl::UnionMap &Write, isl::UnionMap &MayWrite,
                              isl::UnionMap &AccessSchedule,
                              isl::UnionMap &StmtSchedule) {
  SmallPtrSet<const Value *, 8> ReductionBaseValues;
  for (ScopStmt *Stmt : S)
    for (MemoryAccess *MA : *Stmt)
      if (MA->isReductionLike())
        ReductionBaseValues.insert(MA->getBaseAddr());

  for (ScopStmt *Stmt : S) {
    for (MemoryAccess *MA : *Stmt) {
      isl::Set Domcp = isl::Set(Stmt->getDomain());
      isl::Map AccDom = isl::Map(MA->getAccessRelation());

      AccDom = AccDom.intersectDomain(std::move(Domcp));

      if (ReductionBaseValues.count(MA->getBaseAddr())) {
        // Wrap the access domain and adjust the scattering accordingly.
        //
        // An access domain like
        //   Stmt[i0, i1] -> MemAcc_A[i0 + i1]
        // will be transformed into
        //   [Stmt[i0, i1] -> MemAcc_A[i0 + i1]] -> MemAcc_A[i0 + i1]
        //
        // The original scattering looks like
        //   Stmt[i0, i1] -> [0, i0, 2, i1, 0]
        // but as we transformed the access domain we need the scattering
        // to match the new access domains, thus we need
        //   [Stmt[i0, i1] -> MemAcc_A[i0 + i1]] -> [0, i0, 2, i1, 0]

        AccDom = AccDom.rangeMap();

        isl::Map StmtScatter = isl::Map(Stmt->getScattering());
        isl::Set ScatterDom = AccDom.domain();
        isl::Set ScatterRan = StmtScatter.range();
        isl::Map Scatter = isl::Map::fromDomainAndRange(std::move(ScatterDom),
                                                        std::move(ScatterRan));

        for (unsigned u = 0, e = Stmt->getNumIterators(); u != e; u++)
          Scatter = Scatter.equate(isl::DTOut, 2 * u + 1, isl::DTIn, u);
        AccessSchedule = AccessSchedule.addMap(Scatter);
      }

      if (MA->isRead())
        Read = Read.addMap(AccDom);
      else
        Write = Write.addMap(AccDom);
    }
    StmtSchedule = StmtSchedule.addMap(isl::Map(Stmt->getScattering()));
  }


  isl::Set AssumedContext(S.getAssumedContext());
  StmtSchedule = StmtSchedule.intersectParams(AssumedContext);
}

/// @brief Compute the privatization dependences for a given dependency @p Map
///
/// Privatization dependences are widened original dependences which originate
/// or end in a reduction access. To compute them we apply the transitive close
/// of the reduction dependences (which maps each iteration of a reduction
/// statement to all following ones) on the RAW/WAR/WAW dependences. The
/// dependences which start or end at a reduction statement will be extended to
/// depend on all following reduction statement iterations as well.
/// Note: "Following" here means according to the reduction dependences.
///
/// For the input:
///
///  S0:   *sum = 0;
///        for (int i = 0; i < 1024; i++)
///  S1:     *sum += i;
///  S2:   *sum = *sum * 3;
///
/// we have the following dependences before we add privatization dependences:
///
///   RAW:
///     { S0[] -> S1[0]; S1[1023] -> S2[] }
///   WAR:
///     {  }
///   WAW:
///     { S0[] -> S1[0]; S1[1024] -> S2[] }
///   RED:
///     { S1[i0] -> S1[1 + i0] : i0 >= 0 and i0 <= 1022 }
///
/// and afterwards:
///
///   RAW:
///     { S0[] -> S1[i0] : i0 >= 0 and i0 <= 1023;
///       S1[i0] -> S2[] : i0 >= 0 and i0 <= 1023}
///   WAR:
///     {  }
///   WAW:
///     { S0[] -> S1[i0] : i0 >= 0 and i0 <= 1023;
///       S1[i0] -> S2[] : i0 >= 0 and i0 <= 1023}
///   RED:
///     { S1[i0] -> S1[1 + i0] : i0 >= 0 and i0 <= 1022 }
///
/// Note: This function also computes the (reverse) transitive closure of the
///       reduction dependences.
void Dependences::addPrivatizationDependences() {
  // The transitive closure might be over approximated, thus could lead to
  // dependency cycles in the privatization dependences. To make sure this
  // will not happen we remove all negative dependences after we computed
  // the transitive closure.
  TcRed.reset(new isl::UnionMap(Red->transitiveClosure(0)));

  // FIXME: Apply the current schedule instead of assuming the identity schedule
  //        here. The current approach is only valid as long as we compute the
  //        dependences only with the initial (identity schedule). Any other
  //        schedule could change "the direction of the backward dependences" we
  //        want to eliminate here.
  isl::UnionSet UDeltas = TcRed->deltas();
  isl::UnionSet Universe = isl::UnionSet::universe(UDeltas);
  isl::UnionSet Zero = isl::UnionSet::empty(Universe.getSpace());

  /// @brief Fix all dimensions of @p Zero to 0 and add it to @p user
  Universe.foreachSet([](isl_set *zero, void *user) -> int {
                        isl::Set Zero_ = isl::Set(zero);
                        isl::UnionSet &User = *(isl::UnionSet *)user;
                        unsigned ndim = Zero_.dim(isl::DTSet);
                        for (unsigned i = 0; i < ndim; i++)
                          Zero_ = Zero_.fixSi(isl::DTSet, i, 0);
                        User = User.addSet(Zero_);
                        return 0;
                      },
                      &Zero);
  isl::UnionMap NonPositive = UDeltas.lexLeUnionSet(Zero);
  *TcRed = TcRed->subtract(NonPositive);
  *TcRed = TcRed->union_(TcRed->reverse());
  *TcRed = TcRed->coalesce();

  *Raw = Raw->union_(Raw->applyRange(*TcRed).union_(TcRed->applyRange(*Raw)));
  *Waw = Waw->union_(Waw->applyRange(*TcRed).union_(TcRed->applyRange(*Waw)));
  *War = War->union_(War->applyRange(*TcRed).union_(TcRed->applyRange(*War)));
}

void Dependences::calculateDependences(Scop &S) {
  const isl::Space Space = isl::Space(S.getParamSpace());

  isl::UnionMap Read = isl::UnionMap::empty(Space);
  isl::UnionMap Write = isl::UnionMap::empty(Space);
  isl::UnionMap MayWrite = isl::UnionMap::empty(Space);
  isl::UnionMap AccessSchedule = isl::UnionMap::empty(Space);
  isl::UnionMap StmtSchedule = isl::UnionMap::empty(Space);

  DEBUG(dbgs() << "Scop: \n" << S << "\n");

  collectInfo(S, Read, Write, MayWrite, AccessSchedule, StmtSchedule);

  isl::UnionMap Schedule = AccessSchedule.union_(StmtSchedule);

  Read = Read.coalesce();
  Write = Write.coalesce();
  MayWrite = MayWrite.coalesce();

  long MaxOpsOld = isl_ctx_get_max_operations(S.getIslCtx());
  isl_ctx_set_max_operations(S.getIslCtx(), OptComputeOut);
  isl_options_set_on_error(S.getIslCtx(), ISL_ON_ERROR_CONTINUE);

  DEBUG(dbgs() << "Read: " << Read.toStr(isl::FIsl) << "\n";
        dbgs() << "Write: " << Write.toStr(isl::FIsl) << "\n";
        dbgs() << "MayWrite: " << MayWrite.toStr(isl::FIsl) << "\n";
        dbgs() << "Schedule: " << Schedule.toStr(isl::FIsl) << "\n");

  if (OptAnalysisType == VALUE_BASED_ANALYSIS) {
    Read.computeFlow(Write, MayWrite, Schedule, &Raw, nullptr, nullptr,
                     nullptr);
    Write.computeFlow(Write, Read, Schedule, &Waw, &War, nullptr, nullptr);
  } else {
    isl::UnionMap Empty = isl::UnionMap::empty(Write.getSpace());
    Write = Write.union_(MayWrite);

    Read.computeFlow(Empty, Write, Schedule, nullptr, &Raw, nullptr, nullptr);
    Write.computeFlow(Empty, Read, Schedule, nullptr, &War, nullptr, nullptr);
    Write.computeFlow(Empty, Write, Schedule, nullptr, &Waw, nullptr, nullptr);
  }

  map_inplace(&UnionMap::coalesce, { *Raw, *Waw, *War });

  if (isl_ctx_last_error(S.getIslCtx()) == isl_error_quota) {
    Raw.reset(nullptr);
    Waw.reset(nullptr);
    War.reset(nullptr);
    isl_ctx_reset_error(S.getIslCtx());
  }
  isl_options_set_on_error(S.getIslCtx(), ISL_ON_ERROR_ABORT);
  isl_ctx_reset_operations(S.getIslCtx());
  isl_ctx_set_max_operations(S.getIslCtx(), MaxOpsOld);

  isl::UnionMap StmtRaw = Raw->intersectDomain(StmtSchedule.domain());
  isl::UnionMap StmtWaw = Waw->intersectDomain(StmtSchedule.domain());
  isl::UnionMap StmtWar = War->intersectDomain(StmtSchedule.domain());

  DEBUG({
    dbgs() << "Wrapped Dependences:\n";
    printScop(dbgs());
    dbgs() << "\n";
  });

  // To handle reduction dependences we proceed as follows:
  // 1) Aggregate all possible reduction dependences, namely all self
  //    dependences on reduction like statements.
  // 2) Intersect them with the actual RAW & WAW dependences to the get the
  //    actual reduction dependences. This will ensure the load/store memory
  //    addresses were __identical__ in the two iterations of the statement.
  // 3) Relax the original RAW and WAW dependences by substracting the actual
  //    reduction dependences. Binary reductions (sum += A[i]) cause both, and
  //    the same, RAW and WAW dependences.
  // 4) Add the privatization dependences which are widened versions of
  //    already present dependences. They model the effect of manual
  //    privatization at the outermost possible place (namely after the last
  //    write and before the first access to a reduction location).

  // Step 1)
  Red.reset(new isl::UnionMap(isl::UnionMap::empty(Raw->getSpace())));
  // FIXME(isl++) Below, an assertion is checked for equality, but
  // we might run in the case where TcRed was never set:
  //  Red->isEmpty() == true -> TcRed will be empty.
  // I assume it was relying on the isl to return false here.
  TcRed.reset(new isl::UnionMap(isl::UnionMap::empty(Raw->getSpace())));

  for (ScopStmt *Stmt : S) {
    for (MemoryAccess *MA : *Stmt) {
      if (!MA->isReductionLike())
        continue;
      isl::Set AccDomW = isl::Map(MA->getAccessRelation()).wrap();
      isl::Map Identity = isl::Map::fromDomainAndRange(AccDomW, AccDomW);
      *Red = Red->addMap(Identity);
    }
  }

  // Step 2)
  *Red = Red->intersect(*Raw);
  *Red = Red->intersect(*Waw);

  if (!Red->isEmpty()) {
    // Step 3)
    *Raw = Raw->subtract(*Red);
    *Waw = Waw->subtract(*Red);

    // Step 4)
    addPrivatizationDependences();
  }

  DEBUG({
    dbgs() << "Final Wrapped Dependences:\n";
    printScop(dbgs());
    dbgs() << "\n";
  });

  // RED_SIN is used to collect all reduction dependences again after we
  // split them according to the causing memory accesses. The current assumption
  // is that our method of splitting will not have any leftovers. In the end
  // we validate this assumption until we have more confidence in this method.
  isl::UnionMap RedSin = isl::UnionMap::empty(Raw->getSpace());

  // For each reduction like memory access, check if there are reduction
  // dependences with the access relation of the memory access as a domain
  // (wrapped space!). If so these dependences are caused by this memory access.
  // We then move this portion of reduction dependences back to the statement ->
  // statement space and add a mapping from the memory access to these
  // dependences.
  for (ScopStmt *Stmt : S) {
    for (MemoryAccess *MA : *Stmt) {
      if (!MA->isReductionLike())
        continue;

      isl::Set AccDomW = isl::Map(MA->getAccessRelation()).wrap();
      isl::UnionMap AccRedDepU =
          TcRed->intersectDomain(isl::UnionSet::fromSet(std::move(AccDomW)));
      if (AccRedDepU.isEmpty())
        continue;

      isl::Map AccRedDep = isl::Map::fromUnionMap(std::move(AccRedDepU));
      RedSin = RedSin.addMap(AccRedDep);
      AccRedDep = AccRedDep.zip();
      AccRedDep = AccRedDep.domain().unwrap();
      setReductionDependences(MA, std::move(AccRedDep));
    }
  }

  assert(RedSin.isEqual(*TcRed) &&
         "Intersecting the reduction dependence domain with the wrapped access "
         "relation is not enough, we need to loosen the access relation also");

  map_inplace(&UnionMap::zip, {*Raw, *Waw, *War, *Red, *TcRed});

  DEBUG({
    dbgs() << "Zipped Dependences:\n";
    printScop(dbgs());
    dbgs() << "\n";
  });

  *Raw = Raw->domain().unwrap();
  *Waw = Waw->domain().unwrap();
  *War = War->domain().unwrap();
  *Red = Red->domain().unwrap();
  *TcRed = TcRed->domain().unwrap();

  DEBUG({
    dbgs() << "Unwrapped Dependences:\n";
    printScop(dbgs());
    dbgs() << "\n";
  });

  *Raw = Raw->union_(StmtRaw);
  *Waw = Waw->union_(StmtWaw);
  *War = War->union_(StmtWar);

  map_inplace(&UnionMap::coalesce, { *Raw, *Waw, *War, *Red, *TcRed});

  DEBUG(printScop(dbgs()));
}

void Dependences::recomputeDependences() {
  releaseMemory();
  calculateDependences(*S);
}

bool Dependences::runOnScop(Scop &ScopVar) {
  S = &ScopVar;
  recomputeDependences();
  return false;
}

bool Dependences::isValidScattering(StatementToIslMapTy *NewScattering) {
  Scop &S = getCurScop();

  if (LegalityCheckDisabled)
    return true;

  isl::UnionMap Dependences =
      isl::UnionMap(getDependences(TYPE_RAW | TYPE_WAW | TYPE_WAR));
  isl::Space Space = isl::Space(S.getParamSpace());
  isl::UnionMap Scattering = isl::UnionMap::empty(Space);

  std::unique_ptr<isl::Space> ScatteringSpace(nullptr);

  for (ScopStmt *Stmt : S) {
    isl::Map StmtScat = isl::Map(nullptr);

    if (NewScattering->find(Stmt) == NewScattering->end())
      StmtScat = isl::Map(Stmt->getScattering());
    else
      StmtScat = isl::Map(isl_map_copy((*NewScattering)[Stmt]));

    if (!ScatteringSpace)
      ScatteringSpace.reset(new isl::Space(StmtScat.getSpace().range()));

    Scattering = Scattering.addMap(StmtScat);
  }

  Dependences = Dependences.applyDomain(Scattering);
  Dependences = Dependences.applyRange(Scattering);

  isl::Set Zero = isl::Set::universe(*ScatteringSpace);
  for (unsigned i = 0; i < Zero.dim(DTSet); i++)
    Zero = Zero.fixSi(DTSet, i, 0);

  isl::UnionSet UDeltas = Dependences.deltas();
  isl::Set Deltas = UDeltas.extractSet(*ScatteringSpace);

  isl::Map NonPositive = Deltas.lexLeSet(Zero);

  return NonPositive.isEmpty();
}

// Check if the current scheduling dimension is parallel.
//
// We check for parallelism by verifying that the loop does not carry any
// dependences.
//
// Parallelism test: if the distance is zero in all outer dimensions, then it
// has to be zero in the current dimension as well.
//
// Implementation: first, translate dependences into time space, then force
// outer dimensions to be equal. If the distance is zero in the current
// dimension, then the loop is parallel. The distance is zero in the current
// dimension if it is a subset of a map with equal values for the current
// dimension.
bool Dependences::isParallel(isl_union_map *Schedule, isl_union_map *Deps,
                             isl_pw_aff **MinDistancePtr) {
  isl::Set Deltas = isl::Set(nullptr);
  isl::Set Distance = isl::Set(nullptr);
  isl::Map ScheduleDeps = isl::Map(nullptr);

  unsigned Dimension;
  bool IsParallel;

  // FIXME(isl++)
  // Usually this would be very easy, but atm I don't want to bleed
  // out to all classes of Polly yet, so we have to do a little bit of extra
  // work in here, namely: Give the ownership back to the output parameters.

  // Pretend to take ownership. It has to be released before every return
  // in this method.
  isl::UnionMap Deps_ = isl::UnionMap(Deps);
  isl::UnionMap Schedule_ = isl::UnionMap(Schedule);

  Deps_ = Deps_.applyRange(Schedule_);
  Deps_ = Deps_.applyDomain(Schedule_);

  if (Deps_.isEmpty()) {
    Deps = Deps_.Give();
    Schedule = Schedule_.Give();
    return true;
  }

  ScheduleDeps = isl::Map::fromUnionMap(Deps_);
  Dimension = ScheduleDeps.dim(DTOut) - 1;

  for (unsigned i = 0; i < Dimension; i++)
    ScheduleDeps = ScheduleDeps.equate(DTOut, i, DTIn, i);

  Deltas = ScheduleDeps.deltas();
  Distance = isl::Set::universe(Deltas.getSpace());

  // [0, ..., 0, +] - All zeros and last dimension larger than zero
  for (unsigned i = 0; i < Dimension; i++)
    Distance = Distance.fixSi(DTSet, i, 0);

  Distance = Distance.lowerBoundSi(DTSet, Dimension, 1);
  Distance = Distance.intersect(Deltas);

  IsParallel = Distance.isEmpty();
  if (IsParallel || !MinDistancePtr) {
    Deps = Deps_.Give();
    Schedule = Schedule_.Give();
    return IsParallel;
  }

  Distance = Distance.projectOut(DTSet, 0, Dimension);
  Distance = Distance.coalesce();

  // This last step will compute a expression for the minimal value in the
  // distance polyhedron Distance with regards to the first (outer most)
  // dimension.
  *MinDistancePtr = Distance.dimMin(0).coalesce().Give();

  Deps = Deps_.Give();
  Schedule = Schedule_.Give();
  return false;
}

static void printDependencyMap(raw_ostream &OS, __isl_keep isl_union_map *DM) {
  if (DM)
    OS << DM << "\n";
  else
    OS << "n/a\n";
}

void Dependences::printScop(raw_ostream &OS) const {
  OS << "\tRAW dependences:\n\t\t";
  printDependencyMap(OS, Raw->Get());
  OS << "\tWAR dependences:\n\t\t";
  printDependencyMap(OS, War->Get());
  OS << "\tWAW dependences:\n\t\t";
  printDependencyMap(OS, Waw->Get());
  OS << "\tReduction dependences:\n\t\t";
  printDependencyMap(OS, Red->Get());
  OS << "\tTransitive closure of reduction dependences:\n\t\t";
  printDependencyMap(OS, TcRed->Get());
}

void Dependences::releaseMemory() {
  Raw.reset(nullptr);
  War.reset(nullptr);
  Waw.reset(nullptr);
  Red.reset(nullptr);
  TcRed.reset(nullptr);

  for (auto &ReductionDeps : ReductionDependences)
    isl_map_free(ReductionDeps.second);
  ReductionDependences.clear();
}

isl_union_map *Dependences::getDependences(int Kinds) {
  assert(hasValidDependences() && "No valid dependences available");
  isl::Space Space = Raw->getSpace();
  isl::UnionMap Deps = isl::UnionMap::empty(Space);

  if (Kinds & TYPE_RAW)
    Deps = Deps.union_(*Raw);

  if (Kinds & TYPE_WAR)
    Deps = Deps.union_(*War);

  if (Kinds & TYPE_WAW)
    Deps = Deps.union_(*Waw);

  if (Kinds & TYPE_RED)
    Deps = Deps.union_(*Red);

  if (Kinds & TYPE_TC_RED)
    Deps = Deps.union_(*TcRed);

  Deps = Deps.coalesce();
  Deps = Deps.detectEqualities();
  return Deps.Give();
}

bool Dependences::hasValidDependences() {
  return (Raw != nullptr) && (War != nullptr) && (Waw != nullptr);
}

isl_map *Dependences::getReductionDependences(MemoryAccess *MA) {
  return isl_map_copy(ReductionDependences[MA]);
}

void Dependences::setReductionDependences(MemoryAccess *MA, isl::Map &&D) {
  assert(ReductionDependences.count(MA) == 0 &&
         "Reduction dependences set twice!");
  ReductionDependences[MA] = D.GetCopy();
}

void Dependences::getAnalysisUsage(AnalysisUsage &AU) const {
  ScopPass::getAnalysisUsage(AU);
}

char Dependences::ID = 0;

Pass *polly::createDependencesPass() { return new Dependences(); }

INITIALIZE_PASS_BEGIN(Dependences, "polly-dependences",
                      "Polly - Calculate dependences", false, false);
INITIALIZE_PASS_DEPENDENCY(ScopInfo);
INITIALIZE_PASS_END(Dependences, "polly-dependences",
                    "Polly - Calculate dependences", false, false)
