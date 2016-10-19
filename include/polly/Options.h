//===--------------- polly/Options.h - The Polly option category *- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Introduce an option category for Polly.
//
//===----------------------------------------------------------------------===//

#ifndef POLLY_OPTIONS_H
#define POLLY_OPTIONS_H

#include "llvm/Support/CommandLine.h"

extern llvm::cl::OptionCategory PollyCategory;

namespace polly {
namespace opt {
  // IslAst.cpp
  extern bool PollyParallel;
  extern bool PollyParallelForce;
  extern bool UseContext;
  extern bool DetectParallel;

  // ScheduleOptimizer.cpp
  extern std::string OptimizeDeps;
  extern std::string SimplifyDeps;
  extern int MaxConstantTerm;
  extern int MaxCoefficient;
  extern std::string FusionStrategy;
  extern std::string MaximizeBandDepth;
  extern std::string OuterCoincidence;
  extern int PrevectorWidth;
  extern bool FirstLevelTiling;
  extern bool SecondLevelTiling;
  extern bool RegisterTiling;

  // ScopDetection.cpp
  extern bool PollyInvariantLoadHoisting;
}
}
#endif
