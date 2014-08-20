if (CUDALIB_FOUND)
  add_subdirectory(GPURuntime)
endif (CUDALIB_FOUND)

option(POLLY_BUILD_POLLI "Build PolyJIT's JIT engine polli" ON)
if (POLLY_BUILD_POLLI)
  add_subdirectory(polli)
endif (POLLY_BUILD_POLLI)

set(LLVM_COMMON_DEPENDS ${LLVM_COMMON_DEPENDS} PARENT_SCOPE)
