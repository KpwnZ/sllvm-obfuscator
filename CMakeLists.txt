
set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -g -O0")

add_llvm_component_library(LLVMSLLVM_OBF
  BogusControlFlow.cpp
  InstructionObf.cpp
  StringObf.cpp
  IndirectCall.cpp
  IndirectBranch.cpp
  Flatten.cpp
  
  DEPENDS
  intrinsics_gen
)
