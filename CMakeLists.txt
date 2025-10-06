cmake_minimum_required(VERSION 3.28)
project(prof_to_wasm)

set(CMAKE_CXX_STANDARD 20)

add_subdirectory(third_party/wabt)
find_package(LLVM REQUIRED)
message(STATUS "Using LLVM version ${LLVM_VERSION} from ${LLVM_BINARY_DIR}")

add_executable(prof_to_wasm main.cpp)
target_compile_options(prof_to_wasm PUBLIC -fno-rtti)
target_link_libraries(prof_to_wasm
        wabt::wabt
        LLVMCore
        LLVMObject
        LLVMProfileData
        LLVMSupport
)
target_include_directories(prof_to_wasm PRIVATE ${LLVM_INCLUDE_DIRS})
