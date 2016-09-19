file(GLOB LIBOPTS_SRC src/*.cpp)
include_directories(${CMAKE_CURRENT_SOURCE_DIR})
SET(LIBRARY_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/lib)
add_library(program_opts STATIC ${LIBOPTS_SRC})
