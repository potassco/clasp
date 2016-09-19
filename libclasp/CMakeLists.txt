cmake_minimum_required(VERSION 2.8)
file(GLOB LIBCLASP_SRC src/*.cpp)
if (NOT CLASP_INCLUDE_DIRS)
	set(CLASP_INCLUDE_DIRS "${CMAKE_CURRENT_SOURCE_DIR}/../liblp" "${CMAKE_CURRENT_SOURCE_DIR}/../libprogram_opts")
endif()
if (NOT CLASP_COMPILE_DEFS)
	set (CLASP_COMPILE_DEFS "-DWITH_THREADS=0")
endif()
include_directories(${CMAKE_CURRENT_SOURCE_DIR} ${CLASP_INCLUDE_DIRS})
add_definitions(${CLASP_COMPILE_DEFS})

SET(LIBRARY_OUTPUT_PATH ${CMAKE_CURRENT_BINARY_DIR}/lib)
add_library(clasp STATIC ${LIBCLASP_SRC})

# Doc target
find_package(Doxygen)
if(DOXYGEN_FOUND)
	set(doxyfile ${CMAKE_CURRENT_SOURCE_DIR}/doc/api/clasp)
	add_custom_target(doc
		COMMAND ${DOXYGEN_EXECUTABLE} ${doxyfile}
		WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/doc/api 
		COMMENT "Generating clasp documentation..."
		VERBATIM)
endif()

