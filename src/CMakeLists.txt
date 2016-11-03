set(header_path ${CLASP_SOURCE_DIR}/clasp)

# generate config.h
set(CLASP_HAS_THREADS ${CLASP_BUILD_WITH_THREADS})
if (NOT DEFINED CLASP_USE_STD_VECTOR)
	if (MSVC)
		set(CLASP_USE_STD_VECTOR "_DEBUG")
	else()
		set(CLASP_USE_STD_VECTOR 0)
	endif()
endif()
if (NOT DEFINED CLASP_HAS_STATIC_ASSERT)
	if (CLASP_BUILD_WITH_THREADS OR (DEFINED CMAKE_CXX_STANDARD AND NOT CMAKE_CXX_STANDARD LESS 11))
		set(CLASP_HAS_STATIC_ASSERT ON)
	elseif(MSVC AND NOT MSVC_VERSION LESS 1600)
		set(CLASP_HAS_STATIC_ASSERT ON)
	endif()
endif()
configure_file(${header_path}/config.h.in ${CLASP_BINARY_DIR}/clasp/config.h @ONLY)

set(header_temp
	${CLASP_BINARY_DIR}/clasp/config.h
	${header_path}/heuristics.h
	${header_path}/statistics.h
	${header_path}/claspfwd.h
	${header_path}/logic_program.h
	${header_path}/pod_vector.h
	${header_path}/weight_constraint.h
	${header_path}/asp_preprocessor.h
	${header_path}/enumerator.h
	${header_path}/clingo.h
	${header_path}/lookahead.h
	${header_path}/shared_context.h
	${header_path}/solver_strategies.h
	${header_path}/solve_algorithms.h
	${header_path}/literal.h
	${header_path}/satelite.h
	${header_path}/program_builder.h
	${header_path}/dependency_graph.h
	${header_path}/clause.h
	${header_path}/cb_enumerator.h
	${header_path}/minimize_constraint.h
	${header_path}/unfounded_check.h
	${header_path}/solver_types.h
	${header_path}/solver.h
	${header_path}/parser.h
	${header_path}/clasp_facade.h
	${header_path}/model_enumerators.h
	${header_path}/logic_program_types.h
	${header_path}/constraint.h)
LIST(APPEND header ${header_temp})
set(ide_header "Header Files")
source_group("${ide_header}" FILES ${header_temp})
set(header_temp
	${header_path}/util/misc_types.h
	${header_path}/util/multi_queue.h
	${header_path}/util/left_right_sequence.h
	${header_path}/util/pod_vector.h
	${header_path}/util/hash_map.h
	${header_path}/util/indexed_priority_queue.h
	${header_path}/util/type_manip.h
	${header_path}/util/platform.h
	${header_path}/util/timer.h)
LIST(APPEND header ${header_temp})
source_group("${ide_header}\\util" FILES ${header_temp})
set(header_temp
	${header_path}/cli/clasp_output.h
	${header_path}/cli/clasp_options.h)
LIST(APPEND header ${header_temp})
source_group("${ide_header}\\cli" FILES ${header_temp})

set(src
	asp_preprocessor.cpp
	cb_enumerator.cpp
	clasp_facade.cpp
	clasp_options.cpp
	clasp_output.cpp
	clause.cpp
	clingo.cpp
	constraint.cpp
	dependency_graph.cpp
	enumerator.cpp
	heuristics.cpp
	logic_program.cpp
	logic_program_types.cpp
	lookahead.cpp
	minimize_constraint.cpp
	model_enumerators.cpp
	parser.cpp
	program_builder.cpp
	satelite.cpp
	shared_context.cpp
	solve_algorithms.cpp
	solver.cpp
	solver_strategies.cpp
	solver_types.cpp
	statistics.cpp
	timer.cpp
	unfounded_check.cpp
	weight_constraint.cpp)
if (CLASP_BUILD_WITH_THREADS)
LIST(APPEND src
	parallel_solve.cpp)
set(header_temp
	${header_path}/mt/thread.h
	${header_path}/mt/mutex.h
	${header_path}/mt/parallel_solve.h)
LIST(APPEND header ${header_temp})
source_group("${ide_header}\\mt" FILES ${header_temp})
endif()

add_library(libclasp ${header} ${src})
if (CLASP_BUILD_WITH_THREADS)
	target_link_libraries(libclasp PUBLIC Threads::Threads)
endif()
if(MSVC)
	target_compile_definitions(libclasp PRIVATE _SCL_SECURE_NO_WARNINGS)
endif()
target_include_directories(libclasp PUBLIC
	$<BUILD_INTERFACE:${CLASP_SOURCE_DIR}>
	$<BUILD_INTERFACE:${CLASP_BINARY_DIR}>
	$<INSTALL_INTERFACE:${clasp_include_dest}>)
target_link_libraries(libclasp PUBLIC libpotassco)
set_target_properties(libclasp PROPERTIES
	OUTPUT_NAME clasp
	FOLDER lib)

# installation
install(TARGETS libclasp EXPORT clasp DESTINATION "${clasp_lib_dest}")
install(FILES ${header}               DESTINATION "${clasp_include_dest}/clasp")
