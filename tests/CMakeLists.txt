add_executable(test_clasp lpcompare.h)
target_sources(test_clasp PRIVATE
    clause_creator_test.cpp
    clause_test.cpp
    cli_test.cpp
    decision_heuristic_test.cpp
    dependency_graph_test.cpp
    dlp_builder_test.cpp
    enumerator_test.cpp
    facade_test.cpp
    literal_test.cpp
    minimize_test.cpp
    parser_test.cpp
    program_builder_test.cpp
    rule_test.cpp
    satelite_test.cpp
    solver_test.cpp
    unfounded_check_test.cpp
    weight_constraint_test.cpp
)

target_link_libraries(test_clasp PRIVATE libclasp Catch2::Catch2WithMain potassco_default_warnings)
target_include_directories(test_clasp PRIVATE $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>)
set_target_properties(test_clasp PROPERTIES FOLDER test)

catch_discover_tests(test_clasp PROPERTIES TIMEOUT 30)
