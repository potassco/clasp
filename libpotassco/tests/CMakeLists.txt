enable_testing()
set(test_lp
	test_aspif.cpp
	test_smodels.cpp
	test_text.cpp
	test_string_convert.cpp
	main.cpp
)
add_executable(potassco_test_lp ${test_lp})
target_link_libraries(potassco_test_lp potassco)
target_include_directories(potassco_test_lp  PRIVATE
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
)
set_target_properties(potassco_test_lp PROPERTIES
	CXX_STANDARD 11
	CXX_EXTENSIONS OFF
	CXX_STANDARD_REQUIRED YES
)
set(test_opts
	test_application.cpp
	test_options.cpp
	test_value.cpp
	main.cpp
)

add_executable(potassco_test_opts ${test_opts})
target_link_libraries(potassco_test_opts potassco)
target_include_directories(potassco_test_opts PRIVATE
	$<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
)

add_test(NAME test_lp COMMAND potassco_test_lp)
add_test(NAME test_opts COMMAND potassco_test_opts)
set_property(TARGET potassco_test_lp   PROPERTY FOLDER test)
set_property(TARGET potassco_test_opts PROPERTY FOLDER test)
