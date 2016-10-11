enable_testing()
file(GLOB src    *.cpp)
file(GLOB header *.h)
add_executable(test_clasp ${header} ${src})
target_include_directories(test_clasp PRIVATE ${CPPUNIT_INCLUDE_DIRS})
target_link_libraries(test_clasp clasp ${CPPUNIT_LIBRARIES})
add_test(NAME testClasp COMMAND test_clasp)


	
