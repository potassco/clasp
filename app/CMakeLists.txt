set(files
	clasp_app.cpp
	clasp_app.h
	main.cpp)
add_executable(clasp_bin ${files})
target_link_libraries(clasp_bin clasp)
set_property(TARGET clasp_bin PROPERTY FOLDER exe)
set_target_properties(clasp_bin PROPERTIES OUTPUT_NAME clasp)
