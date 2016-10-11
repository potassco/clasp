set(header_path      ${LIB_POTASSCO_SOURCE_DIR}/potassco)
set(opts_header_path ${header_path}/program_opts)

set(detail_header
	${opts_header_path}/detail/notifier.h
	${opts_header_path}/detail/refcountable.h
	${opts_header_path}/detail/value_store.h)
set(opts_header
	${opts_header_path}/errors.h
	${opts_header_path}/mapped_value.h
	${opts_header_path}/program_options.h
	${opts_header_path}/typed_value.h
	${opts_header_path}/value.h
	${opts_header_path}/value_store.h)
set(header
	${header_path}/application.h
	${header_path}/aspif.h
	${header_path}/aspif_text.h
	${header_path}/basic_types.h
	${header_path}/clingo.h
	${header_path}/convert.h
	${header_path}/match_basic_types.h
	${header_path}/rule_utils.h
	${header_path}/smodels.h
	${header_path}/string_convert.h
	${header_path}/theory_data.h)
set(ide_header_group "Header Files")
source_group("${ide_header_group}" FILES ${header})
source_group("${ide_header_group}\\program_opts" FILES ${opts_header})
source_group("${ide_header_group}\\program_opts\\detail" FILES ${detail_header})
set(src
	application.cpp
	aspif.cpp
	aspif_text.cpp
	clingo.cpp
	convert.cpp
	match_basic_types.cpp
	program_options.cpp
	rule_utils.cpp
	smodels.cpp
	string_convert.cpp
	theory_data.cpp
	value_store.cpp)

add_library(potassco ${detail_header} ${opts_header} ${header} ${src})
if(MSVC)
target_compile_definitions(potassco PRIVATE _SCL_SECURE_NO_WARNINGS)
endif()
target_include_directories(potassco PUBLIC
	$<BUILD_INTERFACE:${LIB_POTASSCO_SOURCE_DIR}>
	$<INSTALL_INTERFACE:${include_dest}>)

# installation
install(TARGETS potassco EXPORT potassco DESTINATION "${lib_dest}")
install(FILES ${header}         DESTINATION "${include_dest}/potassco")
install(FILES ${opts_header}    DESTINATION "${include_dest}/potassco/program_opts")
install(FILES ${detail_header}  DESTINATION "${include_dest}/potassco/program_opts/detail")
