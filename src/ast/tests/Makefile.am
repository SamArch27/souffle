# Souffle - A Datalog Compiler
# Copyright (c) 2020, The Souffle Developers. All rights reserved.
# Licensed under the Universal Permissive License v 1.0 as shown at:
# - https://opensource.org/licenses/UPL
# - <souffle root>/licenses/SOUFFLE-UPL.txt


SUFFIXES = .cpp .h

CXXFLAGS += -I${top_srcdir}/src -I$(top_srcdir)/src/include

########## Unit Tests

AM_COLOR_TESTS=always

# -------------------------

# init check programs
check_PROGRAMS =

# test description
# check_PROGRAMS += testname
# test_testname_SOURCES = cppfile test.h
# if needed
# test_testname_LDADD = $(top_builddir)/src/libsouffle.la
# test_testname_CXXFLAGS = test-specific flags

# ast print test
check_PROGRAMS += ast_print_test
ast_print_test_SOURCES = ast_print_test.cpp
ast_print_test_LDADD = $(top_builddir)/src/libsouffle.la

# ast program test
check_PROGRAMS += ast_program_test
ast_program_test_SOURCES = ast_program_test.cpp
ast_program_test_LDADD = $(top_builddir)/src/libsouffle.la

# ast transformers test
check_PROGRAMS += ast_transformers_test
ast_transformers_test_SOURCES = ast_transformers_test.cpp
ast_transformers_test_LDADD = $(top_builddir)/src/libsouffle.la

# ast utils test
check_PROGRAMS += ast_utils_test
ast_utils_test_SOURCES = ast_utils_test.cpp
ast_utils_test_LDADD = $(top_builddir)/src/libsouffle.la

# ast parser utils test
check_PROGRAMS += ast_parser_utils_test
ast_parser_utils_test_SOURCES = ast_parser_utils_test.cpp
ast_parser_utils_test_LDADD = $(top_builddir)/src/libsouffle.la

# type system test
check_PROGRAMS += type_system_test
type_system_test_SOURCES = type_system_test.cpp
type_system_test_LDADD = $(top_builddir)/src/libsouffle.la

# constraints test
check_PROGRAMS += constraints_test
constraints_test_SOURCES = constraints_test.cpp
constraints_test_LDADD = $(top_builddir)/src/libsouffle.la

# make all check-programs tests
TESTS = $(check_PROGRAMS)
