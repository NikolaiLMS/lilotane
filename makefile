CC=g++

# Options: minisat220 lingeling glucose4
IPASIRSOLVER=glucose4
SOLVERLIB=lib/${IPASIRSOLVER}/libipasir${IPASIRSOLVER}.a

CWARN=-Wno-unused-parameter -Wno-sign-compare -Wno-format -Wno-format-security
CERROR=

COMPILEFLAGS=-O3 -g -pipe -Wall -Wextra -pedantic -std=c++17 $(CWARN) $(CERROR)
LINKERFLAG=-O3 -lm -Llib/${IPASIRSOLVER} -lipasir${IPASIRSOLVER}

#COMPILEFLAGS=-O0 -ggdb -pipe -Wall -Wextra -pedantic -std=c++17 $(CWARN) $(CERROR)
#LINKERFLAG=-O0 -ggdb
INCLUDES=-Isrc -Isrc/parser

.PHONY = parser clean

treerexx: ${SOLVERLIB} $(patsubst %.cpp,%.o,$(wildcard src/parser/*.cpp src/data/*.cpp src/planner/*.cpp src/sat/*.cpp src/util/*.cpp)) src/main.o 
	${CC} $^ -o treerexx ${LINKERFLAG}

src/parser/%.o: src/parser/%.cpp src/parser/%.hpp
	cd src/parser && make
	
src/main.o: src/main.cpp
	${CC} ${COMPILEFLAGS} ${INCLUDES} -o $@ -c $<
	
%.o: %.cpp %.h
	${CC} ${COMPILEFLAGS} ${INCLUDES} -o $@ -c $<

${SOLVERLIB}:
	cd lib/${IPASIRSOLVER} && bash fetch_and_build.sh

clean:
#	[ ! -e libpandaPIparser.a ] || rm libpandaPIparser.a
	[ ! -e treerexx ] || rm treerexx
	rm $(wildcard src/*.o src/*/*.o)

cleantr:
	[ ! -e treerexx ] || rm treerexx
	rm $(wildcard src/*.o src/data/*.o src/planner/*.o src/sat/*.o src/util/*.o)
