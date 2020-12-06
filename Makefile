all: sat sat_opt sudoku

sat: sat.cpp
	clang++ -Wall -Wextra -g -O0 -std=c++17 -o $@ $^

sat_opt: sat.cpp
	clang++ -Wall -Wextra -DNDEBUG -O2 -std=c++17 -o sat_opt sat.cpp

sudoku: sudoku.cpp
	clang++ -std=c++17 -o sudoku sudoku.cpp

.PHONY: all

