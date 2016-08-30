#!/bin/sh

LIBS=$(pwd)/lib

mlton -mlb-path-var "LIBS $LIBS" -output example.out example.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-unparser.out abt-unparser.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-parser.out abt-parser.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-unparser.out abt-unparser.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-patterns.out abt-patterns.mlb
# mlton -mlb-path-map mlb-path-map -output abt-lcs.out abt-lcs.mlb
