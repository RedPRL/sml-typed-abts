#!/bin/sh

LIBS=$(pwd)/lib

mlton -mlb-path-var "LIBS $LIBS" -output example.out example.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-unparser.out abt-unparser.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-parser.out abt-parser.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-unparser.out abt-unparser.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-json.out abt-json.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-machine.out abt-machine.mlb
