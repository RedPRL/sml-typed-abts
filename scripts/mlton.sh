#!/bin/sh

LIBS=$(pwd)/lib

mlyacc example/example.grm
mllex example/example.lex

mlton -mlb-path-var "LIBS $LIBS" -output example.out example.mlb
mlton -mlb-path-var "LIBS $LIBS" -output abt-unify.out abt-unify.mlb
