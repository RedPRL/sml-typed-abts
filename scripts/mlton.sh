#!/bin/sh

mlton -mlb-path-map mlb-path-map -output example.out example.mlb
mlton -mlb-path-map mlb-path-map -output abt-unparser.out abt-unparser.mlb
