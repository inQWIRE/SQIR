#!/bin/sh

git submodule init
git submodule update
coq_makefile -f _CoqProject -o Makefile
