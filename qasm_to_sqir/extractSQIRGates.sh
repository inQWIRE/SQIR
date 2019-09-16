#!/bin/bash

coqc -R .. Top SqirExtraction.v && rm -f .SqirExtraction.aux SqirExtraction.{glob,vo} SqirGates.mli && mv SqirGates.ml lib
