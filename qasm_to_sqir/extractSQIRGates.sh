#!/bin/bash

coqc -R .. Top SqireExtraction.v && rm -f .SqireExtraction.aux SqireExtraction.{glob,vo} SqireGates.mli && mv SqireGates.ml lib
