#!/bin/bash

coqc -R .. Top Extraction.v && rm -f .Extraction.aux Extraction.glob Extraction.vo extracted_code.mli && mv extracted_code.ml qasm-translation/src
