#!/bin/bash

coqc -R .. Top Extraction.v
rm -f .Extraction.aux Extraction.glob Extraction.vo ExtractedCode.mli
