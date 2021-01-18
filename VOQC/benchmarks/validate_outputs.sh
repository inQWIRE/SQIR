#!/bin/bash

RED='\033[0;31m'
BLUE='\033[0;34m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
YELLOW='\033[1;33m'
NOCOLOR='\033[0m'

Arithmetic_and_Toffoli_filenames=( $(ls -d VOQC-benchmarks/Arithmetic_and_Toffoli_p*/*.qasm) )

currentTime=`date`
for filename in "${Arithmetic_and_Toffoli_filenames[@]}"
do
    currentTime=`date`
    printf "${CYAN}[${currentTime}] Running VOQC on ${filename}${NOCOLOR}\n"
    (dune exec --root .. -- ./voqc.exe -i ${filename} -o out.qasm) &> /dev/null
    printf "${CYAN}  Running translation validation...${NOCOLOR}\n"
    python3 rzq_to_rz.py out.qasm
    python3 verifyEquality.py ${filename} out.qasm
    ret=$?
    if [ $ret -ne 0 ]; then
        printf "${RED}    FAILED${NOCOLOR}\n"
    else
        printf "${GREEN}    PASSED${NOCOLOR}\n"
    fi
    rm -rf out.qasm
done

