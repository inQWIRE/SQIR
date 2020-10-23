#!/bin/bash

RED='\033[0;31m'
BLUE='\033[0;34m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
YELLOW='\033[1;33m'
NOCOLOR='\033[0m'

# Get files
Arithmetic_and_Toffoli_filenames=( $(ls -d VOQC-benchmarks/Arithmetic_and_Toffoli_p*/*.qasm) )

currentTime=`date`
printf "${GREEN}##### [${currentTime}] Running VOQC...${NOCOLOR}\n"
> voqc_out.csv
echo "name,Orig. total,Orig. Rz,Orig. T,Orig. H,Orig. X,Orig. CNOT,VOQC total,VOQC Rz,VOQC T,VOQC H,VOQC X,VOQC CNOT,parse time,optimization time,write time" >> voqc_out.csv
for filename in "${Arithmetic_and_Toffoli_filenames[@]}"
do
    program_name=`basename "$filename" .qasm`
    (time dune exec --root .. -- ./voqc.exe -i ${filename} -o out.qasm) &> ${program_name}.txt
    python parseOutput.py ${program_name}.txt >> voqc_out.csv
    rm -rf ${program_name}.txt
    rm -rf out.qasm
done
printf "${CYAN}\tDONE${NOCOLOR}\n"

# run the other optimizers
currentTime=`date`
printf "${GREEN}##### [${currentTime}] Running Qiskit...${NOCOLOR}\n"
python run_qiskit.py VOQC-benchmarks/Arithmetic_and_Toffoli_partial qiskit_out.csv &> /dev/null
if [ -f qiskit_out.csv ]; then
    printf "${CYAN}\tDONE${NOCOLOR}\n"
else
    printf "${RED}\tFAILED - try running run_qiskit.py for more information${NOCOLOR}\n"
    exit 1
fi

currentTime=`date`
printf "${GREEN}##### [${currentTime}] Running tket...${NOCOLOR}\n"
python run_tket.py VOQC-benchmarks/Arithmetic_and_Toffoli_partial tket_out.csv &> /dev/null
if [ -f tket_out.csv ]; then
    printf "${CYAN}\tDONE${NOCOLOR}\n"
else
    printf "${RED}\tFAILED - try running run_tket.py for more information${NOCOLOR}\n"
    exit 1
fi

currentTime=`date`
printf "${GREEN}##### [${currentTime}] Running PyZX...${NOCOLOR}\n"
python run_pyzx.py VOQC-benchmarks/Arithmetic_and_Toffoli_partial pyzx_out.csv &> /dev/null
if [ -f pyzx_out.csv ]; then
    printf "${CYAN}\tDONE${NOCOLOR}\n"
else
    printf "${RED}\tFAILED - try running run_pyzx.py for more information${NOCOLOR}\n"
    exit 1
fi

# print aggregate data
python create_tables.py
