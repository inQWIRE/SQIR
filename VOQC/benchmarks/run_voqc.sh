#!/bin/bash

RED='\033[0;31m'
BLUE='\033[0;34m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
YELLOW='\033[1;33m'
NOCOLOR='\033[0m'

# Get files
pf_filenames=( $(ls -d PF/*.qasm) )
Arithmetic_and_Toffoli_filenames=( $(ls -d Arithmetic_and_Toffoli/*.qasm) )
QFT_and_Adders_filenames=( $(ls -d QFT_and_Adders/*.qasm) )

> benchmark_results.csv
echo "name,Orig. total,Orig. Rz,Orig. T,Orig. H,Orig. X,Orig. CNOT,VOQC total,VOQC Rz,VOQC T,VOQC H,VOQC X,VOQC CNOT,time" >> benchmark_results.csv



printf "${GREEN}##### Running on files in Arithmetic_and_Toffoli #####${NOCOLOR}\n"
for filename in "${Arithmetic_and_Toffoli_filenames[@]}"
do
    program_name=`basename "$filename" .qasm`
    currentTime=`date`
    printf "${CYAN}   + [${currentTime}] Running on ${filename}${NOCOLOR}\n"
    (time dune exec ./voqc.exe ${filename} out.qasm --root ../extraction) &> ${program_name}.txt
    python parseOutput.py ${program_name}.txt >> benchmark_results.csv
    rm -rf ${program_name}.txt
done

# echo""
# printf "${GREEN}##### Running on files in PF #####${NOCOLOR}\n"
# for filename in "${pf_filenames[@]}"
# do
#     program_name=`basename "$filename" .qasm`
#     currentTime=`date`
#     printf "${CYAN}   + [${currentTime}] Running on ${filename}${NOCOLOR}\n"
#     (time dune exec ./voqc.exe ${filename} out.qasm --root ../extraction) &> ${program_name}.txt
#     python parseOutput.py ${program_name}.txt >> benchmark_results.csv
#     rm -rf ${program_name}.txt
# done
# 
# echo""
# printf "${GREEN}##### Running on files in QFT_and_Adders #####${NOCOLOR}\n"
# for filename in "${QFT_and_Adders_filenames[@]}"
# do
#     program_name=`basename "$filename" .qasm`
#     currentTime=`date`
#     printf "${CYAN}   + [${currentTime}] Running on ${filename}${NOCOLOR}\n"
#     (time dune exec ./voqc.exe ${filename} out.qasm --root ../extraction) &> ${program_name}.txt
#     python parseOutput.py ${program_name}.txt >> benchmark_results.csv
#     rm -rf ${program_name}.txt
# done
