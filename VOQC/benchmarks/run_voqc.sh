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

# Number of iterations stored as an array. The order
# of these elements must match the order of the pf pf_filenames
# in the above ls command.
ITERS=(
"160000400"         # pf1_10
"1600000040000"     # pf1_100
"2560001600"        # pf1_20
"12960003600"       # pf1_30
"40960006400"       # pf1_40
"100000010000"      # pf1_50
"207360014400"      # pf1_60
"384160019600"      # pf1_70
"655360025600"      # pf1_80
"1049760032400"     # pf1_90
"413519"            # pf2_10
"413158222"         # pf2_100
"3306546"           # pf2_20
"11157792"          # pf2_30
"26445966"          # pf2_40
"51649777"          # pf2_50
"89247936"          # pf2_60
"141719150"         # pf2_70
"211542129"         # pf2_80
"301195584"         # pf2_90
"136920"            # pf4_10
"43082682"          # pf4_100
"772890"            # pf4_20
"2127820"           # pf4_30
"4365524"           # pf4_40
"7623316"           # pf4_50
"12021906"          # pf4_60
"17670307"          # pf4_70
"24668706"          # pf4_80
"33110322"          # pf4_90
"277691"            # pf6_10
"59445190"          # pf6_100
"1396045"           # pf6_20
"3591360"           # pf6_30
"7021880"           # pf6_40
"11812504"          # pf6_50
"18068360"          # pf6_60
"25881196"          # pf6_70
"35332981"          # pf6_80
"46498162"          # pf6_90
)

echo""
printf "${GREEN}##### Running on files in PF #####${NOCOLOR}\n"
index=0
> PF_results.csv
echo "name,Orig. total,Orig. Rz,Orig. Cliff,Orig. H,Orig. X,Orig. CNOT,VOQC total,VOQC Rz,VOQC Cliff,VOQC H,VOQC X,VOQC CNOT,parse time,optimization time,write time" >> PF_results.csv
for filename in "${pf_filenames[@]}"
do
    program_name=`basename "$filename" .qasm`
    iter=${ITERS[${index}]}
    index=$((index+1))
    currentTime=`date`
    printf "${CYAN}   + [${currentTime}] Running on ${filename}${NOCOLOR}\n"
    (time dune exec --root .. -- ./voqc.exe -i ${filename} -o out.qasm -n ${iter}) &> ${program_name}.txt
    python parseOutput2.py ${program_name}.txt >> PF_results.csv
    rm -rf ${program_name}.txt
done

printf "${GREEN}##### Running on files in Arithmetic_and_Toffoli #####${NOCOLOR}\n"
> Arithmetic_and_Toffoli_results.csv
echo "name,Orig. total,Orig. Rz,Orig. T,Orig. H,Orig. X,Orig. CNOT,VOQC total,VOQC Rz,VOQC T,VOQC H,VOQC X,VOQC CNOT,parse time,optimization time,write time" >> Arithmetic_and_Toffoli_results.csv
for filename in "${Arithmetic_and_Toffoli_filenames[@]}"
do
    program_name=`basename "$filename" .qasm`
    currentTime=`date`
    printf "${CYAN}   + [${currentTime}] Running on ${filename}${NOCOLOR}\n"
    (time dune exec --root .. -- ./voqc.exe -i ${filename} -o out.qasm) &> ${program_name}.txt
    python parseOutput.py ${program_name}.txt >> Arithmetic_and_Toffoli_results.csv
    rm -rf ${program_name}.txt
done

echo""
printf "${GREEN}##### Running on files in QFT_and_Adders #####${NOCOLOR}\n"
> QFT_and_Adders_results.csv
echo "name,Orig. total,Orig. Rz,Orig. T,Orig. H,Orig. X,Orig. CNOT,VOQC total,VOQC Rz,VOQC T,VOQC H,VOQC X,VOQC CNOT,parse time,optimization time,write time" >> QFT_and_Adders_results.csv
for filename in "${QFT_and_Adders_filenames[@]}"
do
    program_name=`basename "$filename" .qasm`
    currentTime=`date`
    printf "${CYAN}   + [${currentTime}] Running on ${filename}${NOCOLOR}\n"
    (time dune exec --root .. -- ./voqc.exe -i ${filename} -o out.qasm) &> ${program_name}.txt
    python parseOutput.py ${program_name}.txt >> QFT_and_Adders_results.csv
    rm -rf ${program_name}.txt
done
