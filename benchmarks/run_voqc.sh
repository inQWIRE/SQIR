#!/bin/bash

declare -a PROG=("adder_8.qasm" "barenco_tof_10.qasm" "barenco_tof_3.qasm" "barenco_tof_4.qasm" "barenco_tof_5.qasm" "csla_mux_3.qasm" "csum_mux_9.qasm" "gf2^10_mult.qasm" "gf2^16_mult.qasm" "gf2^32_mult.qasm" "gf2^4_mult.qasm" "gf2^5_mult.qasm" "gf2^6_mult.qasm" "gf2^7_mult.qasm" "gf2^8_mult.qasm" "gf2^9_mult.qasm" "mod5_4.qasm" "mod_mult_55.qasm" "mod_red_21.qasm" "qcla_adder_10.qasm" "qcla_com_7.qasm" "qcla_mod_7.qasm" "rc_adder_6.qasm" "tof_10.qasm" "tof_3.qasm" "tof_4.qasm" "tof_5.qasm" "vbe_adder_3.qasm")

declare -a N=("24" "19" "5" "7" "9" "15" "30" "30" "48" "96" "12" "15" "18" "21" "24" "27" "5" "9" "11" "36" "24" "26" "14" "19" "5" "7" "9" "10")

len=$((${#PROG[@]}-1))

cd ../VOQC

for i in `seq 0 ${len}`
do
    outfile="../benchmarks/nam-benchmarks/${PROG[$i]}_opt"
    dune exec ./voqc.exe ../benchmarks/nam-benchmarks/${PROG[$i]} ${N[$i]} $outfile
done
