#!/bin/bash

declare -a PROG=("adder_8.qasm" "barenco_tof_3.qasm" "barenco_tof_4.qasm" "barenco_tof_5.qasm" "barenco_tof_10.qasm" "csla_mux_3.qasm" "csum_mux_9.qasm" "gf2^4_mult.qasm" "gf2^5_mult.qasm" "gf2^6_mult.qasm" "gf2^7_mult.qasm" "gf2^8_mult.qasm" "gf2^9_mult.qasm" "gf2^10_mult.qasm" "gf2^16_mult.qasm" "gf2^32_mult.qasm" "mod5_4.qasm" "mod_adder_1024.qasm" "mod_mult_55.qasm" "mod_red_21.qasm" "qcla_adder_10.qasm" "qcla_com_7.qasm" "qcla_mod_7.qasm" "rc_adder_6.qasm" "tof_3.qasm" "tof_4.qasm" "tof_5.qasm" "tof_10.qasm" "vbe_adder_3.qasm")

len=$((${#PROG[@]}-1))

for i in `seq 0 ${len}`
do
    outfile="../benchmarks/Arithmetic_and_Toffoli/${PROG[$i]}_opt"
    dune exec ./voqc.exe Arithmetic_and_Toffoli/${PROG[$i]} $outfile --root ../extraction
done
