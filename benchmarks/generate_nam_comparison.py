#!/usr/bin/env python

import sys

# key = benchmark filename
# value = [original total # gates, original # CNOT gates,
#          post-optimization (L) total # gates, post-optimization (L) # CNOT gates,
#          post-optimization (H) total # gates, post-optimization (H) # CNOT gates ]
nam_data = {
    "adder_8" : [900, 409, 646, 331, 606, 291],
    "barenco_tof_10" : [450, 192, 294, 160, 264, 130],
    "barenco_tof_3" : [58, 24, 42, 20, 40, 18],
    "barenco_tof_4" : [114, 48, 78, 40, 72, 34],
    "barenco_tof_5" : [170, 72, 114, 60, 104, 50],
    "csla_mux_3" : [170, 80, 161, 76, 155, 70],
    "csum_mux_9" : [420, 168, 294, 168, 266, 140],
    "gf2^10_mult" : [1347, 609, 1070, 609, 1070, 609],
    "gf2^16_mult" : [3435, 1581, 2707, 1581, 2707, 1581],
    "gf2^32_mult" : [13562, 6268, 10601, 6299, 10601, 6299],
    "gf2^4_mult" : [225, 99, 187, 99, 187, 99],
    "gf2^5_mult" : [347, 154, 296, 154, 296, 154],
#    "gf2^64_mult" : [61629, 24765, 41563, 24765, 41563, 24765],
    "gf2^6_mult" : [495, 221, 403, 221, 403, 221],
    "gf2^7_mult" : [669,300, 555, 300, 555, 300],
    "gf2^8_mult" : [883, 405, 712, 405, 712, 405],
    "gf2^9_mult" : [1095, 494, 891, 494, 891, 494],
    "mod5_4" : [63, 28, 51, 28, 51, 28],
    "mod_mult_55" : [119, 48, 91, 40, 91, 40],
    "mod_red_21" : [278, 105, 184, 81, 180, 77],
    "qcla_adder_10" : [521, 233, 411, 195, 399, 183],
    "qcla_com_7" : [443, 186, 284, 132, 284, 132],
    "qcla_mod_7" : [884, 382, 636, 302, 624, 292],
    "rc_adder_6" : [200, 93, 142, 73, 140, 71],
    "tof_10" : [255, 102, 175, 70, 175, 70],
    "tof_3" : [45, 18, 35, 14, 35, 14],
    "tof_4" : [75, 30, 55, 22, 55, 22],
    "tof_5" : [105, 42, 75, 30, 75, 30],
    "vbe_adder_3" : [150, 70, 89, 50, 89, 50]
}

if (len(sys.argv) != 4):
    print "Usage: ./generate_nam_comparison.py <output file> <qiskit input file> <SQIRE input file>"
    exit(-1)

outfname = sys.argv[1]
infname1 = sys.argv[2]
infname2 = sys.argv[3]

outf = open(outfname, "w")
inf1 = open(infname1, "r")
inf2 = open(infname2, "r")

outf.write("Name, original, L, H, Qiskit A, Qiskit B, VOQC\n")

qiskit_data = {}
for line in inf1:
    line = line.strip().split(",")
    qiskit_data[line[0].split(".")[0]] = [line[1], line[2]]

sqire_data = {}
for line in inf2:
    line = line.strip().split(",")
    sqire_data[line[0].split("/")[2].split(".")[0]] = [line[1]]

for benchmark in sorted(nam_data.keys()):
    data = [benchmark]
    data.append(str(nam_data[benchmark][0]))
    data.append(str(nam_data[benchmark][2]))
    data.append(str(nam_data[benchmark][4]))
    data += qiskit_data [benchmark]
    if benchmark in sqire_data:
        data += sqire_data[benchmark]
    else:
        data += ""
    outf.write(",".join(data) + "\n")

outf.close()
