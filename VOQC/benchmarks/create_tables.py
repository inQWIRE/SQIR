'''
    Assumes that the following files exist in the current
    directory: pyzx_out.csv, qiskit_out.csv, tket_out.csv,
    voqc_out.csv
'''

import os
import sys
import numpy as np
import re

#############################################################################################
# Open each file, read in the lines and parse
# into a dictionary. The keys are the circuit names.
# Values are another dictionary where the keys are
# the header fields. This dictionary is returned
def parseCVStoDict(fileName):
    fIn = open(fileName, "r")
    lines = fIn.readlines()
    fIn.close()
    header = lines[0].split(",")[1:]
    del lines[0]
    res_dict = {}
    for line in lines:
        circuit_name = line.split(",")[0].split(".qasm")[0]
        res_dict[circuit_name] = {}
        fields = line.split(",")[1:]
        idx = 0
        for field in fields:
            res_dict[circuit_name][header[idx].strip()] = field.strip()
            idx+=1
        
    return res_dict

#############################################################################################

# human sorting method, taken from stack overflow
def sorted_nicely( l ): 
    """ Sort the given iterable in the way that humans expect.""" 
    convert = lambda text: int(text) if text.isdigit() else text 
    alphanum_key = lambda key: [ convert(c) for c in re.split('([0-9]+)', key) ] 
    return sorted(l, key = alphanum_key)

# geomean function
def geo_mean(nums):
    a = np.array(nums)
    return a.prod()**(1.0/len(a))

# Calculate the geomean runtime for each tool across all circuits
def outputGeomeanRuntimes(qiskit_dict, tket_dict, voqc_dict, pyzx_dict):
    qiskit_times = [float(x["time"].split("s")[0]) for x in qiskit_dict.values()]
    tket_times = [float(x["time"].split("s")[0]) for x in tket_dict.values()]
    voqc_times = [float(x["optimization time"].split("s")[0]) for x in voqc_dict.values()]
    pyzx_times = [float(x["time"].split("s")[0]) for x in pyzx_dict.values()]
    print("\n### Geometric mean runtimes over all 28 benchmarks\n")
    print("VOQC  | Qiskit  | tket  | PyZX")
    print("---------------------------------")
    print("%.3f |  %.3f  | %.3f | %.3f" %(geo_mean(voqc_times), geo_mean(qiskit_times),\
                                          geo_mean(tket_times), geo_mean(pyzx_times)))
    print("")

#############################################################################################

# Outputs Table 2 from the paper
def outputTable2(qiskit_dict, tket_dict, voqc_dict):
    print("\n\n#### Table 2: Reduced total gate counts on Amy et al. benchmarks.\n")
    print("%s| Original\tQiskit\t\ttket\t\tVOQC" %("Name".ljust(15)))
    print("----------------------------------------------------------------------")
    # Sort circuit names
    circuits = sorted_nicely(voqc_dict.keys())
    qiskit_red = []
    tket_red = []
    voqc_red = []
    for circuit in circuits:
        # orig is same in all dicts
        orig = qiskit_dict[circuit]["Orig. total"]
        qiskit = qiskit_dict[circuit]["Qiskit total"]
        tket = tket_dict[circuit]["tket total"]
        voqc = voqc_dict[circuit]["VOQC total"]
        print("%s| %s\t\t%s\t\t%s\t\t%s" %(circuit.ljust(15), orig, qiskit, tket, voqc))
        if circuit != "qcla_mod_7":
            qiskit_red += [(1.0-float(qiskit)/float(orig))*100]
            tket_red += [(1.0-float(tket)/float(orig))*100]
            voqc_red += [(1.0-float(voqc)/float(orig))*100]

    # Print average reduction. One less circuit due to red box in paper
    num_cirs = len(circuits)-1
    print("----------------------------------------------------------------------")
    print("%s| -\t\t%.1f%%\t\t%.1f%%\t\t%.1f%%" %("Geo Mean Reduction".ljust(15),\
                                             geo_mean(qiskit_red),\
                                             geo_mean(tket_red),\
                                             geo_mean(voqc_red)))

#############################################################################################

# Outputs Table 3 from the paper
def outputTable3(voqc_dict, pyzx_dict):
    print("\n\n#### Table 3: Reduced T-gate counts on Amy et al. benchmarks.\n")
    print("%s| Original\tPyZX\t\tVOQC" %("Name".ljust(15)))
    print("----------------------------------------------------------------------")
    # Sort circuit names
    circuits = sorted_nicely(voqc_dict.keys())
    pyzx_red = []
    voqc_red = []
    for circuit in circuits:
        # orig is same in all dicts
        orig = voqc_dict[circuit]["Orig. T"]
        pyzx = pyzx_dict[circuit]["PyZX T"]
        voqc = voqc_dict[circuit]["VOQC T"]
        print("%s| %s\t\t%s\t\t%s" %(circuit.ljust(15), orig, pyzx, voqc))
        # Exclude these two benchmarks from averages
        if circuit != "csla_mux_3" and circuit != "qcla_mod_7":
            pyzx_red += [(1.0-float(pyzx)/float(orig))*100]
            voqc_red += [(1.0-float(voqc)/float(orig))*100]

    # Print average reduction. 2 less circuits due to red boxes in paper
    num_cirs = len(circuits)-2
    print("----------------------------------------------------------------------")
    print("%s| -\t\t%.1f%%\t\t%.1f%%" %("Geo Mean Reduction".ljust(15),\
                                        geo_mean(pyzx_red),\
                                        geo_mean(voqc_red)))


#############################################################################################
if __name__ == "__main__":
    # Read in each CVS into a dictionary
    pyzx_dict = parseCVStoDict("pyzx_out.csv")
    qiskit_dict = parseCVStoDict("qiskit_out.csv")
    tket_dict = parseCVStoDict("tket_out.csv")
    voqc_dict = parseCVStoDict("voqc_out.csv")

    # Print out geomean runtimes across all
    # circuits
    outputGeomeanRuntimes(qiskit_dict, tket_dict, voqc_dict, pyzx_dict)

    # Construct Table 2 in the paper. The header for
    # this table is:
    #
    #   Name  Original  Qiskit  tket  VOQC
    #
    # The values are total gate count
    outputTable2(qiskit_dict, tket_dict, voqc_dict)

    # Construct Table 3 in the paper. The header for
    # this table is:
    #
    #   Name  Original  PyZX  VOQC
    #
    # The values are the T gate counts
    outputTable3(voqc_dict, pyzx_dict)

    print("")

