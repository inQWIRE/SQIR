import sys

if __name__ == "__main__":
    inFile = sys.argv[1]
    fIn = open(inFile, "r")
    lines = fIn.readlines()
    fIn.close()

    # Keys are "Original" and "Final".
    # Value are dicts mapping gate names to counts
    resDict = {}
    elapsedTime = None
    for line in lines:
        if line.startswith("Original") or line.startswith("Final"):
            category = line.split(":")[0].strip()
            resDict[category] = {}
            tokens = [x.strip() for x in line.split(":")[-1].split(",")]
            for token in tokens:
                gateName = token.split()[0].strip()
                count = token.split()[-1].strip()
                resDict[category][gateName] = count
        elif line.startswith("real"):
            elapsedTime = line.split()[-1].strip()

    # Print out results. The run_benchmarks script will redirect
    # this to the CSV file. Below is the header
    # name,Orig. total,Orig. Rz,Orig. T,Orig. H,Orig. X,Orig. CNOT,VOQC total,VOQC Rz,VOQC T,VOQC H,VOQC X,VOQC CNOT,time
    name = inFile.split("/")[-1].split(".txt")[0].strip()
    print("%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s" %(name, resDict["Original"]["Total"], resDict["Original"]["Rz"],\
                                                          resDict["Original"]["T"], resDict["Original"]["H"], \
                                                          resDict["Original"]["X"], resDict["Original"]["CNOT"],\
                                                          resDict["Final"]["Total"], resDict["Final"]["Rz"],\
                                                          resDict["Final"]["T"], resDict["Final"]["H"],\
                                                          resDict["Final"]["X"], resDict["Final"]["CNOT"], elapsedTime))

