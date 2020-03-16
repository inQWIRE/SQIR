import sys

if __name__ == "__main__":
    inFile = sys.argv[1]
    fIn = open(inFile, "r")
    lines = fIn.readlines()
    fIn.close()

    # Keys are "Original" and "Final".
    # Value are dicts mapping gate names to counts
    resDict = {}
    pTime = None
    oTime = None
    wTime = None
    for line in lines:
        if line.startswith("Original (n iter.)") or line.startswith("Final (n iter. w/ LCR)"):
            category = line.split(":")[0].strip()
            category = category.split(" ")[0]
            resDict[category] = {}
            tokens = [x.strip() for x in line.split(":")[-1].split(",")]
            for token in tokens:
                gateName = token.split()[0].strip()
                count = token.split()[-1].strip()
                resDict[category][gateName] = count
        elif line.startswith("Time"):
            t = line.split()[-1].strip()
            if line.find("parse") != -1:
                pTime = t
            elif line.find("optimize") != -1:
                oTime = t
            elif line.find("write") != -1:
                wTime = t

    # Print out results. The run_benchmarks script will redirect
    # this to the CSV file. Below is the header
    # name,Orig. total,Orig. Rz,Orig. Cliff,Orig. H,Orig. X,Orig. CNOT,VOQC total,VOQC Rz,VOQC Cliff,VOQC H,VOQC X,VOQC CNOT,time
    name = inFile.split("/")[-1].split(".txt")[0].strip()
    print("%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s,%s" %(name, resDict["Original"]["Total"], resDict["Original"]["Rz"],\
                                                          resDict["Original"]["Clifford"], resDict["Original"]["H"], \
                                                          resDict["Original"]["X"], resDict["Original"]["CNOT"],\
                                                          resDict["Final"]["Total"], resDict["Final"]["Rz"],\
                                                          resDict["Final"]["Clifford"], resDict["Final"]["H"],\
                                                          resDict["Final"]["X"], resDict["Final"]["CNOT"], pTime, oTime, wTime))

