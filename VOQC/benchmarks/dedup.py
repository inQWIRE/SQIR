import sys
import re
import math

if (len(sys.argv) != 3):
    print "Usage: ./formatqasm <input file> <output filename>"
    exit(-1)

inf = open(sys.argv[1])
outf = open(sys.argv[2], "w")

lastidx = None
for line in inf:
    m = re.match(r"h q\[([0-9]+)\];\n", line)
    if m:
        arg = int(m.group(1))
        if lastidx:
            if lastidx == arg:
                # don't write
                lastidx = None 
            else:
                outf.write("h q[%d];\n" % lastidx)
                lastidx = arg
        else:
            lastidx = arg
    else:
        if lastidx:
            outf.write("h q[%d];\n" % lastidx)
            lastidx = None
        outf.write(line)
if lastidx:
    outf.write("h q[%d];\n" % lastidx)