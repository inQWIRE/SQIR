import sys
import re

if (len(sys.argv) != 3):
    print "Usage: ./formatqasm <input file> <output filename>"
    exit(-1)

inf = open(sys.argv[1])
outf = open(sys.argv[2], "w")

for line in inf:
    m = re.match(r"rz\(([-+]?(\d+(\.\d*)?|\.\d+)([eE][-+]?\d+)?)\*pi\) q\[([0-9]+)\];\n", line)
    if m:
        rounded_angle = round(float(m.group(1)) * (2 ** 15))
        if rounded_angle < 0:
            rounded_angle += (2 ** 15)
        arg = int(m.group(5))
        outf.write("rzk(%d) q[%d];\n" % (rounded_angle, arg))
    else:
        outf.write(line)