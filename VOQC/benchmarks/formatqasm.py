import sys
import re
import math

if (len(sys.argv) != 3):
    print "Usage: ./formatqasm <input file> <output filename>"
    exit(-1)

inf = open(sys.argv[1])
outf = open(sys.argv[2], "w")

for line in inf:
    m = re.match(r"rz\(([-+]?(\d+(\.\d*)?|\.\d+)([eE][-+]?\d+)?)\*pi\) q\[([0-9]+)\];\n", line)
    if m:
        angle = float(m.group(1))
        neg = False
        if angle < 0:
            angle = - angle
            neg = True
        den = 2 ** (round(- math.log(angle, 2)))
        error = angle - (1.0 / den)
        if (abs(error) > 0.0000000001):
            print ("ERROR: Rounding did not work correctly for %.10f" % angle)
        arg = int(m.group(5))
        if neg:
            num = -1
        else:
            num = 1
        outf.write("rzq(%d,%d) q[%d];\n" % (num, den, arg))
    else:
        outf.write(line)