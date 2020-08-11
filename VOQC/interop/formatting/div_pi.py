import re
from gmpy2 import *
import os.path
from qiskit.qasm import pi

#Undo multiplication of pi by Qiskit, and re-format for VOQC pass
def div_pi(fname):
    count = 0
    rz = []
    p_rz = re.compile("rz\(([-+]?(\d+(\.\d*)?|\.\d+)([eE][-+]?\d+)?)\) q\[([0-9]+)\];")
    with open(str(fname), 'r') as f:
        data = f.readlines()
        for line in data:
            m1 = p_rz.match(line)
            if m1:
                rz.append(count)
            count = count+1
    for i in range(len(rz)):
        a = p_rz.match(data[rz[i]])
        num1 = (float(a.group(1))/pi)
        q = int(a.group(5))
        data[rz[i]] = "rz(%s*pi) q[%d];\n" % (num1, q)

    with open(str(fname), 'w') as f:
        f.writelines(data)
