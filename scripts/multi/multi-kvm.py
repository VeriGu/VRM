#!/usr/bin/python

import sys
import os

benchmarks = ["apache", "hack", "kern", "mongo", "redis"]
usage = "Usage: ./multi-sekvm.py apache|hack|kern|mongo|redis"

if len(sys.argv) < 2:
    print(usage)
    exit(0)
else:
    benchmark = sys.argv[1]
    if benchmark not in benchmarks:
        print(usage)
        exit(0)

NUM = 8
QEMU="/srv/vm/qemu"
CMD = "./run-guest-n.sh -q {} -k ../tests/Image.sekvm -i /mydata/cloud-{}-{}.img -m tcp:localhost:444{},server,nowait -x {}"

print("Launch %d VM(s)"%NUM)

os.system("../tools/net.sh")

for i in range(1, int(NUM) + 1):
    pid = os.fork()
    mac = "de:ad:be:ef:f6:b" + str(i)
    if pid == 0:
        os.system(CMD.format(QEMU, benchmark, i, i, mac))
        exit(0)
    print(CMD.format(QEMU, benchmark, i, i, mac))

