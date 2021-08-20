#!/bin/bash

BENCHMARKS=(apache kern hack mongo redis)
i=0

cd /mydata
for bench in ${BENCHMARKS[@]}; do
	echo "Downloading " $bench
	wget http://hp03.ncl.cs.columbia.edu/files/cloud-$bench.img &
	pids[${i}]=$!
	i=$((i+1))
done

for pid in ${pids[*]}; do
	wait $pid
done
