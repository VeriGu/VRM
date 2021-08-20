#!/bin/bash
NUM=8

usage(){
	echo "usage: ./multi-run.sh apache|mango|redis|hack|kern"
}

if [ $# -lt 1 ]; then
	usage
	exit 1
fi

if [ $1 = apache ] || [ $1 = mongo ] || [ $1 = redis ] || [ $1 = hack ] || [ $1 = kern ]; then
	BENCHMARK=$1
	echo $NUM
	for i in `seq 1 $NUM`;
	do
		if [ "$i" -ge "10" ]; then
	                IP=10.10.1.1$i
	        else
	                IP=10.10.1.10$i
	        fi
	
		./$BENCHMARK.sh $IP &
	done
else
	usage
fi

