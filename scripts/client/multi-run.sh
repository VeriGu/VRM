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
	RESULTS="${1}.txt"
	if [ ! $1 = hack ] && [ ! $1 = kern ]; then
		if [ -f $RESULTS ]; then
			now=`date +"%Y-%m-%d-%H-%M-%S"`
			old="${RESULTS}-${now}"
			echo "backup old $RESULTS to ${old}"
			mv $RESULTS $old
		fi
	fi

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

	for job in `jobs -p`
	do
		wait $job
	done

else
	usage
fi

