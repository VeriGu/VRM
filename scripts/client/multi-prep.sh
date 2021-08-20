NUM=8

usage(){
	echo "usage: ./multi-prep.sh apache|mango|redis"
}

if [ $# -lt 1 ]; then
	usage
	exit 1
fi

if [ $1 = apache ] || [ $1 = mongo ] || [ $1 = redis ]; then
	BENCHMARK=$1
	
	echo $NUM
	for i in `seq 1 $NUM`;
	do
		if [ "$i" -ge "10" ]; then
	                IP=10.10.1.1$i
	        else
	                IP=10.10.1.10$i
	
	        fi
	
		CMD="./prep-$BENCHMARK.sh $IP"
		echo $CMD
		$CMD
	done
else
	usage
fi

