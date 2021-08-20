NUM=8

echo $NUM
for i in `seq 1 $NUM`;
do
	if [ "$i" -ge "10" ]; then
                IP=10.10.1.1$i
        else
                IP=10.10.1.10$i

        fi

	CMD="ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no $IP"
	echo $CMD
	$CMD "exit"
done

