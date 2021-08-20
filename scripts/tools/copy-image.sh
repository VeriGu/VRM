BENCHMARKS=(apache kern hack mongo redis)
for i in `seq 1 8`;
do
	for bench in ${BENCHMARKS[@]}; do
		CMD="cp /mydata/cloud-$bench.img /mydata/cloud-$bench-$i.img"
        	echo $CMD
        	$CMD

        	CMD="mount /mydata/cloud-$bench-$i.img /mnt"
        	echo $CMD
        	$CMD

	
        	if [ "$i" -ge "10" ]; then
        	        IP=1$i
        	else
        	        IP=10$i

        	fi

		#CONFIGURE IP FOR EACH GUEST VM
        	sed "s/100/$IP/" /mnt/etc/netplan/50-cloud-init.yaml -i
        	cat /mnt/etc/netplan/50-cloud-init.yaml
        	sleep 1

        	umount /mnt/
		sync
        	sleep 1
	done

done
