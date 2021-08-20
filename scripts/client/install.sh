#!/bin/bash

sudo apt-get update
sleep 1

echo "Install ab"
which ab > /dev/null
if [[ $? != 0 ]]; then
	sudo apt-get install -y apache2-utils
fi

echo "Install env for YCSB"
sudo apt-get install default-jre default-jdk maven
sleep 1
curl -O --location https://github.com/brianfrankcooper/YCSB/releases/download/0.17.0/ycsb-0.17.0.tar.gz
tar xfvz ycsb-0.17.0.tar.gz

wget http://hp03.ncl.cs.columbia.edu/files/sosp-ae-vm -O /root/.ssh/sosp-ae-vm
chmod 600 /root/.ssh/sosp-ae-vm
cat ssh-config.config >> /root/.ssh/config
