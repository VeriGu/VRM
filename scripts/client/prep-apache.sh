#!/bin/bash                                                                                                                                                                       

SRV=$1

ssh -o UserKnownHostsFile=/dev/null -o StrictHostKeyChecking=no $SRV "service apache2 start"
