#!/bin/bash

mkdir -p output

for k in $(seq 5 5 25)
do
    ./Minting -d dataset/WCGoals.gfu -k $k > output/WCGoals_$k

    elapsed_time=$(grep "Elapsed Time" output/WCGoals_$k | awk '{print $NF}')

    echo "Elapsed Time when k is $k = $elapsed_time (s)"
done
