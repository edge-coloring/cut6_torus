#!/bin/bash
set -euxo pipefail

#
# Usage)
# bash checkall.sh <The directory that contains configuration files> <The summary file>
#
# Example)
# bash checkall.sh toroidal_configurations/reducible/conf toroidal_configurations/reducible/summary.csv
#

confdir=$1
summary=$2

while IFS="," read f status csize conts; do
    filename=$(basename $f)
    conf=${filename%.*}
    if [ $status = "C" ]; then
        ./build/a.out -c ${confdir}/${conf}.conf -e $(echo "${conts}" | tr -d '"' | tr '+' ' ')
    fi
done < "$summary"
