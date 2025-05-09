# The program to check Lemma about cuts of size 6 or 7
This program is used to prove Claim regarding cuts of size 6 or 7.
Specifically, it verifies Claim 6.5, 6.9 in Section 6.

## Requirements
+ g++, CMake, Boost, spdlog

## Build
```bash
cmake -S . -B build
cmake --build build
```

## Execution
We prepared a shell script (```checkall.sh```), so we have only to execute the command below.
```
bash checkall.sh toroidal_configurations/reducible/conf toroidal_configurations/reducible/summary.csv > cut6result.log &
```

## Results
The results (log) are written in ```cut6result.log``` if the above command is exected. If the sentence ```(6|7)-cut ... is dangerous in {FILENAME}``` or ```dangerous: may be a bridge ...``` is writtten in log file, it means the configuration described in ```{FILENAME}``` can violate Claim 6.5 or 6.9.

We list configurations that are detecdted as dangerous in this program, but they are handled in other ways.
+ ```C01.conf```: This configration is C(1) in paper. We deal with it in Appendix E.1.
+ ```torus00095.conf```: We deal with it by choosing an appropriate contraction. (This contraction can be used to prove C-reducibility, See ```toroidal_configurations/reducible/contraction_summary.csv```)
```bash
./build/a.out -c toroidal_configurations/reducible/conf/torus00095.conf -e 12 16 19 22 24 25 35
```
+ ```torus00096.conf```: We deal with it by choosing an appropriate contraction. (This contraction can be used to prove C-reducibility, See ```toroidal_configurations/reducible/contraction_summary.csv```)
```bash
./build/a.out -c toroidal_configurations/reducible/conf/torus00096.conf -e 12 17 19 23 25 35
```
+ ```torus01061.conf```: We deal with it in Claim 6.8.



