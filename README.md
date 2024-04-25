# Modelchecker
A recent open-source MC tool developed by Xindi Zhang, Lingfeng Zhu, Shaowei Cai, Yongjian Li, from ISCAS. Modelchecker implements the IC3 with an advanced incremental SAT solver named CaDiCaL

## Usage
---
To build:

```
./rebulid.sh
make clean
make -j
```

To Run:

```
$ ./modelchecker <AIGER_file> [-sc][-acc]
```
- -sc: enable safe sub-cube derivation
- -acc: enable assuption-core consistency