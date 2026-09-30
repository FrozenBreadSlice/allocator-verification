# README 

## Installing dependencies
This project depends on Rocq 9.2.0 and Iris dev.2026-07-21.1.514e0b41

Using opam switches 
Adding new: `opam repo add [name] [url]`

Creating and activating a local switch
```
opam switch create . 5.5.0    
eval $(opam env)
opam switch (to see what switch your on)
```
Installing Rocq 9.2.0
```
opam install rocq-runtime.9.2.0 
```
Installing iris dev version 
```
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam install rocq-iris.dev.2026-07-21.1.514e0b41
opam install rocq-iris-heap-lang.dev.2026-07-21.1.514e0b41
```

## Building source
```
make -f RocqMakefile
```
