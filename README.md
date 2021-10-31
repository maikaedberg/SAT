# CSE301_Project

To run the file, simply
```
$ cd Main
$ ghc MySAT
```
on the command line.

To run your CNF file of choice, run
```
$ ./MySat filename.cnf 
```
with your flags of choice, including
  subsumption: -ss
  self-subsumption: -sss
  unit propogation: -up
  pure literal elimination: -ple
  greedy picking of cluases: -greedy
  3 cnf: -3cnf
  
Now, the folder two-watch-literals is an experiment implementing two-watch literals. 
It is not faster than regular unit propogation, but is there to show the attempt that we made in implementing it.
To run:
```
$ cd -
$ cd Main
$ ghc MySAT
```
