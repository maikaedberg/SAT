# CSE301_Project

To run the file, simple run
```
$ ghc MySAT
```
on the command line.

To run your CNF file of choise, run
```
$ ./MySat filename.cnf 
```
with your flags of choice, including
  subsumption: -ss
  unit propogation: -up
  pure literal elimination: -ple
  greedy picking of cluases: -greedy
  3 cnf: -3cnf
  
Now, the file TwoWatch.hs is an experiment implementing two-watch literals. 
It is not faster than regular unit propogation, but is there to show the attempt that we made in implementing it.
To run it, just comment out lines 42-49 on MySat.hs and comment in 39-41. Then follow the steps us as before.
