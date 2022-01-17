This repository contains Magma code for the paper:  "Possible indices for the Galois image of elliptic curves over Q"  (https://arxiv.org/abs/1508.07663)
  
The file "FindGroups.m" computes the groups G(N) satisfying conditions (a), (b), (c) and (d) from Definition 4.1 of the paper, as we vary over all congruence subgroup of PSL(2,Z), up to conjugacy in PGL(2,Z), of genus 0 and 1.  The groups are outputed to files "groups0.dat" and "groups1.dat" depending on the genus.

The file "IndexComputations.m" has code for the computations in section 5.2 and 5.3 of the paper; it requires the files groups0.dat and groups1.dat.

There are many cases to consider and the code may take a while before it finishes; it took around 40 minutes using one of Cornell math department's machines.