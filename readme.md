Maple script for equivariant cohomology of flag manifolds
==================
* written by S. Kaji
* some algorithms are explained in:  
S. Kaji, Three presentations of torus equivariant cohomology of flag manifolds, in Proceedings of International Mathematics Conference in honour of the 70th Birthday of Professor S. A. Ilori  
arXiv:1504.01091   http://arxiv.org/abs/1504.01091


This script requires the “coxeter and weyl package” by J.Stembridge.
Download it from:

* http://www.math.lsa.umich.edu/~jrs/maple.html

rename it to “coxeter.txt” 
and place in the same directory as the script file.


## contents
### Maple worksheets
* BGG_example.mws:  Example for calculation of H^*(E_8/P_2;Z)  
* BGGT_example.mws: Example for calculation of H^*_T(G/B;Z)
* BGG_graph_example.mws: Example for drawing GKM-graph for G/P

### Maple scripts
* BGG.mpl: module for ordinary cohomology (optimised for exceptional types)
* BGGT.mpl: module for equivariant cohomology
* WeylOps.mpl: module for Weyl group manipulation
* BGG_graph.mpl: module for drawing GKM-graph
