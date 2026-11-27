/* Cross-check: fundamental D with -30000 < D < 0 whose class group has exponent 1 or 3.
   quadclassunit is GRH-conditional in general; here it only cross-checks exact_classgroups.py. */
v=[];for(m=3,30000,D=-m;if(isfundamental(D),c=quadclassunit(D).cyc;e=if(#c,c[1],1);if(e==1||e==3,v=concat(v,[[D,e,c]]))));
print(#v);for(i=1,#v,print(v[i]));
