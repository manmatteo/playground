module oracle-fpc.
/* start */
decide_ke  (start Oracle) (consume Oracle) root. 
store_kc   (start Oracle) (start Oracle) root.
decide_ke  (restart Oracle) (consume Oracle) root.
store_kc   (restart Oracle) (restart Oracle) lit.
true_ke    (consume emp).
initial_ke (consume emp) lit.
orPos_ke   (consume (l Oracle)) (consume Oracle) left.
orPos_ke   (consume (r Oracle)) (consume Oracle) right.
andPos_ke  (consume (c Left Right)) (consume Left) (consume Right).
release_ke (consume Oracle) (restart Oracle).
/* end */
