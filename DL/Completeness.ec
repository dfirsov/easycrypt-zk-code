pragma Goals:printall.
require import AllCore DBool Bool List Distr.
require import Basics.

require import CyclicGroup.

import FDistr.


section.


local lemma dl_complete_h (p : dl_prob) (w : dl_wit) : 
  IsDL p w =>
   hoare [ Completeness(HonestProver,HonestVerifier).run : arg = (p,w) ==> res ].
progress.
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.
rewrite /verify_transcript. simplify.
rewrite /dl_verify. simplify. smt.
qed. 


local lemma dl_complete_ph ya wa : IsDL ya wa
   => phoare [ Completeness(HonestProver,HonestVerifier).run : arg = (ya,wa) ==> res ] = 1%r.
move => isdl.
proc*.
seq 1 : true 1%r 1%r 1%r 0%r r.
call (dl_complete_h ya wa). auto.
conseq (_: true ==> true). inline*. sp.
wp.  progress. rnd. simplify.
conseq (_: true ==> true). smt.
wp.  rnd. skip. simplify.
progress. smt. auto. auto. auto.
qed.

    (* (c1 - c2) * a    *)
lemma dl_completeness: forall (statement : dl_prob) (witness : dl_wit) &m,
  IsDL statement witness =>
     Pr[Completeness(HonestProver, HonestVerifier).run(statement, witness) 
            @ &m : res] = 1%r.
progress. byphoare (_: arg = (statement, witness) ==> _);auto.
conseq (dl_complete_ph  statement witness _). auto. 
qed.

  
end section.
