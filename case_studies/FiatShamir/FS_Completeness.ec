pragma Goals:printall.
require import AllCore DBool Bool List Distr.
require import FS_Basics.



section.

local lemma qr_complete_h ya wa : completeness_relation ya wa
   => hoare [ Completeness(HP,HV).run : arg = (ya,wa) ==> res ].
move => [qra invrtbl].
proc. inline*.  wp.
rnd. wp.  rnd.  wp.
skip.  simplify. progress.  simplify. apply ZModpRing.unitrM. smt (d_prop4).
have -> : s{hr}  = (w{hr} * w{hr}).
apply qra. 
have ->: ch. clear H0. smt. 
simplify.
smt.
smt.
qed.


local lemma qr_complete_ph ya wa : completeness_relation ya wa 
   => phoare [ Completeness(HP,HV).run : arg = (ya,wa) ==> res ] = 1%r.
move => [qra invrtbl].
proc*.
seq 1 : true 1%r 1%r 1%r 0%r r.
call (qr_complete_h ya wa). auto.
conseq (_: true ==> true). inline*. sp.
wp.  progress. rnd. simplify.
conseq (_: true ==> true). smt.
wp.  rnd. skip. simplify.
progress. apply d_prop5. auto. auto. auto.
qed.


lemma qr_completeness: forall (statement:qr_stat) (witness:qr_wit) &m,
  completeness_relation statement witness =>
  Pr[Completeness(HP,HV).run(statement, witness) @ &m : res] = 1%r.
progress. byphoare (_: arg = (statement, witness) ==> _);auto.
conseq (qr_complete_ph statement witness _). auto. 
qed.


lemma qr_completeness_iter: forall (statement:qr_stat) (witness:qr_wit) &m n,
        1 <= n =>
       completeness_relation statement witness =>
      Pr[CompletenessAmp(HP,HV).run(statement, witness,n) @ &m : res] = 1%r.
progress.
apply (FiatShamir.CompletenessTheory.Perfect.completeness_seq HP HV _ _ _ _ _ &m).
proc.  skip.  auto.
proc.  wp.  rnd.  skip.  progress. smt.
proc.  wp.  skip. auto.
proc. rnd. wp. skip.  progress. smt (d_prop5).
progress.
apply qr_completeness. auto. auto. auto.
qed.

end section.
