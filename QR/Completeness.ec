pragma Goals:printall.
require import AllCore DBool Bool List Distr.
require import Basics.


section.

local lemma qr_complete_h ya wa : completeness_relation ya wa
   => hoare [ Completeness(HP,HV).run : arg = (ya,wa) ==> res ].
move => [qra invrtbl].
proc. inline*.  wp.
rnd. wp.  rnd.  wp.
skip. progress.   apply (d_prop4 rrr.`1 rrr.`2). smt. 
have -> : s{hr}  = (w{hr} * w{hr}).
apply qra.
have ->: challenge00. smt. 
simplify.
have -> : rrr.`2 = rrr.`1 * rrr.`1.  smt(d_prop1).
smt.
apply (d_prop4 rrr.`1 rrr.`2). smt. 
have ->: !challenge00. smt. 
simplify. smt.
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


lemma qr_completeness: forall (statement:qr_prob) (witness:qr_wit) &m,
        IsSqRoot statement witness /\ unit statement =>
     Pr[Completeness(HP,HV).run(statement, witness) @ &m : res] = 1%r.
progress. byphoare (_: arg = (statement, witness) ==> _);auto.
conseq (qr_complete_ph statement witness _). auto. 
qed.

end section.
