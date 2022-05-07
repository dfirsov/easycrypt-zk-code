pragma Goals:printall.
require import AllCore DBool Bool List Distr Aux RealExp.
require import Basics.


section.
declare module P : MaliciousProver {HonestVerifier}.

axiom P_response_ll : islossless P.response.

local lemma qr_soundness_ph s ax :
     ! in_language IsSqRoot s => phoare [ Soundness(P,HonestVerifier).run : arg = (s,ax) ==> res ] <= (1%r/2%r).
proof. move => qra.
proc. inline*. 
wp.
seq 3 : ((statement,aux) = (s,ax) /\ statement0 = statement /\ commitment = commit) (1%r) (1%r/2%r) (0%r) (1%r).  auto. auto.
exists* commit. elim*. move => cv.
case (!IsQR (cv)).
seq 1 : (!challenge0) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = commit /\ s = statement /\ ax = aux /\ !IsQR cv).
rnd.  skip. auto.
hoare. call (_:true ==> true). auto.
wp. auto. progress. rewrite H0. simplify.   smt.
rnd.  skip.  progress. 

have -> : (fun (x : bool) => x) = pred1 true. smt. 
have ->: mu1 (duniform [false; true]) true = 1%r/2%r. 
rewrite duniform1E_uniq. auto. simplify. auto. auto.
simplify. 
conseq (_: _ ==> true). call (_: true ==> true). auto.  auto. auto.
seq 1 : (!challenge0) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = commit /\ s = statement /\ ax = aux /\ IsQR cv).
rnd. skip. auto.
hoare. 
call (_:true ==> true). auto.  
wp. skip. progress. rewrite H0. simplify. smt.
rnd. skip. progress. 
have -> : (fun (x : bool) => x) = pred1 true. smt. 
have ->: mu1 (duniform [false; true]) true = 1%r/2%r. 
rewrite duniform1E_uniq. auto. simplify. auto. auto.
conseq (_: _ ==> true). call (_:true ==> true). auto.
wp. skip. auto. auto.
hoare.
simplify. auto. call (_ : true ==> true).  auto. skip. auto. auto.
qed.


lemma qr_soundness &m s ax:
    ! in_language IsSqRoot s =>
     Pr[Soundness(P, HonestVerifier).run(s, ax) @ &m : res]
     <= 1%r/2%r.
progress. byphoare (_: arg = (s,ax) ==> _);auto.
apply (qr_soundness_ph s ax);auto.
qed.


end section.
