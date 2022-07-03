pragma Goals:printall.
require import AllCore.
require import Distr.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.

require import RandomFacts.
require Reflection.


theory RewCommNI.

type at1, rt1, at2, rt2, sbits, irt, rrt, iat.


op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.


require RewBasics.
clone import RewBasics as RW with type sbits <- sbits,
                                  type rrt <- rrt,
                                  type irt <- irt,
                                  type iat <- iat,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.


module type RewRun = {
  proc getState()          : sbits
  proc * setState(b : sbits) : unit
  proc ex1(a:at1) : rt1
  proc ex2(a:at2) : rt2
}.



module CommNoInit(A : RewRun) = {
  proc ex1ex2(a1 : at1, a2 : at2) = {
     var r1, r2, s;
     s <@ A.getState();
     r1 <@ A.ex1(a1);
     A.setState(s);
     r2 <@ A.ex2(a2);
     return (r1,r2);
  }

  proc ex2ex1(a1 : at1, a2 : at2) = {
     var r1, r2, s;
     s <@ A.getState();
     r2 <@ A.ex2(a2);
     A.setState(s);
     r1 <@ A.ex1(a1);
     return (r1,r2);
  }
}.


section.
declare module A <: RewRun. 


local module BestModule(A : RewRun) = {
  proc main(a : at1) : rt1 = {
    var s, r;
    s <@ A.getState();
    r <@ A.ex1(a);
    A.setState(s);
    return r;
  }

  proc main'(a, d : at1 -> rt1 distr) = {
    var r;
    r <$ d a;
    return r;
  }

  proc comm1(a1,a2) = {
     var r1, r2, s;
     r1 <@ main(a1);
     s <@ A.getState();
     r2 <@ A.ex2(a2);
     A.setState(s);
     return (r1,r2);
  }

  proc comm2(a1,a2, d : at1 -> rt1 distr) = {
     var r1, r2, s;
     r1 <@ main'(a1,d);
     s <@ A.getState();
     r2 <@ A.ex2(a2);
     A.setState(s);
     return (r1,r2);
  }

  proc comm3(a1,a2, d : at1 -> rt1 distr) = {
     var r1, r2,s;
     s <@ A.getState();
     r2 <@ A.ex2(a2);
     A.setState(s);
     r1 <@ main'(a1,d);
     return (r1,r2);
  }

  proc comm4(a1,a2) = {
     var r1, r2, s;
     s <@ A.getState();
     r2 <@ A.ex2(a2);
     A.setState(s);
     r1 <@ main(a1);
     return (r1,r2);
  }

}.


clone import Reflection.Refl with type at <- at1,
                                  type rt <- rt1.

                                  
(* getState lossless follows from rewindable_A, but setState lossless does not, so we ask it *)
declare axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

  
local module WA = {
  proc main(a:at1) : rt1 = {
   var r;
   r <@ A.ex1(a);
   return r;
  }
}.


local lemma bestLemma : exists D, 
   equiv [ BestModule(A).main ~ BestModule(A).main' : 
   ={glob A} /\ arg{1} = arg.`1{2} /\ arg.`2{2} = D (glob A){2} ==> ={glob A, res} ].
elim (reflection_simple_res WA). simplify.
move => D Dprop.
exists D.
bypr (res, glob A){1} (res, glob A){2}.
move => &1 &2 x.
progress.
move => &1 &2 x. progress.
case (x.`2{1} <> (glob A){1}).
move => ss.
have jk : Pr[BestModule(A).main(a{1}) @ &1 : (res, glob A) = x]= 0%r.
byphoare (_: (exists ga, (glob A = ga)) /\ ((glob A) <> x.`2) ==> _). elim*. move => ga.
hoare. 
elim (rewindable_A_plus A RewProp).
progress. proc.
call (H7 ga). call(_:true).
call (H4 ga). skip. progress. smt. auto.  smt. auto.  
rewrite jk. clear jk.
byphoare (_: (glob A) <> x.`2 ==> _) . hoare. proc. rnd.  skip. smt. smt. auto.
simplify.
move => pcc.
have jkk : Pr[BestModule(A).main(a{1}) @ &1 : (res, (glob A)) = x] = Pr[BestModule(A).main(a{1}) @ &1 : res = x.`1]. 
byequiv(_: (exists ga, (glob A){1} = ga) /\ ={glob A, arg} /\ x.`2 = (glob A){1}  ==> _).
elim (rewindable_A_plus A RewProp).
progress. proc.
  elim*.
move => ga.
call {1} (H6 ga). 
call {2} (H6 ga). 
call(_:true).
call {1} (H3 ga). 
call {2} (H3 ga).  skip. progress. smt. smt. smt. smt.
rewrite jkk.
have  kkj : Pr[BestModule(A).main'(a{2}, d{2}) @ &2 : (res, (glob A)) = x] =  Pr[BestModule(A).main'(a{2}, d{2}) @ &2 : res = x.`1].
byequiv(_: ={glob A, arg} /\ x.`2 = (glob A){1}  ==> _).
proc. rnd. skip. progress. smt. smt. smt. smt.
rewrite kkj. clear jkk. clear kkj.
have kkj : Pr[BestModule(A).main'(a{2}, d{2}) @ &2 : res = x.`1]
   =   mu1 (D (glob A){2} a{2}) x.`1.
byphoare (_: arg = (a{2} , d{2})  ==> _). 
proc. rnd.  skip. progress. smt. auto. auto.
rewrite kkj.
rewrite Dprop.
byequiv (_: exists ga, ga = (glob A){1} /\  ={arg, glob A} ==> _).
proc*. inline*. sp. wp.
elim*. move => ga.
elim (rewindable_A_plus A RewProp).
progress. call {1} (H6 ga). call(_:true). call {1} (H3 ga). skip. progress.
smt. smt.
qed.


local lemma bestLemma1 &m : exists D, (forall M a1 a2,
  Pr[BestModule(A).comm1(a1,a2) @ &m : M res] = Pr[BestModule(A).comm2(a1,a2, D (glob A){m}) @ &m : M  res]) /\
  (forall M a1 a2 d, Pr[BestModule(A).comm2(a1,a2,d) @ &m : M  res] = Pr[BestModule(A).comm3(a1,a2,d) @ &m : M  res])
 /\ (forall M a1 a2, Pr[BestModule(A).comm3(a1,a2,D (glob A){m}) @ &m : M  res] = Pr[BestModule(A).comm4(a1,a2) @ &m : M  res]).
proof. elim bestLemma. move => D Dprop.
exists D.
split. move => M a1 a2. 
byequiv.
proc.  
call (_:true). call (_:true). call (_:true).
call Dprop. skip. progress. smt. smt. 
split. move => M a1 a2 d. 
byequiv (_: exists ga, ga = (glob A){1} /\ (={glob A, arg}) ==> _).
elim (rewindable_A_plus A RewProp). progress. 
proc. elim*. move => ga.
inline*.
sp. 
wp. 
swap {1} [1..2] 3.
wp.  rnd.  wp.
call (_:true). call (_:true). call (_:true).
skip. progress.   smt. auto.
move => M a1 a2.
byequiv (_: exists ga, ga = (glob A){1} /\ ={a1,a2, glob A} /\ arg.`3{1} = D (glob A){1}  ==> _). proc. 
elim*. move => ga.
seq 3 3 : (={r2, a1, glob A} /\ ga = (glob A){2} /\ d{1} = D (glob A){1}).
elim (rewindable_A_plus A RewProp). progress. 
call {1} (H3 ga). call {2} (H3 ga). call (_:true).
call {1} (H0 ga). call {2} (H0 ga). skip. smt.
symmetry. call Dprop.
skip. progress.  smt. smt. 
qed.


local lemma bestLemma3 &m : forall M a1 a2,
   Pr[CommNoInit(A).ex1ex2(a1,a2) @ &m : M res] =
   Pr[BestModule(A).comm1(a1,a2) @ &m : M res].
proof. move => M a1 a2.
byequiv (_: exists ga, ga = (glob A){1} /\ ={glob A, arg} ==> _). proc.
elim (rewindable_A_plus A RewProp). progress. elim*.
move => ga.
call {2} (H3 ga).
call (_:true).
call {1} (H3 ga).
call {2} (H0 ga).
inline*.  wp. 
call {2} (H3 ga).
call (_:true).
call {2} (H0 ga).
call {1} (H0 ga). wp. skip.  
progress.  smt. 
auto. 
qed.


local lemma bestLemma4 &m : forall M a1 a2,
   Pr[BestModule(A).comm4(a1,a2) @ &m : M res] =
   Pr[CommNoInit(A).ex2ex1(a1,a2) @ &m : M res].
move => M a1 a2.
byequiv (_: exists ga, ga = (glob A){1} /\ ={glob A, arg} ==> _). proc.
elim (rewindable_A_plus A RewProp). progress. elim*.
move => ga. inline*.  wp.
call {1} (H3 ga).
call (_:true).
call {1} (H0 ga).
wp. 
call {1} (H3 ga).
call {2} (H3 ga).
call (_:true).
call {1} (H0 ga). 
call {2} (H0 ga). 
skip.  
progress.  smt.  auto.
qed.


lemma rew_comm_law_simple : forall &m M i1 i2,
   Pr[CommNoInit(A).ex1ex2(i1,i2) @ &m : M res] 
 = Pr[CommNoInit(A).ex2ex1(i1,i2) @ &m : M res].
proof. move => &m M a1 a2. 
elim (bestLemma1 &m).
progress. rewrite bestLemma3. rewrite - bestLemma4.
rewrite H H0 H1. auto.
qed.


end section.
end RewCommNI.
