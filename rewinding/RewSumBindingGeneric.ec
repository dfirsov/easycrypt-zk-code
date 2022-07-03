pragma Goals:printall.
require import AllCore DBool.
require import Distr.
require import List.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.
require import RandomFacts.

require RewBasics.
theory RSBA.


type sbits, irt, rrt,iat.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.


clone import RewBasics as RW with type sbits <- sbits,
                                  type rrt <- rrt,
                                  type irt <- irt,
                                  type iat <- iat,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.


require RewWithInit.
clone import RewWithInit.RWI as RWAW with type sbits <- sbits,
                                         type iat   <- iat,
                                         type irt   <- irt,
                                         type rrt <- rrt,
                                         op pair_sbits <- pair_sbits,
                                         op unpair <- unpair.


require RewCommutes.
clone import RewCommutes.SpecRewCommutes as SRC with type rt1 <- rrt,
                                                     type rt2 <- rrt,
                                                     type iat <- iat,
                                                     type sbits <- sbits,
                                                     type irt <- irt,
                                                     type rrt <- rrt,
                                                     op pair_sbits <- pair_sbits,
                                                     op unpair <- unpair.

require RewSumBindingAux.
clone import RewSumBindingAux.RSBH as RSBH with type sbits <- sbits,
                                                    type rrt <- rrt,
                                                    type irt <- irt,
                                                    type iat <- iat,
                                                    op pair_sbits <- pair_sbits,
                                                    op unpair <- unpair.


section.
declare module A <: RewRunExec1Exec2.
declare module B <: Initializer.


axiom Afl : islossless A.ex1.
axiom Agl : islossless A.ex2.
axiom Bin : islossless B.init.

(* due to EC restrictions (bug) these are not provable and not reduciable to one another  *)
axiom Bsens    : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={glob A, res} ].
axiom Bsens'   : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={glob A, glob B, res} ].
axiom Bsens''  : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={glob A} ]. 
axiom Bsens''' : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={res, glob A} ]. 


axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

  
local lemma Ass : islossless A.setState.
proof. elim RewProp. progress. qed.


local lemma fact1 &m P i : Pr[ SB(A,B).main(i) @ &m : P res.`1 /\ P res.`2 ] >= Pr[ SB(A,B).main_run(i) @ &m : P res ]^2.
have : forall &m,
      Pr[QQ(SBB(A), B).main_run(i) @ &m : (fun (x : irt * rrt) => P x.`2) res] ^ 2 <=
      Pr[QQ(SBB(A), B).main(i) @ &m : (fun (x : irt * rrt) => P x.`2) res.`1 /\ (fun (x : irt * rrt) => P x.`2)  res.`2 ].
move => &m0.
apply (rew_with_init (SBB(A)) B).  
elim (rewindable_A A RewProp). move => fA [s1 [s2 [s3]]] s4. simplify. (* apply Bsens''. *)
simplify.
(* apply Bsens'''. *)
elim RewProp. progress.
(* exists f. progress. *)
(* rewrite - (H0 &m1). byequiv. proc*.  inline*. wp. call (_:true). *)
(*       skip. progress. auto. auto. *)
(* rewrite -  (H1 &m1 (f x) x). auto. *)
(* byequiv. proc*. inline*. sp.   call(_:true). skip. progress. auto. auto. *)
(* proc. call H2. skip. auto. *)
(* proc. seq 1 : (true). rnd. auto. rnd.  skip. auto. smt. *)
(* if. call Afl. skip. auto. call Agl. skip. auto.  hoare.  simplify. rnd. skip. auto.  auto. *)
(* apply Bin.       *)


simplify.
have q : Pr[QQ(SBB(A), B).main_run(i) @ &m : P res.`2] = Pr[SB(A, B).main_run(i) @ &m : P res].
        byequiv (_: (={i, glob A, glob B}) ==> _). proc.      
seq 1 1 : (={glob A} /\ r0{1} = ix{2}). call Bsens. skip. auto. 
inline*. wp.
conseq (_: exists ga, ga = (glob A){1} /\ ={glob A} /\ r0{1} = ix{2} ==> _). smt. sp. 
simplify. 
seq 1 1 : (i0{2} = ix{2} /\
  i0{1} = r0{1} /\
  exists (ga : (glob A)), ga = (glob A){1} /\ ={glob A} /\ r0{1} = ix{2} /\ ={x}).
rnd. skip. progress. smt.
if.  smt. call (_:true). skip. progress. call(_:true). skip. progress. auto. 
auto.  
rewrite - q. clear q.
have q : Pr[QQ(SBB(A), B).main(i) @ &m : P res.`1.`2 /\ P res.`2.`2] = Pr[SB(A, B).main(i) @ &m : P res.`1 /\ P res.`2].
byequiv (_: (={i, glob A, glob B}) ==> _). proc. simplify.
conseq (_: P r1{1} /\  P r2{1} <=>  (P r1{2} /\ P r2{2})). 
seq 1 1 : (={glob A} /\ r0{1} = ix{2}). call Bsens. skip. auto.
call (_: ={glob A, i} ==> ={res}). proc.
seq 1 1 : (={i,x, glob A}). rnd. skip. progress.
if. auto. call(_:true). skip. progress.
call (_:true). skip. progress.
inline {1} SBB(A).setState. call (_:true).
wp. 
call (_:(={glob A})).
seq 1 1 : (={i,x, glob A}). rnd. skip. progress.
if.  auto. call (_:true). skip. progress.
call (_:true). skip. progress.
inline {1} SBB(A).getState. wp. call (_:true). skip. progress. auto. auto.
rewrite - q. 
rewrite H3.

qed.


local lemma fact3' P &m i : Pr[SB(A,B).main_run(i) @ &m : P res] = 1%r / 2%r * Pr[SB(A,B).main_1(i) @ &m : P res] 
                                                                 + 1%r / 2%r * Pr[SB(A,B).main_2(i) @ &m : P res].
apply (fact3 A B). (* apply Afl. apply Agl. apply Ass. apply Bsens. *)
qed.


local lemma fact4 &m P i : Pr[SB(A,B).main_11(i) @ &m : P res.`1 /\ P res.`2] <= Pr[SB(A,B).main_1(i) @ &m : P res].
byequiv (_: (={i, glob A, glob B}) ==> _). proc. 
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 2 1 : (r1{1} = r{2}). 
elim (rewindable_A A RewProp). move => fA [s1 [s2 [s3]]] s4.
call (_:true). conseq (_: exists ga, ga = (glob A){1} /\ ={glob A, ix} ==> _). smt.
elim*. move => ga.
call {1} (s2 ga). skip. smt.
call {1} (_:true ==> true). apply Afl.
call {1} (_:true ==> true). apply Ass.
skip. auto. auto. auto.
qed.


local lemma fact5 &m P i : Pr[SB(A,B).main_22(i) @ &m : P res.`1 /\ P res.`2] <= Pr[SB(A,B).main_2(i) @ &m : P res].
byequiv (_: (={i,glob A, glob B}) ==> _). proc. 
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 2 1 : (r1{1} = r{2}). 
elim (rewindable_A A RewProp). move => fA [s1 [s2 [s3]]] s4.
call (_:true). conseq (_: exists ga, ga = (glob A){1} /\ ={glob A, ix} ==> _). smt.
elim*. move => ga.
call {1} (s2 ga). skip. smt.
call {1} (_:true ==> true). apply Agl.
call {1} (_:true ==> true). apply Ass.
skip. auto. auto. auto.
qed.


local lemma deriv &m P i : 
   1%r/2%r * Pr[ SB(A,B).main_12(i) @ &m : P res.`1 /\ P res.`2 ] 
   + 1%r/2%r * Pr[ SB(A,B).main_21(i) @ &m : P res.`1 /\ P res.`2 ]
    >= 2%r * Pr[ SB(A,B).main_run(i) @ &m :  P res ] *  (Pr[ SB(A,B).main_run(i) @ &m :  P res ] - (1%r/2%r)).
proof. 
pose V_rnd_rnd := Pr[SB(A,B).main(i) @ &m : P res.`1 /\ P res.`2].
pose V_rnd := Pr[SB(A,B).main_run(i) @ &m : P res ].
pose V_12  := Pr[SB(A,B).main_12(i) @ &m : P res.`1 /\ P res.`2].
pose V_21  := Pr[SB(A,B).main_21(i) @ &m : P res.`1 /\ P res.`2].
pose V_22  := Pr[SB(A,B).main_22(i) @ &m : P res.`1 /\ P res.`2].
pose V_11  := Pr[SB(A,B).main_11(i) @ &m : P res.`1 /\ P res.`2].
pose V_1  := Pr[SB(A,B).main_1(i) @ &m : P res].
pose V_2  := Pr[SB(A,B).main_2(i) @ &m : P res].
have tr1 : 
   1%r/2%r * V_12 
 + 1%r/2%r * V_21
 = 2%r * (1%r/4%r * V_12 + 1%r/4%r * V_21 + 1%r/4%r * V_11 + 1%r/4%r * V_22
   - (1%r/4%r * V_11 + 1%r/4%r * V_22)).
smt.
rewrite tr1. clear tr1.
rewrite - (fact2  A B). (* apply Afl.  apply Agl. apply Ass. apply Bsens. *)
have se : Pr[SB(A,B).main(i) @ &m : P res.`1 /\ P res.`2 ] = V_rnd_rnd. reflexivity.
rewrite se. clear se.
have v_1_11 : V_11 <= V_1. apply fact4.
have v_2_22 : V_22 <= V_2. apply fact5.
have ntg :
  2%r * (V_rnd ^ 2 - 1%r / 2%r * V_rnd) <= 2%r * (V_rnd_rnd - (1%r / 4%r * V_1 + 1%r / 4%r * V_2)).
have tr3 : (1%r / 4%r * V_1 + 1%r / 4%r * V_2) = (1%r/2%r * ((1%r / 2%r * V_1 + 1%r / 2%r * V_2))).
smt. rewrite tr3.
have tr4 : V_rnd = (1%r / 2%r * V_1 + 1%r / 2%r * V_2). 
apply fact3'.
rewrite - tr4.
have lk : V_rnd ^ 2 <= V_rnd_rnd . apply fact1.
smt. 
smt.
qed.


local lemma fin_deriv' &m P i : 
  Pr[ SB(A,B).main_1(i) @ &m : P res ] + Pr[ SB(A,B).main_2(i) @ &m : P res ]
   <= 1%r +  Pr[ SB(A,B).main_12(i) @ &m : P res.`1 /\ P res.`2 ] + Pr[ SB(A,B).main_21(i) @ &m : P res.`1 /\ P res.`2 ].
case (Pr[ SB(A,B).main_run(i) @ &m :  P res ] <= 1%r/2%r).
move => ass1.   
have s1 : 1%r/2%r * Pr[ SB(A,B).main_1(i) @ &m :  P res ] 
         + 1%r/2%r * Pr[ SB(A,B).main_2(i) @ &m :  P res ] <= 1%r/2%r.
rewrite - fact3'. apply ass1.
smt.
move => pr_reln.
have pr_rel : Pr[SB(A,B).main_run(i) @ &m : P res] > 1%r/2%r. smt. clear pr_reln.
have fr_ab : 1%r/2%r * Pr[ SB(A,B).main_12(i) @ &m : P res.`1 /\ P res.`2 ] 
           + 1%r/2%r * Pr[ SB(A,B).main_21(i) @ &m : P res.`1 /\ P res.`2 ]
   >= 2%r * Pr[ SB(A,B).main_run(i) @ &m :  P res ] *  (Pr[ SB(A,B).main_run(i) @ &m :  P res ] - (1%r/2%r)). apply deriv.
have : 1%r/2%r * Pr[ SB(A,B).main_12(i) @ &m : P res.`1 /\ P res.`2 ] + 1%r/2%r * Pr[ SB(A,B).main_21(i) @ &m : P res.`1 /\ P res.`2 ]
   >= (Pr[ SB(A,B).main_run(i) @ &m :  P res ] - (1%r/2%r)).  
smt.
rewrite (fact3').
move => strfr_ab.
have qqq : Pr[SB(A,B).main_1(i) @ &m : P res] +
           Pr[SB(A,B).main_2(i) @ &m : P res] - 1%r <=
           Pr[SB(A,B).main_12(i) @ &m : P res.`1 /\ P res.`2] +
           Pr[SB(A,B).main_21(i) @ &m : P res.`1 /\ P res.`2].
smt.
smt.
qed.


lemma sum_binding_generic : forall &m M i,
  Pr[ SB(A,B).main_1(i) @ &m : M res ] + Pr[ SB(A,B).main_2(i) @ &m : M res ]
   <= 1%r +  2%r * Pr[ SB(A,B).main_12(i) @ &m : M res.`1 /\ M res.`2 ].
proof. move => &m P i.
have d : 1%r + 2%r * Pr[SB(A, B).main_12(i) @ &m : P res.`1 /\ P res.`2]
          = 1%r + Pr[SB(A, B).main_12(i) @ &m : P res.`1 /\ P res.`2] + Pr[SB(A, B).main_21(i) @ &m : P res.`1 /\ P res.`2].
    have q : Pr[ SB(A,B).main_12(i) @ &m : P res.`1 /\ P res.`2 ] 
         = Pr[ SB(A,B).main_21(i) @ &m : P res.`1 /\ P res.`2 ]. 
  pose M := fun (x : rrt * rrt) => P x.`1 /\ P x.`2.
    have q1 : Pr[ SpecRewComm(A,B).iex1ex2(i) @ &m : M res.`2 ] = Pr[SB(A, B).main_12(i) @ &m : P res.`1 /\ P res.`2 ].
    byequiv (_: (={arg, glob A, glob B}) ==> _ ). proc.  
    seq 1 1 : (={glob A} /\ r0{1} = ix{2}). call Bsens. skip. auto.
    call(_:true). call (_:true). call(_:true). call(_:true). skip. progress. smt. smt.  smt. smt. auto. 
    auto.
    rewrite - q1. clear q1.
    have q2 : Pr[ SpecRewComm(A,B).iex2ex1(i) @ &m : M res.`2 ] = Pr[SB(A, B).main_21(i) @ &m : P res.`1 /\ P res.`2 ].
    byequiv (_: (={arg,glob A, glob B}) ==> _ ). proc.  
    seq 1 1 : (={glob A} /\ r0{1} = ix{2}). call Bsens. skip. auto.
    call(_:true). call (_:true). call(_:true). call(_:true). skip. progress. smt. smt.  smt. smt. auto. 
    auto.
    rewrite - q2. clear q2.
    rewrite  (rew_comm_law A B (* Bsens' *) (* RewProp *) &m (fun (x : irt * (rrt * rrt)) => M x.`2)).  auto.
  rewrite q. smt.
rewrite d.
 apply (fin_deriv' &m P).
qed.


end section.
end RSBA.
