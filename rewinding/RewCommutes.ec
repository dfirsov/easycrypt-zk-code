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
require ReflectionComp.
require RewCommutesSimple.

theory GenRewCommutes.


type at1, at2, rt1, rt2.

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


module type GenRewEx1Ex2 = {
  proc getState() : sbits
  proc * setState(b : sbits) : unit 
  proc ex1(x1 : at1 * irt) : rt1
  proc ex2(x2 : at2 * irt) : rt2
}.


module ModComm(A : GenRewEx1Ex2, B : Initializer) = {

  proc ex2(i12 : at1 * at2,r0 : irt) = {
    var r1, r2,s;
    s <@ A.getState();
    r1 <@ A.ex1(i12.`1,r0);
    A.setState(s);
    r2 <@ A.ex2(i12.`2,r0);
    return (r1,r2);
  }

  proc ex1(i0 : iat) = {
    var r0;
    r0 <@ B.init(i0);
    return r0;
  }
}.

module ModComm'(A : GenRewEx1Ex2, B : Initializer) = {
  proc ex2(i12 : at1 * at2,r0 : irt) = {
    var r1, r2,s;
    s <@ A.getState();
    r2 <@ A.ex2(i12.`2,r0);
    A.setState(s);
    r1 <@ A.ex1(i12.`1,r0);
    return (r1,r2);
  }

  proc ex1(i0 : iat) = {
    var r0;
    r0 <@ B.init(i0);
    return r0;
  }
}.



section.
declare module A <: GenRewEx1Ex2.
declare module B <: Initializer.

declare axiom Bsens : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={glob A, glob B,res}  ].    

declare axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.


clone import ReflectionComp.ReflComp as RC with type at1 <- iat,
                                 type at2 <- at1 * at2,
                                 type rt1 <- irt,
                                 type rt2 <- rt1 * rt2.


clone import RewCommutesSimple.RewCommNI as RCNI with type at1 <- at1 * irt,
                                                      type at2 <- at2 * irt,
                                                      type rt1 <- rt1,
                                                      type rt2 <- rt2,
                                                      type sbits <- sbits,
                                                      type iat <- iat,
                                                      type irt <- irt,
                                                      op pair_sbits <- pair_sbits,
                                                      op unpair <- unpair.


local lemma reflectionComp1 : 
  exists (D : iat -> glob ModComm(A,B) -> (irt * glob ModComm(A,B)) distr), 
  exists (Q : at1 * at2 -> irt * glob ModComm(A,B) -> ((rt1 * rt2) * glob ModComm(A,B)) distr),
  (forall M i1 &m, mu (D i1 (glob ModComm(A,B)){m}) M 
     = Pr[ ModComm(A,B).ex1(i1) @ &m : M (res, glob ModComm(A,B))]) /\
  (forall M i2 r1 &m, mu (Q i2 (r1, glob ModComm(A,B)){m}) M 
     = Pr[ ModComm(A,B).ex2(i2, r1) @ &m :  M (res, glob ModComm(A,B))]) /\
  forall &m M i1 i2, 
   Pr[ RCR(ModComm(A,B)).main(i1,i2) 
     @ &m : M (res.`1, ((res.`2.`1, res.`2.`2), glob ModComm(A,B))) ] 
   = mu (dlet (D i1 (glob ModComm(A,B)){m}) (fun a => dmap (Q i2 a) (fun x => (a.`1, x)))) M.
proof. 
elim (reflectionComp_dmap (ModComm(A,B))).
progress.
exists D.
exists Q.
progress. rewrite (H0 (fun r => M )). auto. rewrite - H1.
rewrite Pr[mu_eq]. smt. auto.
qed.


local lemma reflectionComp2 : 
  exists (D : iat -> glob ModComm'(A,B) -> (irt * glob ModComm'(A,B)) distr), 
  exists (Q : at1 * at2 -> irt * glob ModComm'(A,B) 
                  -> ((rt1 * rt2) * glob ModComm'(A,B)) distr),
  (forall M i1 &m, mu (D i1 (glob ModComm'(A,B)){m}) M 
     = Pr[ ModComm'(A,B).ex1(i1) @ &m : M (res, glob ModComm'(A,B))]) /\
  (forall M i2 r1 &m, mu (Q i2 (r1, glob ModComm'(A,B)){m}) M 
     = Pr[ ModComm'(A,B).ex2(i2, r1) @ &m :  M (res, glob ModComm'(A,B))]) /\
  forall &m M i1 i2, Pr[ RCR(ModComm'(A,B)).main(i1,i2) 
                       @ &m : M (res.`1 , ((res.`2.`1, res.`2.`2), glob ModComm'(A,B))) ] 
     = mu (dlet (D i1 (glob ModComm'(A,B)){m}) (fun a => dmap (Q i2 a) (fun x => (a.`1, x)))) M.
proof. 
elim (reflectionComp_dmap (ModComm'(A,B))).
progress.
exists D. exists Q.
progress. rewrite (H0 (fun r => M )). auto. rewrite - H1. rewrite Pr[mu_eq]. smt. auto.
qed.


lemma reflectionComb : 
  forall &m M i1 i2, Pr[ RCR(ModComm'(A,B)).main(i1,i2) @ &m : M res ] 
  = Pr[ RCR(ModComm(A,B)).main(i1,i2) @ &m : M res ].
proof.  move => &m M.
pose M' := (fun (x :   irt * ((rt1 * rt2) * ((glob B) * (glob A)))) => M (x.`1, (x.`2.`1))).
elim reflectionComp1. 
elim reflectionComp2. 
progress. 
have e1 : Pr[RCR(ModComm'(A, B)).main(i1, i2) @ &m : M res] = 
     Pr[RCR(ModComm'(A, B)).main(i1, i2) @ &m : M (res.`1, (res.`2.`1, res.`2.`2))]. 
rewrite Pr[mu_eq]. smt. auto.
rewrite e1.
have e2 : Pr[RCR(ModComm(A, B)).main(i1, i2) @ &m : M res] = 
     Pr[RCR(ModComm(A, B)).main(i1, i2) @ &m : M (res.`1, (res.`2.`1, res.`2.`2))].
rewrite Pr[mu_eq]. smt. auto.
rewrite e2.
rewrite (H1 &m M').
rewrite (H4 &m M'  ).  
rewrite dlet_mu_main.
rewrite dlet_mu_main.
have : (fun (a : irt * ((glob B) * (glob A))) =>
     mu1 (D i1 ((glob B){m}, (glob A){m})) a *
     mu
       ((fun (a0 : irt * ((glob B) * (glob A))) =>
           dmap (Q i2 a0)
             (fun (x : (rt1 * rt2) * ((glob B) * (glob A))) => (a0.`1, x)))
          a) M')
  = (fun (a : irt * ((glob B) * (glob A))) =>
     mu1 (D0 i1 ((glob B){m}, (glob A){m})) a *
     mu
       ((fun (a0 : irt * ((glob B) * (glob A))) =>
           dmap (Q0 i2 a0)
             (fun (x : (rt1 * rt2) * ((glob B) * (glob A))) => (a0.`1, x)))
          a) M').
apply fun_ext. move => a.
simplify. rewrite H.
rewrite H2.
simplify pred1.
have jj : Pr[ModComm'(A,B).ex1(i1) @ &m : (res, ((glob B), (glob A))) = a]
 = Pr[ModComm'(A,B).ex1(i1) @ &m : (res, ((glob B), (glob A))) = a /\ exists &n, (glob B, glob A){n} = a.`2].
rewrite Pr[mu_eq]. smt.
auto. 
have yy : Pr[ModComm(A,B).ex1(i1) @ &m : (res, ((glob B), (glob A))) = a]
 = Pr[ModComm(A,B).ex1(i1) @ &m : (res, ((glob B), (glob A))) = a /\ exists &n, (glob B, glob A){n} = a.`2].
rewrite Pr[mu_eq]. smt.
auto.
case (! exists &n, (glob B, glob A){n} = a.`2).
simplify.
rewrite jj.
rewrite yy.
move => ff.
have eq : Pr[ModComm'(A,B).ex1(i1) @ &m :
   (res, ((glob B), (glob A))) = a /\
   exists &n, ((glob B){n}, (glob A){n}) = a.`2] = 0%r.
  have eq1 : Pr[ModComm'(A,B).ex1(i1) @ &m :
   (res, ((glob B), (glob A))) = a /\
   exists &n, ((glob B){n}, (glob A){n}) = a.`2] =  Pr[ModComm'(A,B).ex1(i1) @ &m : false ].
   rewrite Pr[mu_eq]. smt. auto.
   rewrite eq1. rewrite Pr[mu_false]. auto. rewrite eq. simplify. clear eq.
have eq : Pr[ModComm(A,B).ex1(i1) @ &m :
   (res, ((glob B), (glob A))) = a /\
   exists &n, ((glob B){n}, (glob A){n}) = a.`2] = 0%r.
  have eq1 : Pr[ModComm(A,B).ex1(i1) @ &m :
   (res, ((glob B), (glob A))) = a /\
   exists &n, ((glob B){n}, (glob A){n}) = a.`2] =  Pr[ModComm(A,B).ex1(i1) @ &m : false ].
   rewrite Pr[mu_eq]. smt. auto.
   rewrite eq1. rewrite Pr[mu_false]. auto. rewrite eq. simplify. clear eq.
auto. simplify. move => zzz.
elim zzz. move => &n np .
have aa :  a = (a.`1, a.`2). smt.
rewrite aa.
rewrite - np.
rewrite - dmeq. rewrite - dmeq.
rewrite  (H0 (fun (x : (rt1 * rt2) * ((glob B) * (glob A))) =>
     M' ((a.`1, ((glob B){n}, (glob A){n})).`1, x)) i2 a.`1).
rewrite  (H3 (fun (x : (rt1 * rt2) * ((glob B) * (glob A))) =>
     M' ((a.`1, ((glob B){n}, (glob A){n})).`1, x)) i2 a.`1).
have myeq1 : Pr[ModComm'(A,B).ex1(i1) @ &m :
   (res, ((glob B), (glob A))) = (a.`1, ((glob B){n}, (glob A){n}))] 
 = Pr[ModComm(A,B).ex1(i1) @ &m :
   (res, ((glob B), (glob A))) = (a.`1, ((glob B){n}, (glob A){n}))].
byequiv (_: (={arg, glob A, glob B}) ==> ={glob A, glob B,res}).
proc.  call Bsens. skip. progress. auto. smt. 
rewrite myeq1.
simplify.
have q : Pr[ModComm'(A,B).ex2(i2, a.`1) @ &n : M' (a.`1, (res, ((glob B), (glob A))))]
 =    Pr[CommNoInit(A).ex2ex1((i2.`1 , a.`1), (i2.`2 , a.`1)   ) @ &n : M (a.`1, res)].
  have trv : Pr[ModComm'(A,B).ex2(i2, a.`1) @ &n : M' (a.`1, (res, ((glob B), (glob A))))]
       = Pr[ModComm'(A,B).ex2(i2, a.`1) @ &n : M (a.`1, res)].
  rewrite Pr[mu_eq]. auto. auto.
  rewrite trv. clear trv.
  byequiv. proc. call (_:true). call (_:true). call (_:true). call(_:true).
  skip. progress. smt. auto. 
rewrite q. clear q.
have q : Pr[ModComm(A,B).ex2(i2, a.`1) @ &n : M' (a.`1, (res, ((glob B), (glob A))))]
 =    Pr[CommNoInit(A).ex1ex2((i2.`1, a.`1), (i2.`2 , a.`1)) @ &n : M (a.`1, res)].
  have trv : Pr[ModComm(A,B).ex2(i2, a.`1) @ &n : M' (a.`1, (res, ((glob B), (glob A))))]
       = Pr[ModComm(A,B).ex2(i2, a.`1) @ &n : M (a.`1, res) ].
  rewrite Pr[mu_eq]. auto. auto.
  rewrite trv. clear trv.
  byequiv. proc. call (_:true). call (_:true). call (_:true). call(_:true).
  skip. progress. smt. auto. 
rewrite q. clear q.
have q : Pr[CommNoInit(A).ex1ex2((i2.`1, a.`1), (i2.`2, a.`1)   ) @ &n : M (a.`1, res)] 
  = Pr[CommNoInit(A).ex2ex1((i2.`1, a.`1), (i2.`2, a.`1)) @ &n : M (a.`1, res)].
  have kk : i2 = (i2.`1, i2.`2). smt.
  rewrite kk.
 apply (rew_comm_law_simple A RewProp &n 
         (fun (x : rt1 * rt2) => M (a.`1, x)) 
                                   ((i2.`1, i2.`2).`1, a.`1) 
                                   ((i2.`1, i2.`2).`2, a.`1)).
rewrite q. auto.
move => qqq. rewrite qqq. auto.
qed.


end section.
end GenRewCommutes.


(* once the Bsens bug will be fixed we could remove that and finish GenRewCommutes with i1 i2 as for-all-quantified arguments for ex1 and ex2; right now, if ex1 and ex2 need forall-quantified arguments they must be included into i0:iat and tunneled through B.init *)

theory SpecRewCommutes.

type rt1, rt2.

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


clone import GenRewCommutes as GRC with type at1 <- unit,
                                        type at2 <- unit,
                                        type rt1 <- rt1,
                                        type rt2 <- rt2,
                                        type iat <- iat,
                                        type irt <- irt,
                                        type sbits <- sbits,
                                        op pair_sbits <- pair_sbits,
                                        op unpair <- unpair.



module type SpecRewEx1Ex2 = {
  proc getState() : sbits
  proc * setState(b : sbits) : unit 
  proc ex1(x1 : irt) : rt1
  proc ex2(x2 : irt) : rt2
}.


module SpecRewComm(A : SpecRewEx1Ex2, B : Initializer) = {
  proc iex1ex2(i0 : iat) = {
    var r0, r1, r2, s;
    r0 <@ B.init(i0);
    s <@ A.getState();
    r1 <@ A.ex1(r0);
    A.setState(s);
    r2 <@ A.ex2(r0);
    return (r0, (r1, r2));
  }

  proc iex2ex1(i0 : iat) = {
    var r0, r1, r2, s;
    r0 <@ B.init(i0);
    s <@ A.getState();
    r2 <@ A.ex2(r0);
    A.setState(s);
    r1 <@ A.ex1(r0);
    return (r0, (r1, r2));
  }
}.


section.
declare module A <: SpecRewEx1Ex2.
declare module B <: Initializer.


local module WA = {
  proc getState() : sbits = {
    var r;
    r <@ A.getState();
    return r;
  }
  proc setState(b : sbits) : unit  = {
    A.setState(b);
  }
  proc ex1(x1 : unit * irt) : rt1 = {
    var r;
    r <@ A.ex1(x1.`2);
    return r;
  }
  proc ex2(x2 : unit * irt) : rt2 = {
    var r;
    r <@ A.ex2(x2.`2);
    return r;
  }
}.


axiom Bsens : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={glob A, glob B,res}  ].


axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.


lemma rew_comm_law : 
  forall &m M i0, Pr[ SpecRewComm(A,B).iex1ex2(i0) @ &m : M res ] 
  = Pr[ SpecRewComm(A,B).iex2ex1(i0) @ &m : M res ].
proof.  move => &m M i0.
have eq : forall i2, Pr[SpecRewComm(A, B).iex1ex2(i0) @ &m : M res] =
   Pr[RC.RCR(ModComm(WA, B)).main(i0, i2) @ &m : M res].
move => i2. byequiv (_: ={glob A, glob B} /\ arg.`1{2} = arg{1} ==> _).
proc. inline*. sp.
seq 0 0 : (={glob A, glob B, i0}).
skip.  progress.
seq 1 1 : (={glob A, glob B, r0}). call Bsens. skip. progress. 
wp.  sp.
call (_:true). wp. call (_:true).  wp.  call (_:true). wp.  call (_:true). skip. progress.
smt. auto. 
rewrite (eq (tt, tt)). clear eq. 
have eq : forall i2, Pr[SpecRewComm(A, B).iex2ex1(i0) @ &m : M res] =
   Pr[RC.RCR(ModComm'(WA, B)).main(i0, i2) @ &m : M res].
move => i2. byequiv (_: ={glob A, glob B} /\ arg.`1{2} = arg{1} ==> _).
proc. inline*. sp.
seq 0 0 : (={glob A, glob B, i0}).
skip. progress.
seq 1 1 : (={glob A, glob B, r0}). call Bsens. skip. progress. 
wp.  sp.
call (_:true). wp. call (_:true). wp. call (_:true). wp. call (_:true). skip. progress.
smt. auto. 
rewrite (eq (tt, tt)). clear eq. 
rewrite (reflectionComb WA B).
simplify. apply Bsens. 
simplify.
elim (rewindable_A A RewProp). progress. 
     exists f. progress.  
byphoare (_: (glob A) = (glob A){m0} ==> _).   
     proc. call (H0 (glob A){m0}). skip. auto. auto. auto.
byphoare (_: arg = f x /\ (glob A) = (glob A){m0}  ==> _).      
proc. call (H1 x). skip. auto. progress.  auto.
proc. call H2. skip. auto. auto.
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. auto. *)
qed.


end section.
end SpecRewCommutes.
