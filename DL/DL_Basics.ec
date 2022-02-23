pragma Goals:printall.
require import AllCore Distr DInterval.
require import AllCore DBool Bool List Int IntDiv.

require ZK_General.


type dl_prob = (int * int * int).
type dl_wit  = int.
type dl_com = int.
type dl_resp = int.

op IsPrime : int -> bool.

op VerifyZK : dl_prob -> dl_com -> dl_resp -> bool.
op VerifyWit : dl_prob -> dl_wit -> bool.
op ExtractWit : dl_prob -> dl_com -> dl_resp -> dl_resp -> dl_wit option.



axiom dl_prop1 (p a x : int) : IsPrime p => a ^ x %% p = a ^ (x %% (p - 1)) %% p. 


clone import ZK_General as ZK_defs with type prob  = dl_prob,
                                        type wit   = dl_wit,
                                        type chal  = bool,
                                        type com   = dl_com,
                                        type resp  = dl_resp.


(* honest prover  *)
module DL_HP : Prover = {

 var pa : dl_prob
 var wa : dl_wit
 var r : int

 proc commit(p : dl_prob, w : dl_wit) : dl_com = {  
    var h : int; 
    (pa, wa) <- (p,w);
    r <$  [0..p.`1 - 2];
    return (p.`2) ^ r %% p.`1;
 }

 proc response(b : bool) : int = {
    return (if b then r + wa else r) %% (pa.`1 - 1);
 } 

 proc getState() : sbits = {
   return witness;
 }

 proc setState(s : sbits) : unit = {
 }
 
}.



(* honest verifier *)
module DL_HV : Verifier = {
  var pa : dl_prob
  var ca : dl_com
  var b : bool

  proc challenge(p : dl_prob, c : dl_com) : bool = {
   (pa, ca) <- (p,c);
   b <$ {0,1};
   return b;
  }

  proc verify(c : dl_com, r : dl_resp) : bool = {
   
    return pa.`2 ^ r %% pa.`1 = ca * (if b then pa.`3 else 1) %% pa.`1;
 } 

 proc summitup(c : dl_com, r : dl_resp) : sbits = {
   return witness;
 }

 proc getState() : sbits = {
   return witness;
 }

 proc setState(s : sbits) : unit = {
 }
}.


lemma dl_complete_h p (A : int) B (x : int) : 
  IsPrime p /\ A^x %% p = B %% p /\ 0 <= x
   => hoare [ Correct(DL_HP,DL_HV).main : arg = ((p,A,B),x) ==> res ]. 
move => [qra [invrtbl wpos]].
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.
case (b1 = false). progress.
have ->: A ^ r1 %% p %% p = A ^ r1 %% p. smt (modz_mod).
smt (dl_prop1 modz_mod).
move => bf.
have bf1 : b1 = true. smt.
clear bf. rewrite bf1. simplify. 
rewrite  - dl_prop1. auto.
have ->: A ^ (r1 + w{hr})
 = A ^ r1 * A^ w{hr}. apply exprD_nneg. smt. smt.   
smt (modz_mod modzMml modzMmr modzMm).
qed.   


require RewWithInit.
clone import RewWithInit.RWI as MRWI with type sbits <- sbits,
                                          type iat   <- dl_prob,
                                          type irt   <- dl_prob * dl_com,
                                          type rrt   <- (bool * bool).


module MyInit(P : Prover) : RW.Initializer = {
  proc init(i : dl_prob)   = {
    var c : dl_com;
    c <- P.commit(i,witness);
    return (i,c);
  }
}.                                  


module MyRewRun(P : Prover) : RW.RewRun = {

  proc run(pa : dl_prob, ca : dl_com) = {
    var b : bool;
    var r : dl_resp;
    b <$ {0,1};

    r <- P.response(b);
    
    return (b, pa.`2 ^ r %% pa.`1 = ca * (if b then pa.`3 else 1) %% pa.`1);
  }

  proc setState(s : sbits) = {
    P.setState(s);
  }
  
  proc getState() : sbits = {
    return witness;
  }
}.


section.
declare module P : Prover.

lemma step1 &m : forall (i : dl_prob),
        Pr[QQ(MyRewRun(P), MyInit(P)).main_run(i) @ &m : snd (snd res)] ^ 2 <=
        Pr[QQ(MyRewRun(P), MyInit(P)).main(i) @ &m : snd (snd res.`1) /\ snd (snd res.`2)].
proof. move => i.
apply (rew_with_init (MyRewRun(P)) (MyInit(P)) _ _ _ _ _ &m (fun x => snd (snd x ))).
sim. sim. admit. admit. admit.
qed.


lemma step2 &m : forall (i : dl_prob),
    Pr[QQ(MyRewRun(P), MyInit(P)).main_run(i) @ &m : snd (snd res)] ^ 2 <=
    Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
      @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
         /\ res.`1.`2.`1 = res.`2.`2.`1 ]
   + Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
      @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
         /\ res.`1.`2.`1 <> res.`2.`2.`1].
proof. move => i.
have <-: Pr[QQ(MyRewRun(P), MyInit(P)).main(i) @ &m :
             (snd (snd res.`1) /\ snd (snd res.`2)) ] =
   Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
      @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
         /\ res.`1.`2.`1 = res.`2.`2.`1 ]
   + Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
      @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
         /\ res.`1.`2.`1 <> res.`2.`2.`1].
rewrite Pr[mu_split res.`1.`2.`1 = res.`2.`2.`1]. 
auto.
apply step1.
qed.

lemma step3 &m : forall (i : dl_prob),
 Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
     @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
        /\ res.`1.`2.`1 <> res.`2.`2.`1] >= 
 Pr[QQ(MyRewRun(P), MyInit(P)).main_run(i) @ &m : snd (snd res)] ^ 2
  -     Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
      @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
         /\ res.`1.`2.`1 = res.`2.`2.`1 ].
smt (step2).
qed.  


lemma qwe &m i :
 Pr[QQ(MyRewRun(P), MyInit(P)).main(i) @ &m : res.`1.`2.`1 = res.`2.`2.`1 ]
 = 1%r/2%r.
proof. byphoare. proc.
inline*. simplify. wp. simplify.
swap 6 -5. swap 12 -11.
seq 2 : (b0 = b) (1%r/2%r) 1%r 1%r 0%r.
admitted.


lemma step4 &m : forall (i : dl_prob),
 Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
     @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
        /\ res.`1.`2.`1 <> res.`2.`2.`1] >= 
 Pr[QQ(MyRewRun(P), MyInit(P)).main_run(i) @ &m : snd (snd res)] ^ 2
    - 1%r/2%r.
move => i.
have f : Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
      @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
         /\ res.`1.`2.`1 = res.`2.`2.`1 ] <= 1%r/2%r.
rewrite - (qwe &m i).
rewrite Pr[mu_sub]. progress. auto.
smt (step3).
qed.


(*
TODO:
1/ embed verification into  (instead of just bools)

 Pr[QQ(MyRewRun(P), MyInit(P)).main(i)
     @ &m : (snd (snd res.`1) /\ snd (snd res.`2))
        /\ res.`1.`2.`1 <> res.`2.`2.`1] 

2/ show that if verification  succeeds and chals are different
then  the above prob is equal to same probability but with
witness extraction

3/ assuming that single run succeeds with prob > sqrt(1/2) we
have extraction prob > 0.

4/ prove that there exists "p" equal to that prob and p > 0

5/ apply "whp_cap_fin" to show the probability of extraction
on i-th iteration.

======



*)





(*

Define module KE which rewinds the prover
and challenges it with both bits then do the followig analysis

Pr[ Run2 ] >= Pr[ Run1 ]^2
<=>
Pr[ Run2: c = c' ] + Pr[ Run2: c <> c' ] >= Pr[ Run1 ]^2
<=>
Pr[ Run2: c <> c' ] >= Pr[ Run1 ]^2 - Pr[ Run2: c = c' ]
  {Pr[ Run2: c = c' ] <= 1/2}
<=>
Pr[ Run2: c <> c' ] >= Pr[ Run1 ]^2 - 1/2

Hence,

 Pr[ Run1 ] <= sqrt (Pr[ Run2: c <> c' ] + 1/2) (~ 0.7)

Assuming that Pr[ Run2: c <> c' ] is negligible we can iterate Run1
to get arbitrary low probability.

*)
