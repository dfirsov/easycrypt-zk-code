require import AllCore Distr DInterval.
require import AllCore DBool Bool List Int IntDiv.

require ZK_General.


type dl_prob = (int * int * int).
type dl_wit  = int.
type dl_com = int.
type dl_resp = int.

op IsPrime : int -> bool.


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
