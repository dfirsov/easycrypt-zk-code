require import AllCore DBool Bool List Distr Aux.
require import CyclicGroup.

import FDistr.

require import Generic_Defs_thy.


type dl_prob = group * group.
type dl_wit  = t.
type dl_com = group.
type dl_resp = t.


(* Honest Vrifier  *)
op dl_verify (p : dl_prob) (c : dl_com) (b : bool) (r : dl_resp) : bool =
 if b then p.`1 ^ r = p.`2 * c
  else p.`1 ^ r = c.


op verify_transcript = fun p (x : dl_com * bool * dl_resp) => dl_verify p x.`1 x.`2 x.`3.


op IsDL (p : dl_prob) (w : dl_wit) : bool = p.`1 ^ w = p.`2.


op soundness_relation    = IsDL.
op completeness_relation = IsDL.
op zk_relation           = IsDL.


clone include ZKProtocol with 
  type statement       <- dl_prob,
  type commitment      <- dl_com,  
  type witness         <- dl_wit,
  type response        <- dl_resp,
  type challenge       <- bool,
  op challenge_set     <-  (false :: true :: []),
  op verify_transcript <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.


module HonestProver : HonestProver = {
 var pa : dl_prob
 var wa : dl_wit
 var r : t

 proc commitment(p : dl_prob, w : dl_wit) : dl_com = {  
    (pa, wa) <- (p,w);
    r <$  dt;
    return (p.`1) ^ r;
 }

 proc response(b : bool) : dl_resp = {
    return (if b then r + wa else r);
 }  
}.


