require import AllCore DBool Bool List Distr Aux Finite.
require import CyclicGroup.
import FDistr.

require  GenericSigmaProtocol.


type dl_prob = group.
type dl_wit  = t.
type dl_com = group.
type dl_resp = t.
type dl_chal = t.


(* Honest Vrifier  *)
op dl_verify (p : dl_prob) (c : dl_com) (b : dl_chal) (r : dl_resp) : bool =
  g ^ r = (p ^ b) * c.


op verify_transcript = fun p (x : dl_com * dl_chal * dl_resp) => dl_verify p x.`1 x.`2 x.`3.


op IsDL (p : dl_prob) (w : dl_wit) : bool = g ^ w = p.


op soundness_relation    = IsDL.
op completeness_relation = IsDL.
op zk_relation           = IsDL.


clone export GenericSigmaProtocol as FiatShamir with 
  type statement       <- dl_prob,
  type commitment      <- dl_com,  
  type witness         <- dl_wit,
  type response        <- dl_resp,
  type challenge       <- dl_chal,
  op challenge_set     <=  to_seq (support dt),
  op verify_transcript <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.


module HP : HonestProver = {
 var pa : dl_prob
 var wa : dl_wit
 var r : t

 proc commitment(p : dl_prob, w : dl_wit) : dl_com = {  
    (pa, wa) <- (p,w);
    r <$  dt;
    return g ^ r;
 }

 proc response(b : dl_chal) : dl_resp = {
    return r + b * wa;
 }  
}.


