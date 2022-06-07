pragma Goals:printall.
require import AllCore DBool Bool List Distr Aux.

require import GenericZK.


require import ZModP.
clone include ZModRing.         (* must use ring since in ZModField QR is efficiently computable *)

type qr_prob = zmod.
type qr_wit  = zmod.
type qr_com  = zmod.
type qr_resp = zmod.


op IsSqRoot (Ny : qr_prob) (w : qr_wit) = Ny  = (w * w).
op IsQR (Ny : qr_prob) = exists w, IsSqRoot Ny w /\ unit Ny.


op ZNS_dist :  (zmod * zmod) distr.

axiom d_prop0  : is_uniform (ZNS_dist).
axiom d_prop1 r rr :  (r, rr) \in ZNS_dist => r * r = rr.
axiom d_prop3 (r rr : zmod) :  r * r = rr => (r, rr) \in ZNS_dist.
axiom d_prop4  r rr :  (r, rr) \in ZNS_dist => unit rr.
axiom d_prop5 : weight (ZNS_dist) = 1%r.


axiom qr_prop1 (x : zmod) : unit  x => x * (inv x)  = one.
axiom qr_prop2 (x y w : zmod) : unit y => IsSqRoot (y) w => unit w.
axiom qr_prop3 (w : zmod) : unit  w => inv  (w * w) = (inv w) * (inv w).
axiom qr_prop5 (x y r : zmod) : IsQR x => unit x => !IsQR y => unit y => x * y  <> r * r.

axiom qr_prop11 (x : zmod) : unit x => (inv x) * x = one.


(* Honest Vrifier  *)
op qr_verify (p : qr_prob) (c : qr_com) (b : bool) (r : qr_resp) : bool =
  if b then unit c /\ unit p /\ c * p = r * r 
  else unit c /\ c = r * r.

op verify_transcript = fun p (x : qr_com * bool * qr_resp) => qr_verify p x.`1 x.`2 x.`3.
op soundness_relation    = fun Ny w => IsSqRoot Ny w.
op completeness_relation = fun Ny w => IsSqRoot Ny w /\ unit Ny.
op zk_relation           = fun Ny w => IsSqRoot Ny w /\ unit Ny.

clone include ZKProtocol with 
  type statement       <- qr_prob,
  type commitment      <- qr_com,  
  type witness         <- qr_wit,
  type response        <- qr_resp,
  type challenge       <- bool,
  op challenge_set     <-  (false :: true :: []),
  op verify_transcript <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.


(* Honest Prover  *)
module HonestProver : HonestProver = {
  var r,rr, y, w : zmod

  proc commitment(Ny1 : qr_prob, w1 : qr_wit) : zmod = {  
    (y,w) <- (Ny1, w1);
    (r,rr) <$ ZNS_dist;
    return rr;
  }

  proc response(b : bool) : qr_resp = {
    return r * (if b then w else one);
 } 
}.
