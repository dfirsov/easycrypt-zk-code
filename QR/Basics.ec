pragma Goals:printall.
require import AllCore DBool Bool List Distr Aux.

require  GenericSigmaProtocol.


require import ZModP.
clone include ZModRing.         (* must use ring since in ZModField QR is efficiently computable *)
(* import DZmodP. *)

abbrev invertible = unit.           (* more intuitive synonym *)

type qr_prob = zmod.
type qr_wit  = zmod.
type qr_com  = zmod.
type qr_resp = zmod.


op ZNS_dist :  (zmod * zmod) distr.

axiom d_prop0  : is_uniform ZNS_dist.
axiom d_prop1 r rr :  (r, rr) \in ZNS_dist => r * r = rr.
axiom d_prop3 (r rr : zmod) :  r * r = rr => (r, rr) \in ZNS_dist.
axiom d_prop4  r rr :  (r, rr) \in ZNS_dist => unit rr.
axiom d_prop5 : weight (ZNS_dist) = 1%r.



op completeness_relation = fun Ny w => Ny = (w * w) /\ invertible Ny.
op soundness_relation    = fun Ny w => Ny = (w * w) /\ invertible Ny.
op zk_relation           = fun Ny w => Ny = (w * w) /\ invertible Ny.


(* Honest Vrifier  *)
op qr_verify (p : qr_prob) (c : qr_com) (b : bool) (r : qr_resp) : bool =
  if b then unit c /\ unit p /\ c * p = r * r 
  else unit c /\ c = r * r.

op verify_transcript = fun p (x : qr_com * bool * qr_resp) => qr_verify p x.`1 x.`2 x.`3.

clone export GenericSigmaProtocol as FiatShamir with 
  type statement       <- qr_prob,
  type commitment      <- qr_com,  
  type witness         <- qr_wit,
  type response        <- qr_resp,
  type challenge       <- bool,
  op challenge_set     <=  (false :: true :: []),
  op verify_transcript <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.



lemma qr_prop1 (x : zmod) : unit x => x * (inv x)  = one. smt. qed.
lemma qr_prop2 (x y w : zmod) : unit y => y = w * w => unit w. smt. qed.
lemma qr_prop3 (w : zmod) : unit  w => inv (w * w) = (inv w) * (inv w). smt. qed.
lemma qr_prop11 (x : zmod) : unit x => (inv x) * x = one. smt. qed.
lemma qr_prop5 (x y r : zmod) : in_language completeness_relation x 
  => !in_language completeness_relation y => unit y => x * y  <> r * r.
progress.
elim H. progress. 
case (x * y = r * r). elim H.
move => H xinv.
pose w := witness.
rewrite  H. 
have iw : invertible witness.  smt.
move => eq.
have eq2 :  (inv w) * w * w * y = (inv w) * r * r. smt.
have eq3 :  w * y = (inv w) * r * r. smt.
clear eq2 eq.
have eq4 :  (inv w) * w * y = ((inv w) * r) * (inv w) * r. smt.
have eq5 :  y = ((inv w) * r) * ((inv w) * r). smt.
apply H0. exists (inv w * r). split.
apply eq5. auto.
auto.
qed.



(* Honest Prover  *)
module HP : HonestProver = {
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
