pragma Goals:printall.
require import AllCore DBool Bool List Distr AuxResults.

(* All generic definitions associated with sigma protocols.  *)
require  GenericSigmaProtocol.


(* standard library formalization of zmod fields, rings, etc.  *)
(* for FiatShamir we must use ring since in ZModField QR is efficiently computable *)
require import ZModP.           
clone import ZModRing as ZMR.         

(* more intuitive synonym *)
abbrev invertible = unit.       

(* uniform distribution of invertible elements, could be constructed from DZmodP   *)
op zmod_distr : zmod distr.
axiom d_prop0 : is_uniform zmod_distr.
axiom d_prop3 (r : zmod) :  invertible r => r \in zmod_distr.
axiom d_prop4 r : r \in zmod_distr => invertible r.
axiom d_prop5 : weight zmod_distr = 1%r.


(* synonyms for readability *)
type qr_stat = zmod.            (* statement *)
type qr_wit  = zmod.            (* witness *)
type qr_com  = zmod.            (* commitment *)
type qr_resp = zmod.            (* response *)

(* defining relations for completeness, soundness, and ZK *)
op completeness_relation (s:qr_stat) (w:qr_wit) = s = (w * w) /\ invertible s.
op soundness_relation = completeness_relation.
op zk_relation = completeness_relation.

(* Schnorr's verification function  *)
op verify_transcript (p: qr_stat) (x : qr_com * bool * qr_resp) : bool =
 let c = x.`1 in 
 let b = x.`2 in
 let r = x.`3 in   
 unit c /\ unit p /\ if b then c * p = r * r 
                          else c = r * r.

(* cloning the generic definition with specific FiatShamir details  *)
clone export GenericSigmaProtocol as FiatShamirProtocol with 
  type statement       <- qr_stat,
  type commitment      <- qr_com,  
  type witness         <- qr_wit,
  type response        <- qr_resp,
  type challenge       <- bool,
  op challenge_set     <=  (false :: true :: []),
  op verify_transcript <- verify_transcript,
  op soundness_relation    <- soundness_relation,
  op completeness_relation <- completeness_relation,
  op zk_relation           <- zk_relation.


(* standard implementation of Honest Prover *)
module HP : HonestProver = {
  var r, y, w : zmod

  proc commitment(Ny1 : qr_stat, w1 : qr_wit) : zmod = {  
    (y,w) <- (Ny1, w1);
    r <$ zmod_distr;
    return r * r;
  }

  proc response(b : bool) : qr_resp = {
    return r * (if b then w else one);
 } 
}.

(* Honest Verifier is derived automatically from "challenge_set" and "verify_transcript" *)
print HV.
