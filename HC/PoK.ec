pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import Aux Permutation Basics.


clone import PoK.
clone import ComputationalPoK.







require Generic_KE.

clone import Generic_KE as GKE with type pt <- hc_prob,
                                    type auxt <- auxiliary_input,
                                    type irt <- hc_com,
                                    type ct <- bool,
                                    type rt <- hc_resp,
                                    op d <- {0,1},
                                    op allcs <- [false; true].


require import SpecialSoundness.

(* move to Generic_Defs?  *)
module HC_SpecialSoundnessAdversary(P : MaliciousProver) : SpecialSoundnessAdversary = {
  proc attack(p : hc_prob, aux : auxiliary_input) : transcript * transcript = {
    var i,c1,c2,r1,r2;
    i <@ P.commitment(p, aux);

    c1 <$ {0,1};
    r1 <@ P.response(c1);

    c2 <$ {0,1};
    r2 <@ P.response(c2);
    return ((i,c1,r1), (i,c2,r2));
  }
}.

module (Extractor : Extractor)(P : MaliciousProver) = {  
  module SA = HC_SpecialSoundnessAdversary(P)

  proc extract(p : hc_prob, aux : auxiliary_input) : hc_wit = {
    var i,j,c1,c2,r1,r2,t1,t2;
    
    (t1,t2) <@ SA.attack(p, aux);
    (i,c1,r1) <- t1;
    (j,c2,r2) <- t2;
    
    return my_extract p i r1 r2;
 }
}.

section.
declare module P : MaliciousProver.


op ss : hc_prob.
op auxx : auxiliary_input.

clone import SSB as SSB with op ss <- ss,
                             op auxx <- auxx.

local module A : Adv = {
  proc init (p : hc_prob, aux : auxiliary_input) : hc_com = {
    var i : hc_com;
    i <@ P.commitment(p,aux);
    return i;
 }

 proc run(hcm : hc_com, hcc: bool) : hc_resp = {
   var r;
   r <@ P.response(hcc);
   return r;
 }
}.


local lemma ex_a_eq &m p aux : 
 Pr[ InitRun2(A).run(p,aux) @ &m 
          : res.`1.`1 <> res.`2.`1  /\
  hc_verify p res.`1.`2.`2 res.`1.`1 res.`1.`2.`1  /\
  hc_verify p res.`2.`2.`2 res.`2.`1 res.`2.`2.`1  /\
  ! IsHC (p, special_soundness_extract p (res.`1.`2.`2, res.`1.`1, res.`1.`2.`1) 
                                         (res.`2.`2.`2, res.`2.`1, res.`2.`2.`1)) ] 
  = Pr[ HC_SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
             valid_transcript_pair p res.`1 res.`2 /\
              ! IsHC (p, special_soundness_extract p res.`1 res.`2)].
byequiv;auto.
proc. simplify.   
inline*. wp.  call (_:true).  wp.  rnd.  wp. call (_:true). wp.  rnd. 
wp.  call (_:true). wp. skip. progress;smt.
qed.



local lemma ex_a_eq2 &m  : 
  Pr[ HC_SpecialSoundnessAdversary(P).attack(ss, auxx) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
              ! IsHC (ss, special_soundness_extract ss res.`1 res.`2)]
 <= Pr[BindingExperiment(SpecialSoundnessBinder(HC_SpecialSoundnessAdversary(P))).main() @ &m : res].
apply (computational_special_soundness_binding (HC_SpecialSoundnessAdversary(P)) &m).
qed.
