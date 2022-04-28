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
declare module P : MaliciousProver {HonestVerifier}.

op ss : hc_prob.
op auxx : auxiliary_input.

clone import SSB as SSB with op ss <- ss,
                             op auxx <- auxx.

module A(P : MaliciousProver) : Adv = {
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


local lemma ex_a_eq_1 &m p aux : 
 Pr[ InitRun2(A(P)).run(p,aux) @ &m 
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

local lemma ex_a_eq_2 &m p aux : 
 Pr[ InitRun2(A(P)).run(p,aux) @ &m 
          : res.`1.`1 <> res.`2.`1  /\
  hc_verify p res.`1.`2.`2 res.`1.`1 res.`1.`2.`1  /\
  hc_verify p res.`2.`2.`2 res.`2.`1 res.`2.`2.`1  /\
   IsHC (p, special_soundness_extract p (res.`1.`2.`2, res.`1.`1, res.`1.`2.`1) 
                                         (res.`2.`2.`2, res.`2.`1, res.`2.`2.`1)) ] 
  = Pr[ HC_SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
             valid_transcript_pair p res.`1 res.`2 /\
               IsHC (p, special_soundness_extract p res.`1 res.`2)].
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


  


local lemma hc_pok' &m  : 
  Pr[ HC_SpecialSoundnessAdversary(P).attack(ss, auxx) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
              IsHC (ss, special_soundness_extract ss res.`1 res.`2)]

    >= (Pr[ InitRun1(A(P)).run(ss,auxx) @ &m  : hc_verify ss res.`2.`2 res.`1 res.`2.`1 ]^2
         - (1%r/2%r) * Pr[ InitRun1(A(P)).run(ss,auxx) @ &m  :  hc_verify ss res.`2.`2 res.`1 res.`2.`1   ])
        - Pr[BindingExperiment(SpecialSoundnessBinder(HC_SpecialSoundnessAdversary(P))).main() @ &m : res].
rewrite - ex_a_eq_2.
have -> : (1%r/2%r) = (1%r / (size [false ; true ])%r). smt.

apply (final_eq_step1 (A(P)) _ &m (fun pq (r : bool * (hc_resp * hc_com)) => hc_verify (fst pq) r.`2.`2 r.`1 r.`2.`1) (fun (pq :hc_prob * auxiliary_input) (r1 r2 : bool * (hc_resp * hc_com)) => IsHC ((fst pq), special_soundness_extract (fst pq) (r1.`2.`2, r1.`1, r1.`2.`1) (r2.`2.`2, r2.`1, r2.`2.`1)))
  (ss, auxx)
 Pr[BindingExperiment(SpecialSoundnessBinder(HC_SpecialSoundnessAdversary(P))).main() @ &m : res]  
_
). admit.  simplify.
rewrite  ex_a_eq_1.
apply (ex_a_eq2 &m).
qed.


local lemma qqq &m : 
  Pr[HC_SpecialSoundnessAdversary(P).attack(ss, auxx) @ &m :
       valid_transcript_pair ss res.`1 res.`2 /\
       IsHC (ss, special_soundness_extract ss res.`1 res.`2)]
 <=  Pr[Extractor(P).extract(ss, auxx) @ &m : IsHC (ss, res)].
byequiv. proc. inline*. wp. call (_:true).
rnd.  simplify. call (_:true). rnd.  call (_:true).
wp. simplify. skip. progress. smt. smt. smt.
smt. auto.  auto.
qed.


local lemma www &m : 
  Pr[ InitRun1(A(P)).run(ss,auxx) @ &m 
      : hc_verify ss res.`2.`2 res.`1 res.`2.`1 ]
 = Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res].
byequiv. proc. inline*. wp. call (_:true).
wp. rnd.  wp. call (_:true). wp. 
skip. simplify. progress. smt. smt. auto. auto.
qed.


lemma hc_pok &m : 
  Pr[Extractor(P).extract(ss, auxx) @ &m : IsHC (ss, res)] >=
   (Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res]^2
   - (1%r/2%r) * Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res])
     - Pr[BindingExperiment(SpecialSoundnessBinder(HC_SpecialSoundnessAdversary(P))).main() @ &m : res].
smt (www hc_pok' qqq).
qed.


require import RealExp.


lemma qqq1  (a b : real) : a <= b  => sqrt a <= sqrt b.
smt. qed.


lemma qqq2  (a b : real) : a ^ 2 <= b  => a <= sqrt b.
smt. qed.


lemma hc_computational_soundness &m :
    ! in_language (fun x y => IsHC (x,y)) ss =>
     Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res]
     <= sqrt (Pr[BindingExperiment(SpecialSoundnessBinder(HC_SpecialSoundnessAdversary(P))).main() @ &m : res] + 1%r/2%r).
proof. progress.
have f1 : Pr[Extractor(P).extract(ss, auxx) @ &m : IsHC (ss, res)] = 0%r.
  have <-: Pr[Extractor(P).extract(ss, auxx) @ &m : false ] = 0%r.
  rewrite Pr[mu_false]. auto.
rewrite Pr[mu_eq]. smt. auto.
have  :   0%r >=
   (Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res]^2
   - (1%r/2%r) * Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res])
     - Pr[BindingExperiment(SpecialSoundnessBinder(HC_SpecialSoundnessAdversary(P))).main() @ &m : res].
 rewrite - f1.
apply hc_pok.
pose a := Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res].
pose b := Pr[BindingExperiment(SpecialSoundnessBinder(HC_SpecialSoundnessAdversary(P))).main
   () @ &m : res].
have f2 : 0%r <= a <= 1%r. smt.
smt (qqq1 qqq2).
qed.



end section.
