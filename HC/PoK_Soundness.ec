pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import Aux Permutation Basics.

require import SpecialSoundness.
clone import PoK.
clone import ComputationalPoK with 
 op special_soundness_extract <- special_soundness_extract.



section.
declare module P : MaliciousProver {HonestVerifier}.

axiom P_response_ll : islossless P.response.

op ss : hc_prob.
op auxx : auxiliary_input.

clone import SSB as SSB with op ss <- ss,
                             op auxx <- auxx.


local module ExtractionReduction(P : MaliciousProver) = {
  module E = BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P)))
  proc run(statement : hc_prob, aux : auxiliary_input) : bool = {
    var r;
    r  <@ E.main();
    return r;
  }
}.

local lemma ex_a_eq1 &m : 
  Pr[ExtractionReduction(P).run(ss,auxx) @ &m : res] 
  = Pr[BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P))).main() @ &m : res]. byequiv. proc. 
inline ExtractionReduction(P).E.main. wp.  sim. auto.  auto.
qed.

local lemma ex_a_eq2 &m  :
  Pr[ SpecialSoundnessAdversary(P).attack(ss, auxx) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
              ! IsHC (ss, special_soundness_extract ss res.`1 res.`2)]
 <= Pr[ExtractionReduction(P).run(ss,auxx) @ &m : res].
rewrite ex_a_eq1.
apply (computational_special_soundness_binding (SpecialSoundnessAdversary(P)) &m).
qed.
  



lemma hc_computational_PoK &m : 
  Pr[Extractor(P).extract(ss, auxx) @ &m : IsHC (ss, res)] >=
   (Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res]^2
   - (1%r/2%r) * Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res])
     - Pr[BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P))).main() @ &m : res].
rewrite - ex_a_eq1. 
apply (computational_PoK P ExtractionReduction _ &m). apply P_response_ll.
apply (ex_a_eq2 &m).
qed.

require import RealExp.
lemma hc_computational_soundness &m :
    ! in_language (fun x y => IsHC (x,y)) ss =>
     Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res]
     <= sqrt (Pr[BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P))).main() @ &m : res] + 1%r/2%r).
proof.  progress.
rewrite - ex_a_eq1. 
apply (computational_soundness P ExtractionReduction _ &m ss auxx _ ). apply P_response_ll.
auto.
apply (ex_a_eq2 &m).
qed.


end section.
