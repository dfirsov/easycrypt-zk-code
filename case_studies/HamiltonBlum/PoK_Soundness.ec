pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin RealExp.
require import Aux Permutation Basics.

require import SpecialSoundness.
clone import PoK.

clone import ComputationalPoK with op special_soundness_extract <- special_soundness_extract.


section.
declare module P <: MaliciousProver {-HonestVerifier}.

declare axiom P_response_ll : islossless P.response.
op ss : hc_prob.
op auxx : auxiliary_input.

clone import SSB as SSB with op ss <- ss,
                             op auxx <- auxx.

lemma hc_computational_PoK &m : 
  Pr[Extractor(P).extract(ss, auxx) @ &m : IsHC (ss, res)] >=
   (Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res]^2
   - (1%r/2%r) * Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res])
     - Pr[BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P))).main() @ &m : res].
apply (computational_PoK P _ &m).  apply P_response_ll.
apply (computational_special_soundness_binding (SpecialSoundnessAdversary(P)) &m).
qed.



lemma hc_computational_soundness &m :
    ! in_language (fun x y => IsHC (x,y)) ss =>
     Pr[Soundness(P, HonestVerifier).run(ss, auxx) @ &m : res]
     <= sqrt (Pr[BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P))).main() @ &m : res] + 1%r/2%r).
proof.  progress.
apply (computational_soundness P _ &m ss auxx _ );auto.  apply P_response_ll.
apply (computational_special_soundness_binding (SpecialSoundnessAdversary(P)) &m).
qed.


end section.
