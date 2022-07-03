pragma Goals:printall.
require import AllCore.
require import Aux Permutation Basics List.

require import SpecialSoundness.
clone import PoK.

clone import ComputationalPoK with op special_soundness_extract <- special_soundness_extract.


section.
declare module P <: RewMaliciousProver {-HonestVerifier}.

declare axiom P_response_ll : islossless P.response.

lemma qr_computational_PoK &m  s: 
  Pr[Extractor(P).extract(s) @ &m : IsSqRoot s res /\ unit s] >=
   (Pr[Soundness(P, HonestVerifier).run(s) @ &m : res]^2
     - (1%r/2%r) * Pr[Soundness(P, HonestVerifier).run(s) @ &m : res]).



apply (statistical_PoK P  _ &m s _ ).  apply P_response_ll. 
smt (perfect_special_soundness).
qed.

end section.
