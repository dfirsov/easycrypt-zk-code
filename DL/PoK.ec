pragma Goals:printall.
require import AllCore DBool Bool List Distr Aux.
require import Basics.

require import SpecialSoundness.
clone import PoK.

clone import ComputationalPoK with op special_soundness_extract <- special_soundness_extract.


section.
declare module P : MaliciousProver {HonestVerifier}.

axiom P_response_ll : islossless P.response.

lemma qr_computational_PoK &m  s aux: 
  Pr[Extractor(P).extract(s, aux) @ &m : IsDL s res ] >=
   (Pr[Soundness(P, HonestVerifier).run(s, aux) @ &m : res]^2
   - (1%r/2%r) * Pr[Soundness(P, HonestVerifier).run(s, aux) @ &m : res]).
apply (statistical_PoK P  _ &m). apply P_response_ll.
smt (perfect_special_soundness).
qed.

end section.
