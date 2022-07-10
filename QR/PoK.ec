pragma Goals:printall.
require import AllCore.
require import Aux Permutation Basics List.


require import SpecialSoundness.


clone import SpecialSoundnessTheory as SST with op special_soundness_extract <- special_soundness_extract.

section.
declare module P <: RewMaliciousProver {-HV}.
declare axiom P_response_ll : islossless P.response.

lemma qr_computational_PoK &m  s: 
  Pr[Extractor(P).extract(s) @ &m : IsSqRoot s res /\ unit s] >=
   (Pr[Soundness(P, HV).run(s) @ &m : res]^2
     - (1%r/2%r) * Pr[Soundness(P, HV).run(s) @ &m : res]).
apply (SST.Perfect.PoK_from_special_soundness P  _ _ &m s  ).  apply P_response_ll. 
apply perfect_special_soundness.
qed.

end section.
