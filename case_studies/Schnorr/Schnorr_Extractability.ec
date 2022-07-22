pragma Goals:printall.
require import AllCore DBool Bool List Distr Aux Finite.
require import CyclicGroup.
import FDistr.

require import Schnorr_Basics.
require import Schnorr_SpecialSoundness.

clone import SpecialSoundnessTheory as SST with op special_soundness_extract <- special_soundness_extract.


section.
declare module P <: RewMaliciousProver{-HV}.
declare axiom P_response_ll : islossless P.response.


(* rewindability assumption *)
declare axiom rewindable_P_plus :
        (exists (f : glob P -> sbits),
         injective f /\
         (forall &m, Pr[ P.getState() @ &m : (glob P) = ((glob P){m})
                                          /\ res = f ((glob P){m} ) ] = 1%r) /\
         (forall &m b (x: glob P), b = f x =>
           Pr[P.setState(b) @ &m : glob P = x] = 1%r) /\
         islossless P.setState).

(* automatically implying proof-of-knowledge from special soundness  *)
lemma dl_statistical_PoK &m s: 
  Pr[Extractor(P).extract(s) @ &m : soundness_relation s res ] >=
   (Pr[Soundness(P, HV).run(s) @ &m : res]^2
      - 1%r / (size (to_seq (support dt)))%r 
           * Pr[Soundness(P, HV).run(s) @ &m : res]).
apply (SST.Perfect.statistical_extractability P  _ _ _ &m s  ).
apply rewindable_P_plus. apply P_response_ll.
apply dl_perfect_special_soundness.
qed.

end section.
