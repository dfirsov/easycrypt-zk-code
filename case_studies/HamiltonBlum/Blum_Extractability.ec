pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin RealExp.
require import Aux Blum_Basics.

require import Blum_SpecialSoundness.


section.
declare module P <: RewMaliciousProver {-HV}.

declare axiom P_response_ll : islossless P.response.
op ss : hc_prob.

declare axiom P_rewindable : exists (f : (glob P) -> sbits),
  injective f /\
  (forall &m0,
     Pr[P.getState() @ &m0 : (glob P) = (glob P){m0} /\ res = f (glob P){m0}] =
     1%r) /\
  (forall &m0 (b : sbits) (x : (glob P)),
     b = f x => Pr[P.setState(b) @ &m0 : (glob P) = x] = 1%r) /\
  islossless P.setState.


clone import SSB as SSB with op ss <- ss.

lemma hc_computational_PoK &m : 
  Pr[Extractor(P).extract(ss) @ &m : IsHC (ss, res)] >=
   (Pr[Soundness(P, HV).run(ss) @ &m : res]^2
   - (1%r/2%r) * Pr[Soundness(P, HV).run(ss) @ &m : res])
     - Pr[BindingExperiment(SpecialSoundnessBinder(SpecialSoundnessAdversary(P))).main() @ &m : res].
apply (Computational.computational_extractability P _ _ &m). apply P_response_ll.  apply P_rewindable.
apply (computational_special_soundness_binding (SpecialSoundnessAdversary(P)) &m).
qed.


end section.
