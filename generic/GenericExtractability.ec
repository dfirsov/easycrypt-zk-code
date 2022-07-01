pragma Goals:printall.
require import AllCore List Distr.

require GenericZeroKnowledge.
clone include GenericZeroKnowledge. (* inherit defs. *)


module type Extractor(P: MaliciousProver) = {
    proc extract(statement: statement) : witness
}.



theory ExtractabilityTheory.

section.

declare module Extractor <: Extractor.  
declare module P <: MaliciousProver{-HonestVerifier}.

lemma computational_statistical_soundness &m p f epsilon:
    ! in_language soundness_relation p => 
  Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] >=
   f Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]
    => (forall s, f s <= 0%r => s <= epsilon) =>
    Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]
     <= epsilon.
proof. progress.
have f1 : Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] = 0%r.
  have <-: Pr[Extractor(P).extract(p) @ &m : false ] = 0%r.
  rewrite Pr[mu_false]. auto.
rewrite Pr[mu_eq]. smt. auto.
smt. qed. 

end section.


end ExtractabilityTheory.
