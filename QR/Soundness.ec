pragma Goals:printall.
require import AllCore DBool Bool List Distr RealExp.
require import Basics.

require import PoK.
import SS.

clone import ExtractabilityTheory as ET.

section.

declare module P <: RewMaliciousProver {-HV}.
declare axiom P_response_ll : islossless P.response.


lemma qr_soundness &m s:
    ! in_language soundness_relation s =>
     Pr[Soundness(P, HV).run(s) @ &m : res]
     <= 1%r/2%r.
progress.
print computational_statistical_soundness.
apply (computational_statistical_soundness Extractor HV P &m s
 (fun (x:real) => x ^2 - 1%r/2%r * x) (1%r/2%r)   ).
auto. simplify. 
simplify.
apply (qr_computational_PoK P _ &m s).
apply P_response_ll.
move => x. simplify.
have -> : x ^ 2 = x * x. smt.
smt.
qed.


end section.

