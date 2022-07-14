pragma Goals:printall.
require import AllCore DBool Bool List Distr Real.
require import FS_Basics.

require import FS_SpecialSoundness.
require import FS_Extractability.
import SST.





section.

declare module P <: RewMaliciousProver {-HV}.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.


(* rewindability assumption *)
declare axiom rewindable_P_plus :
        (exists (f : glob P -> sbits),
         injective f /\
         (forall &m, Pr[ P.getState() @ &m : (glob P) = ((glob P){m})
                                          /\ res = f ((glob P){m} ) ] = 1%r) /\
         (forall &m b (x: glob P), b = f x =>
           Pr[P.setState(b) @ &m : glob P = x] = 1%r) /\
         islossless P.setState).


lemma qr_soundness &m s:
    ! in_language soundness_relation s =>
     Pr[Soundness(P, HV).run(s) @ &m : res]
     <= 1%r/2%r.
progress.
apply (SST.Perfect.statistical_soundness P _).
apply rewindable_P_plus.
apply P_response_ll.
apply qr_perfect_special_soundness. auto.
qed.


clone import SoundnessTheory.
clone import Statistical with op soundness_error <= fun _ => 1%r/2%r.

lemma qr_soundness_iter &m s n:
     1 <= n =>
     ! in_language soundness_relation s =>
     Pr[SoundnessAmp(P, HV).run(s,n) @ &m : res]
        <= (1%r/2%r) ^ n.
proof. progress.
apply (soundness_seq P  _ _ _ _ _ &m).
proc. skip. auto.
proc. wp. rnd. skip. progress. smt.
apply P_response_ll.
apply P_commitment_ll.
apply qr_soundness. auto. auto.
qed.

end section.

