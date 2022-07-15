pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import Permutation Blum_Basics Blum_Sim1Property.

import DJMM.
import OSS.

clone import Statistical with op epsilon <- 2%r * negl + 20%r * negl2,
                              op sigma <- (1%r/2%r - negl2).


axiom negl2_prop : 0%r <= negl2 < 1%r/4%r.

require RewBasics.
clone import RewBasics as Rew with type sbits <- sbits.


section.

declare module V <: RewMaliciousVerifier{-HonestProver, -ZKT.Hyb.HybOrcl,-ZKT.Hyb.Count}.
declare module D <: ZKDistinguisher{-HonestProver, -V, -ZKT.Hyb.HybOrcl,-ZKT.Hyb.Count }.


declare axiom Sim1_run_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge => islossless V0.summitup => islossless Sim1(V0).run.
declare axiom V_summitup_ll : islossless V.summitup. 
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
declare axiom P_response_ll : islossless HonestProver.response.
declare axiom P_commitment_ll : islossless HonestProver.commitment.

declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].

declare axiom rewindable_V_plus :
        (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                               /\ res = f ((glob V){m}) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).


lemma hc_statistical_zk stat wit  &m:
        zk_relation stat wit => 
        let real_prob = Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimN(Sim1), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= (2%r * negl + 20%r * negl2) + 2%r * (1%r- (1%r/2%r - negl2)) ^ OSS.N.
proof.
progress.
apply (statistical_zk HonestProver Sim1  V D _ _ _ _ _ _ _ _ _ _  stat wit &m _). apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll. apply P_response_ll. apply P_commitment_ll.
apply D_guess_ll. 
proc*. call D_guess_prop. skip.  auto.
move => x.
apply (sim1_rew_ph V _ _ _ _ _ x). apply V_summitup_ll. apply V_challenge_ll. apply P_response_ll. apply P_commitment_ll.
apply (rewindable_A_plus V). apply rewindable_V_plus.
progress.
apply (sim1_prop V D  _ _  _ _ _  _ &m0 p w  _ );auto.  apply V_summitup_ll. apply (rewindable_A_plus V). apply rewindable_V_plus. 
apply D_guess_ll. apply V_summitup_ll. apply V_challenge_ll. smt (negl2_prop).
progress.
apply (sim1assc V D _ _ _ _ _ _ &m0 stat0 _).  apply V_summitup_ll. apply (rewindable_A_plus V). apply rewindable_V_plus. apply D_guess_ll. apply V_summitup_ll.
apply V_challenge_ll. apply negl2_prop. 
elim H0. progress. smt.
auto.
qed.


end section.
