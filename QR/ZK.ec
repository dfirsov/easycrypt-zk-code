pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import  Basics Sim1Property.

import OSS.
(* import OMZK. *)

clone import  StatisticalZK with op negl <- 0%r.


require RewBasics.
clone import RewBasics as Rew with type sbits <- sbits.

section.



declare module V <: RewMaliciousVerifier{-HP}.
declare module D <: ZKDistinguisher{-HP}.



declare axiom Sim1_run_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge => islossless V0.summitup => islossless Sim1(V0).run.
declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].
declare axiom V_summitup_ll : islossless V.summitup. 
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
declare axiom P_response_ll : islossless HP.response.
declare axiom P_commitment_ll : islossless HP.commitment.


declare axiom rewindable_V_plus : 
        (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).



lemma qr_statistical_zk stat wit &m:
        IsSqRoot stat  wit  => unit stat =>
        let real_prob = Pr[ZKReal(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator'(Sim1), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= 2%r * (1%r / 2%r) ^ n.
proof.
progress.
apply (statistical_zk HP Sim1  V D _ _ _ _ _ _ _ _ _ _ stat wit  
  (1%r/2%r) &m _ _);auto. apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll. 
apply P_response_ll. apply P_commitment_ll.
apply D_guess_ll. apply D_guess_prop.
apply rewindable_V_plus. 
apply (sim1_rew_ph V). 
 apply V_summitup_ll. apply V_challenge_ll.  apply (rewindable_A_plus V). apply rewindable_V_plus.
progress. 
rewrite (sim1_prop V D _ _  _ _ _  p w  _ ).  apply (rewindable_A_plus V).
 exists f. split. auto. auto.
auto. auto.   auto.  auto. auto. 
rewrite (sim1assc V D _ _ _ _ &m stat  wit). apply (rewindable_A_plus V).
apply rewindable_V_plus.
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. auto.  auto. 
qed.
