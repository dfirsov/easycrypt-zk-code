pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import Permutation Basics Sim1Property.
import Sim1Property.ZK.

import Sim1Property.QR_SZK.
import OMZK.

clone import  StatisticalZKDeriv with op negl <- 0%r.


require RewBasics.
clone import RewBasics as Rew with type sbits <- sbits.

section.

declare module V : MaliciousVerifier{HonestProver, OMZK.MW.IFB.IM.W, OMZK.MW.IFB.DW}.
declare module D : ZKDistinguisher{HonestProver, OMZK.MW.IFB.IM.W, V}.


axiom Sim1_run_ll : forall (V0 <: MaliciousVerifier), islossless V0.challenge => islossless V0.summitup => islossless Sim1(V0).run.

axiom V_summitup_ll : islossless V.summitup. 
axiom V_challenge_ll : islossless V.challenge.
axiom D_guess_ll : islossless D.guess.


axiom rewindable_V_plus : 
        (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).



lemma qr_statistical_zk stat wit ax N &m:
        IsSqRoot stat  wit  => unit stat =>
        0 <= N =>
        let real_prob = Pr[ZKReal(HonestProver, V, D).run(stat, wit, ax) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N, ax) @ &m : res] in
          `|real_prob - ideal_prob| <= 2%r * (1%r / 2%r) ^ N.
proof.
progress.
apply (statistical_zk HonestProver Sim1  V D _ _ _ _ _ _ _ stat wit ax N
  (1%r/2%r) &m). apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll. apply D_guess_ll.
apply rewindable_V_plus.
apply (sim1_rew_ph V ). apply V_summitup_ll. apply V_challenge_ll. 
apply (rewindable_A_plus V). apply rewindable_V_plus.
progress.
rewrite (sim1_prop V D _ _  _ _ _  p w aux _ ).  apply (rewindable_A_plus V). exists f. split. auto. auto.
auto. auto.   auto.  auto. auto.   auto. auto. 
rewrite (sim1assc V D _ _ _ _ &m stat ax wit). apply (rewindable_A_plus V).
apply rewindable_V_plus. 
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. auto.  auto. 
qed.
