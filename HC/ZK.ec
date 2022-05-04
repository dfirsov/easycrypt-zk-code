pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import Permutation Basics Sim1_Property.
import DJMM.
import Sim1_Property.ZK.

import Sim1_Property.HC_SZK.
import OMZK.

clone import StatisticalZKDeriv with op negl <- 2%r * negl + 20%r * negl2.
axiom negl2_prop : 0%r <= negl2 < 1%r/4%r.

lemma sim1_rew_ph :         forall (V <: MaliciousVerifier) , forall (x : (glob V) * (glob Sim1)),
  phoare[ Sim1(V).run :
           ((glob V), (glob Sim1)) = x ==> ((glob V), (glob Sim1)) = x] = 1%r.
admitted.

lemma hc_statistical_zk:
        forall (V <: MaliciousVerifier{HonestProver, OMZK.MW.IFB.IM.W, OMZK.MW.IFB.DW}) 
               (D <: ZKDistinguisher{HonestProver, OMZK.MW.IFB.IM.W, V}),
        (forall (V0 <: MaliciousVerifier), islossless V0.challenge => islossless V0.summitup => islossless Sim1(V0).run) =>
        forall stat wit ax N &m,
        islossless V.summitup => islossless V.challenge => islossless D.guess =>
        forall (V0 <: MaliciousVerifier), 
        IsHC (stat, wit) => 
        0 <= N =>
        let real_prob = Pr[ZKReal(HonestProver, V, D).run(stat, wit, ax) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N, ax) @ &m : res] in
          `|real_prob - ideal_prob| <= (2%r * negl + 20%r * negl2) + 2%r * (1%r- (1%r/2%r - negl2) ) ^ N.
progress.
print statistical_zk.
apply (statistical_zk HonestProver Sim1  V D _ _  _ _ _ _ stat wit ax N
  (inv 2%r - negl2) &m).
apply H. auto. auto. auto. apply (sim1_rew_ph V). 
progress. 
apply (sim1_prop V0 D0 _ _  _ &m0 p w aux _ ).
auto. auto. apply negl2_prop.  auto. auto. auto. auto. auto.  auto. 
apply (sim1assc V D);auto. apply negl2_prop. smt.
qed.
