pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import FS_Basics FS_Sim1Property.
import OSS.



clone import ZKT.SequentialComposition.


clone import  Statistical with op epsilon <- 0%r,
                                 op sigma <- 1%r/2%r.


require RewBasics.
clone import RewBasics as Rew with type sbits <- sbits.



section.
declare module V <: RewMaliciousVerifier{-ZKT.Hyb.HybOrcl,-ZKT.Hyb.Count,-HP}.
declare module D <: ZKDistinguisher{-ZKT.Hyb.HybOrcl,-ZKT.Hyb.Count, -HP}.
declare axiom Sim1_run_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge 
  => islossless V0.summitup => islossless Sim1(V0).run.
declare axiom V_summitup_ll : islossless V.summitup. 
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom D_guess_ll : islossless D.guess.
declare axiom P_response_ll : islossless HP.response.
declare axiom P_commitment_ll : islossless HP.commitment.
declare axiom simn_simulate_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge 
  => islossless V0.summitup => islossless SimN(Sim1, V0).simulate.
declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].

(* rewindability assumption *)
declare axiom rewindable_V_plus :
        (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).




lemma qr_statistical_zk stat wit &m:
        zk_relation stat wit =>
        let real_prob = Pr[ZKReal(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimN(Sim1), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= 2%r * (1%r / 2%r) ^ OSS.N.
proof.
progress.
apply (statistical_zk HP Sim1  V D _ _ _ _ _ _ _ _ _  _ stat wit  
   &m _ );auto. apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll. 
apply P_response_ll. apply P_commitment_ll.
apply D_guess_ll.  conseq  D_guess_prop. auto.
   apply (sim1_rew_ph V). 
 apply V_summitup_ll. apply V_challenge_ll.  apply (rewindable_A_plus V). 
apply rewindable_V_plus.
progress. 
rewrite (sim1_prop V D _ _  _ _).  apply (rewindable_A_plus V).
apply rewindable_V_plus.
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. 
conseq D_guess_prop. auto. auto. auto.
progress.
rewrite (sim1assc V D _ _ _ _ _ &m0 stat0). apply (rewindable_A_plus V).
apply rewindable_V_plus.
apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. conseq D_guess_prop. auto. auto. auto.
qed.

       
       
lemma qr_statistical_zk_iter stat wit &m:
        zk_relation stat wit =>
        let real_prob = Pr[ZKRealAmp(HP, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(SimAmp(SimN(Sim1)), V, D).run(stat, wit) @ &m : res] in
          `|ideal_prob - real_prob| <= ZKT.n%r * (2%r * (1%r / 2%r) ^ OSS.N).
progress.
apply (zk_seq HP (SimN(Sim1)) V D _ _ _ _ _ _ _ &m  (2%r * (1%r / 2%r) ^ OSS.N) stat wit). 
progress.  apply (simn_simulate_ll V0). auto. auto.
apply V_summitup_ll. apply V_challenge_ll. apply P_response_ll.
apply P_commitment_ll. apply D_guess_ll.  conseq D_guess_prop. 
smt. progress.
apply (statistical_zk HP Sim1  V (Di(D, SimN(Sim1), V)) _ _ _ _ _ _ _ _ _  _ stat wit  
   &n _ ).
apply Sim1_run_ll. apply V_summitup_ll. apply V_challenge_ll.
apply P_response_ll. apply P_commitment_ll.
proc. 
call D_guess_ll. sp.
while (true) (ZKT.n - ZKT.Hyb.HybOrcl.l). progress.
wp. call (simn_simulate_ll V). apply V_challenge_ll. apply V_summitup_ll.  skip. smt.
skip. smt. auto. auto. progress.
proc. 
call D_guess_prop. sim.
progress.
proc*.  
call (sim1_rew_ph V _ _ _ x).  apply V_summitup_ll.
apply V_challenge_ll. apply (rewindable_A_plus V).
apply rewindable_V_plus. skip. auto. progress.
rewrite (sim1_prop V (Di(D, SimN(Sim1), V))).
apply (rewindable_A_plus V). apply rewindable_V_plus.
apply V_summitup_ll. apply V_challenge_ll. 
proc. 
call D_guess_ll. sp.
while (true) (ZKT.n - ZKT.Hyb.HybOrcl.l). progress.
wp. call (simn_simulate_ll V).  apply V_challenge_ll. apply V_summitup_ll. 
skip. smt. skip. smt.
auto. auto. progress.
proc. call D_guess_prop. sim. auto. auto.
progress.
rewrite (sim1assc V D _ _ _ _  _ &m0 stat0). apply (rewindable_A_plus V).
apply rewindable_V_plus. apply V_summitup_ll.
apply V_challenge_ll. apply D_guess_ll. 
proc*.
call D_guess_prop. skip. auto. 
auto. auto. auto.
qed.


end section.