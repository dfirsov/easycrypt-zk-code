pragma Goals:printall.
require import AllCore List Distr.

require GenericSoundness.
clone include GenericSoundness. (* inherit defs. *)

type adv_summary.

op zk_relation : relation.

module type RewMaliciousVerifier = {
  proc challenge(_:statement * commitment) : challenge
  proc summitup(statement: statement, response: response): adv_summary
  proc getState() : sbits
  proc * setState(b : sbits) : unit 
}.

module type MaliciousVerifier = {
  proc challenge(_:statement * commitment) : challenge
  proc summitup(statement: statement, response: response) : adv_summary
}.


module type ZKDistinguisher = {
  proc guess(statement: statement, witness: witness, summary: adv_summary) : bool
}.

module type Simulator(V: RewMaliciousVerifier) = {
  proc * simulate(statement: statement, n : int) : adv_summary
}.

module type Simulator1(V: RewMaliciousVerifier) = {
  proc run(statement: statement) : bool * adv_summary
}.



module ZKReal(P: HonestProver, V: MaliciousVerifier, D: ZKDistinguisher) = {
  proc run(statement: statement, witness: witness) = {
    var commit, challenge, response, summary, guess;
    commit <@ P.commitment(statement, witness);
    challenge <@ V.challenge(statement, commit);
    response <@ P.response(challenge);
    summary <@ V.summitup(statement, response);
    guess <@ D.guess(statement, witness, summary);
    return guess;
  }
}.


module ZKIdeal(S: Simulator, V: RewMaliciousVerifier, D: ZKDistinguisher) = {
  proc run(statement: statement, witness: witness, n : int) = {
    var summary, guess;
    summary <@ S(V).simulate(statement, n);
    guess <@ D.guess(statement, witness, summary);
    return guess;
  }
}.




abstract theory ZeroKnowledgeTheory.

op s:statement.
op w:witness.
op n : int.

axiom zkrel_prop : zk_relation s w.

require Hybrid.
(* q -> N *)
clone import Hybrid as Hyb with type input <- unit,
                                type output <- adv_summary,
                                type outputA <- bool,
                                op q <- n+1.


module Ad(D : ZKDistinguisher, Ob : Orclb, O : Orcl) = {
  proc main() : bool = {
    var summary, guess,i;
    i <- 0;
    summary <- witness;
    while (i <= n){
       summary <@ O.orcl();
       i <- i + 1;
    }
    guess <@ D.guess(s, w, summary);
    return guess;
  }
}.


module Obb(P : HonestProver, V : RewMaliciousVerifier, Sim : Simulator) = {
  proc leaks(x:inleaks) : outleaks = {
    return witness;
  }
  proc orclR() : adv_summary = {
    var commit, challenge, response, summary;
    commit <@ P.commitment(s, w);
    challenge <@ V.challenge(s, commit);
    response <@ P.response(challenge);
    summary <@ V.summitup(s, response);
    return summary;
  }
  proc orclL() : adv_summary = {
    var summary;
    summary <@ Sim(V).simulate(s, n);
    return summary;
  }
}.

require import MemoryPropsLE.


section.


declare module Q <: HonestProver.
declare module P <: HonestProver{-Q, -HybOrcl, -Count}.
declare module Sim <: Simulator{-Q, -HybOrcl, -P, -Count}.
declare module V <: RewMaliciousVerifier {-Q, -HybOrcl, -P, -Sim, -Count}.
declare module D <: ZKDistinguisher{-Q, - Count}. 


declare axiom sim_run_ll : forall (V0 <: RewMaliciousVerifier),  
     islossless V0.challenge => islossless V0.summitup => islossless Sim(V0).simulate.
declare axiom V_summitup_ll  : islossless V.summitup.
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.
declare axiom D_guess_ll     : islossless D.guess.

declare axiom q_ge1 : 0 <= n. 

declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].

module Ob = Obb(P,V,Sim).
module A = Ad(D).



module Y = {
  proc main() = {
   var summary, guess;
   HybOrcl.l0 <$ [0..max 0 n];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     summary <@
       HybOrcl(Ob, R(Ob)).orcl();
   }
   while (HybOrcl.l <= n && HybOrcl.l0 <= HybOrcl.l) {
     summary <@
       HybOrcl(Ob, R(Ob)).orcl();
   }
   guess <@ D.guess(s, w, summary);
   return guess;
 }
}.
module Z = {
  proc main() = {
   var summary, guess;
   HybOrcl.l0 <$ [0..max 0 (n )];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     summary <@
       HybOrcl(Ob, L(Ob)).orcl();
   }
   while (HybOrcl.l <= n && HybOrcl.l0 <= HybOrcl.l) {
     summary <@
       HybOrcl(Ob, L(Ob)).orcl();
   }
   guess <@ D.guess(s, w, summary);
   return guess;
 }
}.
module Z2 = {
  proc main() = {
   var summary, guess;
   HybOrcl.l0 <$ [0..max 0 (n )];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     summary <@
       HybOrcl(Ob, L(Ob)).orcl();
   }
   if(HybOrcl.l <= n && HybOrcl.l0 <= HybOrcl.l){
     summary <@
       HybOrcl(Ob, L(Ob)).orcl();
   }
   while (HybOrcl.l <= n && HybOrcl.l0 <= HybOrcl.l) {
     summary <@
       HybOrcl(Ob, L(Ob)).orcl();
   }
   guess <@ D.guess(s, w, summary);
   return guess;
 }
}.
module Y2 = {
  proc main() = {
   var summary, guess;
   HybOrcl.l0 <$ [0..max 0 (n )];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     summary <@
       HybOrcl(Ob, R(Ob)).orcl();
   }
   if(HybOrcl.l <= n && HybOrcl.l0 <= HybOrcl.l){
     summary <@
       HybOrcl(Ob, R(Ob)).orcl();
   }
   while (HybOrcl.l <= n && HybOrcl.l0 <= HybOrcl.l) {
     summary <@
       HybOrcl(Ob, R(Ob)).orcl();
   }
   guess <@ D.guess(s, w, summary);
   return guess;
 }
}.
module Z3 = {
  proc main() = {
    var commit, challenge, response, summary, guess;
   HybOrcl.l0 <$ [0..max 0 (n )];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     commit <@ P.commitment(s, w);
     challenge <@ V.challenge(s, commit);
     response <@ P.response(challenge);
     summary <@ V.summitup(s, response);
     HybOrcl.l <- HybOrcl.l + 1;
   }
   summary <@ Sim(V).simulate(s, n);
   HybOrcl.l <- HybOrcl.l + 1;
   while (HybOrcl.l <= n) {
    summary <@ Sim(V).simulate(s, n);
    HybOrcl.l <- HybOrcl.l + 1;
   }
   guess <@ D.guess(s, w, summary);
   return guess;
 }
}.
module Y3 = {
  proc main() = {
    var commit, challenge, response, summary, guess;
   HybOrcl.l0 <$ [0..max 0 (n )];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     commit <@ P.commitment(s, w);
     challenge <@ V.challenge(s, commit);
     response <@ P.response(challenge);
     summary <@ V.summitup(s, response);
     HybOrcl.l <- HybOrcl.l + 1;
   }
     commit <@ P.commitment(s, w);
     challenge <@ V.challenge(s, commit);
     response <@ P.response(challenge);
     summary <@ V.summitup(s, response);
   HybOrcl.l <- HybOrcl.l + 1;
   while (HybOrcl.l <= n) {
    summary <@ Sim(V).simulate(s, n);
    HybOrcl.l <- HybOrcl.l + 1;
   }
   guess <@ D.guess(s, w, summary);
   return guess;
 }
}.
lemma y &m :
  Pr[Y2.main() @ &m : res] = Pr[Y3.main() @ &m : res].
byequiv(_: ={glob D, glob V, glob P, glob Sim, glob HybOrcl} ==> _).
proc.
seq 6 10 : (={summary, glob V}).
seq 4 4 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l0{2} = HybOrcl.l{2} /\ HybOrcl.l0{2} < n + 1
 /\ HybOrcl.l{2} <= n
   ).
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l{2} <= HybOrcl.l0{2}  /\ HybOrcl.l0{2} < n + 1 ). inline*.
sp.
rcondf {1} 1 . progress. skip. smt.
rcondf {1} 1 . progress. skip. smt.    
sp. wp. call (_:true).
call (_:true). call (_:true).
call (_:true). skip. progress. smt. 
wp. rnd. skip. progress.  smt. smt. smt. smt.
rcondt {1} 1. progress. 
seq 1 5 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n + 1 /\ HybOrcl.l{2} <= n + 1).
inline HybOrcl(Ob, R(Ob)).orcl. sp. 
rcondf {1} 1. progress. 
rcondt {1} 1. progress. 
inline*.
sp. wp.  
call (_:true). call (_:true).
call (_:true). call (_:true). skip. progress. smt.  smt.
while (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n+1).
inline*. sp.
rcondt {1} 1. progress. 
sp.  wp.  call (_: ={glob V}). sim. sim. sim. sim. skip. progress. smt. 
smt.    skip. progress. smt.
call D_guess_prop. skip.  
auto. auto. auto.
qed.
lemma w &m :
  Pr[Z2.main() @ &m : res] =
    Pr[Z3.main() @ &m : res].
byequiv(_: ={glob D, glob V, glob P, glob Sim, glob HybOrcl} ==> _).
proc.
seq 6 7 : (={summary, glob V}).
seq 4 4 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l0{2} = HybOrcl.l{2} /\ HybOrcl.l0{2} < n + 1
 /\ HybOrcl.l{2} <= n
   ).
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l{2} <= HybOrcl.l0{2}  /\ HybOrcl.l0{2} < n + 1 ). inline*.
sp.
rcondf {1} 1 . progress. skip. smt.
rcondf {1} 1 . progress. skip. smt.    
sp. wp. call (_:true).
call (_:true). call (_:true).
call (_:true). skip. progress. smt. 
wp. rnd. skip. progress.  smt. smt. smt. smt.
rcondt {1} 1. progress. 
seq 1 2 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n + 1 /\ HybOrcl.l{2} <= n+1).
inline HybOrcl(Ob, L(Ob)).orcl. sp. 
rcondf {1} 1. progress. 
rcondt {1} 1. progress. 
inline*.
sp. wp.  
call (_: ={glob V}). sim. sim. sim. sim. skip. progress. smt. smt.
while (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n+1).
inline*. sp.
rcondt {1} 1. progress. 
sp.  wp.  call (_: ={glob V}). sim. sim. sim. sim. skip. progress. smt. 
smt.   skip. progress. smt.
call D_guess_prop. auto.
auto. auto.
qed.
lemma yy &m : 
  Pr[Y.main() @ &m : res] = 
    Pr[Y2.main() @ &m : res].
byequiv(_: ={glob D, glob V, glob P, glob Sim, glob HybOrcl} ==> _).
proc. 
unroll {1} 5.
seq 6 6 : (={summary, glob V}).
sim. call D_guess_prop. skip. auto.
auto. auto.
qed.
lemma ww &m : 
  Pr[Z.main() @ &m : res] = 
    Pr[Z2.main() @ &m : res].
byequiv(_: ={glob D, glob V, glob P, glob Sim, glob HybOrcl} ==> _).
proc. 
unroll {1} 5.
seq 6 6 : (={summary, glob V}).
sim.
call D_guess_prop. skip. auto.
auto. auto.
qed.
lemma www &m : 
  Pr[HybGame(A,Ob,L(Ob)).main() @ &m : res] = 
  Pr[Z.main() @ &m : res].
byequiv(_: ={glob D, glob V, glob P, glob Sim} ==> _).
proc.
inline {1} A(Ob, HybOrcl(Ob, L(Ob))).main.
splitwhile {1} 5 : (i < HybOrcl.l0).
seq 5 4 : (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  i{1} = HybOrcl.l{2} /\ HybOrcl.l0{2} <= HybOrcl.l{2}).
simplify.
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  i{1} = HybOrcl.l{2}). inline*.
sp.
rcondf {1} 1 . progress. skip.   progress.  smt.
rcondf {2} 1 . progress. skip.   progress.  smt.
rcondf {1} 1 . progress. skip.   progress.  smt.
rcondf {2} 1 . progress. skip.   progress.  smt.
sp. wp.  call (_:true). call (_:true). call (_:true). call (_:true).
skip. progress.
wp. rnd. skip. progress. smt.
wp. 
seq 1 1 : (={summary, glob V}).
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  i{1} = HybOrcl.l{2} /\ HybOrcl.l0{2} <= HybOrcl.l{2} ). 
wp. simplify. 
inline HybOrcl(Ob, L(Ob)).orcl.
wp. sp. if. progress. inline*. wp. 
call (_: ={glob V}). sim. sim. sim. sim. 
wp. skip. progress. smt. smt. 
rcondt {1} 1. progress. skip. progress. smt.
rcondt {2} 1. progress. skip. progress. smt.
inline*. wp.
call (_: ={glob V}). sim. sim. sim. sim. 
wp.  skip. progress. smt. smt.  
skip. progress.  
call D_guess_prop. skip. auto.
auto.
auto.
qed.
lemma yyy &m : 
  Pr[HybGame(A,Ob,R(Ob)).main() @ &m : res] = 
  Pr[Y.main() @ &m : res].
byequiv(_: ={glob D, glob V, glob P, glob Sim} ==> _).
proc.
inline {1} A(Ob, HybOrcl(Ob, R(Ob))).main.
splitwhile {1} 5 : (i < HybOrcl.l0).
seq 5 4 : (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  i{1} = HybOrcl.l{2} /\ HybOrcl.l0{2} <= HybOrcl.l{2}).
simplify.
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  i{1} = HybOrcl.l{2}). inline*.
sp.
rcondf {1} 1 . progress. skip.   progress.  smt.
rcondf {2} 1 . progress. skip.   progress.  smt.
rcondf {1} 1 . progress. skip.   progress.  smt.
rcondf {2} 1 . progress. skip.   progress.  smt.
sp. wp.  call (_:true). call (_:true). call (_:true). call (_:true).
skip. progress.
wp. rnd. skip. progress. smt.
wp. 
seq 1 1 : (={summary, glob V, glob HybOrcl}).
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  i{1} = HybOrcl.l{2} /\ HybOrcl.l0{2} <= HybOrcl.l{2} ). 
wp. simplify. 
inline HybOrcl(Ob, R(Ob)).orcl.
wp. sp. if. progress. inline*. wp. 
call (_: ={glob V, glob HybOrcl}). sim. sim. sim. sim. 
wp. skip. progress. smt. smt. 
rcondt {1} 1. progress. skip. progress. smt.
rcondt {2} 1. progress. skip. progress. smt.
inline*. wp. sp.  call (_:true). call (_:true). call (_:true). call (_:true).
skip. progress. smt. smt.
skip. progress.  call D_guess_prop. skip. auto.
auto.
auto.
qed.
lemma qq &m:
        Pr[Ln(Ob,A).main() @ &m : res]
      - Pr[Rn(Ob,A).main() @ &m : res]
    = (n+1)%r *(Pr[HybGame(A,Ob,L(Ob)).main() @ &m : res]
            - Pr[HybGame(A,Ob,R(Ob)).main() @ &m : res]).
apply (Hybrid_restr Ob A _ _ _ _ _ &m (fun _ _ _ r => r)).
progress. proc. inline*.
wp.  call (_:true). 
while (Count.c = i /\ i <= n+1) . wp. 
call (_:true). wp.  skip.  progress. smt.
wp.  skip.  progress. smt.
proc. skip. auto. proc.
call (sim_run_ll V). apply V_challenge_ll.
apply V_summitup_ll. skip. auto.
proc. call V_summitup_ll. call P_response_ll.
call V_challenge_ll. call P_commitment_ll. skip. auto.
progress.
proc. call D_guess_ll. sp.
while (true) (n - i + 1). progress.
wp. call H. skip. progress. smt.
progress. skip. progress. smt.
qed.



module Ob1 = Obb(P,V,Sim).
module A1 = Ad(D).

module Amem : IR1R2 = {
  proc init() = {
   var commit, challenge, response, summary;
   HybOrcl.l0 <$ [0..max 0 (n )];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     commit <@ P.commitment(s, w);
     challenge <@ V.challenge(s, commit);
     response <@ P.response(challenge);
     summary <@ V.summitup(s, response);
     HybOrcl.l <- HybOrcl.l + 1;
   }
  }
  proc run1() = {
   var  summary, guess;
   summary <@ Sim(V).simulate(s, n);
   HybOrcl.l <- HybOrcl.l + 1;
   while (HybOrcl.l <= n) {
    summary <@ Sim(V).simulate(s, n);
    HybOrcl.l <- HybOrcl.l + 1;
   }
   guess <@ D.guess(s, w, summary);
   return guess;
  }
  proc run2() = {
   var commit, challenge, response, summary, guess;
   commit <@ P.commitment(s, w);
   challenge <@ V.challenge(s, commit);
   response <@ P.response(challenge);
   summary <@ V.summitup(s, response);
   HybOrcl.l <- HybOrcl.l + 1;
   while (HybOrcl.l <= n) {
    summary <@ Sim(V).simulate(s, n);
    HybOrcl.l <- HybOrcl.l + 1;
   }
   guess <@ D.guess(s, w, summary);
   return guess;
  }
}.

module Dstar : ZKDistinguisher = {
  proc guess(ss : statement, ww: witness, summary: adv_summary) = {
   var guess;
   HybOrcl.l <- HybOrcl.l + 1;
   while (HybOrcl.l <= n) {
    summary <@ Sim(V).simulate(s, n);
    HybOrcl.l <- HybOrcl.l + 1;
   }
   guess <@ D.guess(s, w,  summary);
   return guess;
  }
}.


lemma lll &m deltoid : 
   (forall &n N, 0 <= N =>
   Pr[ZKIdeal(Sim, V, Dstar).run(s, w, N) @ &n : res]
    - Pr[ZKReal(P, V, Dstar).run(s, w) @ &n : res] 
           < deltoid) =>
   Pr[HybGame(A1,Ob1,L(Ob1)).main() @ &m : res]
               - Pr[HybGame(A1,Ob1,R(Ob1)).main() @ &m : res] < deltoid.
move => zk_ass.
have ->: Pr[HybGame(A1,Ob1,L(Ob1)).main() @ &m : res] =
         Pr[MemoryPropsLE.P(Amem).main1() @ &m : res].
rewrite www. rewrite ww. rewrite w.
byequiv. proc. 
inline Amem.run1. inline Amem.init.
wp.  seq 7 7 : (={summary, glob V}). sim. smt.
call D_guess_prop. skip. auto.
auto. auto.
have ->: Pr[HybGame(A1,Ob1,R(Ob1)).main() @ &m : res] =
         Pr[MemoryPropsLE.P(Amem).main2() @ &m : res].
rewrite yyy. rewrite yy. rewrite y.
byequiv. proc. 
inline Amem.run2. inline Amem.init.
wp. seq 10 10 : (={summary, glob V}). sim. smt. 
call D_guess_prop. skip. auto.
auto. auto.
case (Pr[MemoryPropsLE.P(Amem).main1() @ &m : res] -
Pr[MemoryPropsLE.P(Amem).main2() @ &m : res] < deltoid). auto.
move => q.
have zz : Pr[MemoryPropsLE.P(Amem).main1() @ &m : res] -
  Pr[MemoryPropsLE.P(Amem).main2() @ &m : res] >= deltoid. 
smt. clear q.
have ko : exists &n, deltoid <= Pr[Amem.run1() @ &n : res] - Pr[Amem.run2() @ &n : res].
apply (o_o Amem &m).  auto.
elim ko. move => &n. move => q.
have ok : Pr[Amem.run1() @ &n : res] - Pr[Amem.run2() @ &n : res] < deltoid.
have -> : Pr[Amem.run1() @ &n : res] = Pr[ZKIdeal(Sim, V, Dstar).run(s, w, n) @ &n : res].
byequiv. proc.         
inline Dstar.guess. wp.
seq 3 6: (={glob V} /\ summary{1} = summary0{2}). sim. wp.
call (_: ={glob V}). sim. sim. sim. sim. skip. progress. 
smt. smt.
call D_guess_prop. skip. auto.
auto.  auto. 
have -> : Pr[Amem.run2() @ &n : res] = Pr[ZKReal(P, V, Dstar).run(s, w) @ &n : res].
byequiv. proc.         
inline Dstar.guess. wp.
seq 6 9: (={glob V} /\ summary{1} = summary0{2}). sim. wp.
call (_:true). call (_:true).  call (_:true).  call (_:true). skip.
progress. smt. smt. smt.  call D_guess_prop. skip. auto.
auto.  auto. 
apply (zk_ass  &n n _ ). smt. smt.
qed.


module ZKRealAmp(P: HonestProver, V: MaliciousVerifier, D: ZKDistinguisher) = {
  proc run(statement: statement, witness: witness) = {
    var commit, challenge, response, summary, guess,i;
     i <- 0;
     summary <- Pervasive.witness;
     while(i <= n){
       commit <@ P.commitment(statement, witness);
       challenge <@ V.challenge(statement, commit);
       response <@ P.response(challenge);
       summary <@ V.summitup(statement, response);
       i <- i + 1;
     }
    guess <@ D.guess(statement, witness, summary);
    return guess;
  }
}.


module SimAmp(S: Simulator, V : RewMaliciousVerifier) = { 
  proc simulate(statement:statement,N : int) = { 
   var summary, i; 
   i <- 0;
   summary <- witness;
   while(i <= n) { 
     summary <@ S(V).simulate(statement, N); 
     i <- i + 1;
   } 
   return summary; 
  } 
}.


lemma final &m deltoid : 
   (forall &n N, 0 <= N =>
   Pr[ZKIdeal(Sim, V, Dstar).run(s, w, N) @ &n : res]
    - Pr[ZKReal(P, V, Dstar).run(s, w) @ &n : res] 
           < deltoid) =>

   Pr[ZKIdeal(SimAmp(Sim), V, D).run(s, w, n) @ &m : res]
        - Pr[ZKRealAmp(P, V, D).run(s, w) @ &m : res]
          < (n+1)%r * deltoid.
move => zk_ass.
have -> : Pr[ZKIdeal(SimAmp(Sim), V, D).run(s, w, n) @ &m : res]
 = Pr[Ln(Ob,A).main() @ &m : res].
byequiv (_:   
  (glob V){2} = (glob V){m} /\ ={glob Sim}/\
  (statement{1}, witness{1}, n{1}) = (s, w, n) /\
   (glob V){1} = (glob V){m} ==> _). proc. inline*. wp. sp.
seq 2 1 : (={glob V, summary} /\ statement{1} = s{2} /\ witness{1} = w{2}).   simplify. wp.
while (={i, glob V, glob Sim} /\ summary0{1} = summary{2} /\ statement0{1} = s /\   N{1} = ZeroKnowledgeTheory.n).
wp. call (_: ={glob V}). sim. sim. sim. sim. wp.  skip. progress.
 skip. progress.  call D_guess_prop. skip. auto. auto. auto.
have -> : Pr[ZKRealAmp(P, V, D).run(s, w) @ &m : res]
 = Pr[Rn(Ob,A).main() @ &m : res].
byequiv (_: ={glob V, glob P} /\ (statement{1}, witness{1}) = (s, w) ==> _). proc.
inline*. wp. sp.
seq 1 1 : (={glob V, summary} /\ statement{1} = s{2} /\ witness{1} = w{2} ).   simplify. wp.
while (={i, glob V, glob P} /\ summary{1} = summary{2} /\ statement{1} = s /\  witness{1} = w{2}). sp. wp.
call (_:true). call (_:true). call (_:true). call (_:true). skip. progress.
skip. progress. call D_guess_prop. skip.  auto. auto. auto.
rewrite qq.
have :  Pr[HybGame(A1,Ob1,L(Ob1)).main() @ &m : res]
               - Pr[HybGame(A1,Ob1,R(Ob1)).main() @ &m : res] < deltoid.
apply lll. smt. smt.
qed.


end section.

end ZeroKnowledgeTheory.



abstract theory OneShotSimulator.
    op zk_error : statement -> int -> real.


    require OneToManyZK.
    clone import OneToManyZK as OMZK with type prob <- statement,
                                          type wit <- witness,
                                          type sbits <- adv_summary,
                                          type event <- bool,

                                          op E <- (fun x => fst x),
                                          op fevent <- false

   rename "Simulator1" as "Simulator1NP".


    module ZKD(P : HonestProver, V : MaliciousVerifier, D : ZKDistinguisher) = {
      proc main(Ny : statement, w : witness) = {
        var c,b,r,result,rb;
        c <@ P.commitment(Ny,w);
        b <@ V.challenge(Ny,c);
        r <@ P.response(b);
        result <@ V.summitup(Ny,r);
        rb <@ D.guess(Ny,w,result);
        return rb;
      }
    }.



     module  Simulator(S : Simulator1)(V : RewMaliciousVerifier)  = {
       module M = MW.IFB.IM.W(S(V))
       proc simulate(statement : statement, n : int) :
         adv_summary = {
            var r;
            r <@ M.whp(fst, (statement),1,n,(false,witness));
            return r.`2;
       }
     }.


    theory ComputationalZK.

    section.
    op negl : real.

    declare module HonestProver <: HonestProver.
    declare module Sim1 <: Simulator1 {-MW.IFB.IM.W, -MW.IFB.DW}.
    declare module V <: RewMaliciousVerifier {-Sim1, -MW.IFB.IM.W, -HonestProver, -MW.IFB.DW}.
    declare module D <: ZKDistinguisher{ -MW.IFB.DW, -MW.IFB.IM.W} .


    declare axiom sim1_run_ll : forall (V0 <: RewMaliciousVerifier),
         islossless V0.challenge => islossless V0.summitup => islossless Sim1(V0).run.
    declare axiom V_summitup_ll  : islossless V.summitup.
    declare axiom V_challenge_ll : islossless V.challenge.
    declare axiom D_guess_ll     : islossless D.guess.


    declare axiom V_rew :  (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).


    declare axiom sim1_rew_ph : forall (x : (glob Sim1(V))),
                  phoare[ Sim1(V).run : (glob Sim1(V)) = x ==> ! fst res => (glob Sim1(V)) = x] = 1%r.


    declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].

     lemma computational_statisticalVpoly_zk stat wit N p0 negl &m:
        zk_relation stat wit =>

        `|Pr[W0(Sim1(V), D).run(stat, wit) @ &m : fst res.`2 /\ res.`1] /
             Pr[Sim1(V).run(stat) @ &m : fst res]
         - Pr[ ZKD(HonestProver,V,D).main(stat,wit) @ &m : res ]| <= negl =>

        0 <= N =>

        p0 <= Pr[Sim1(V).run(stat) @ &m : res.`1] =>

        let real_prob = Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res] in
          `|real_prob - ideal_prob| <= negl + 2%r * (1%r - p0)^N.
    proof. progress.
    have ->:
     `|Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res] -
      Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res]|
      = `|Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res]
          - Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res]|. smt.
    have ->: Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res]
     = Pr[Iter(Sim1(V), D).run(false,stat,wit,N,fst) @ &m : res.`1].
    byequiv (_:  E{2} = fst  /\ n{1} = ea{2} /\ fevent{2} = false  /\
      statement{1} = Ny{2} /\ witness{1} = w{2} /\
        ={glob Sim1, glob HonestProver,  glob V, glob MW.IFB.IM.W} ==> _)  ;auto.  proc.
    inline Iter(Sim1(V), D).WI.run. wp.  sp. simplify.
     call D_guess_prop.
    simplify. inline Simulator(Sim1,V).simulate. wp. sp.
     
    

    call (_: ={glob Sim1, glob V, glob MW.IFB.IM.W}).  sim. skip. progress.
    progress.
    have ->: Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res]
      = Pr[ ZKD(HonestProver,V,D).main(stat,wit) @ &m : res ].
 
     byequiv (_:   arg{2} = (stat, wit) /\ ={glob V, glob HonestProver}
 /\
  (glob V){2} = (glob V){m} /\
  (glob HonestProver){2} = (glob HonestProver){m} /\
  arg{1} = (stat, wit) /\
 
  (glob V){1} = (glob V){m} /\
  (glob HonestProver){1} = (glob HonestProver){m} ==> _).
  proc. seq  4 4 : (={glob V} /\ (statement{1}, witness{1}, summary{1}) =
  (Ny{2}, w{2}, result{2})). sim. call D_guess_prop. skip. auto. auto. auto.
    apply (one_to_many_zk  (Sim1(V)) D _  _ _ _ _ &m  stat wit p0 negl N
       Pr[ZKD(HonestProver, V, D).main(stat, wit) @ &m : res]  _ _ _).

    conseq D_guess_prop. auto.

    apply (sim1_run_ll V). apply V_challenge_ll. apply V_summitup_ll.
    apply sim1_rew_ph. apply D_guess_ll.
    auto. auto. auto. smt. auto.
    qed.
    end section.
   end ComputationalZK.


   
   theory StatisticalZK.

    op negl : real.

    section.
    declare module HonestProver <: HonestProver.
    declare module Sim1 <: Simulator1 {-MW.IFB.IM.W, -MW.IFB.DW}.
    declare module V <: RewMaliciousVerifier {-Sim1, -MW.IFB.IM.W, -HonestProver, -MW.IFB.DW}.
    declare module D <: ZKDistinguisher{-MW.IFB.IM.W,  -MW.IFB.DW}.

    declare axiom sim1_run_ll : forall (V0 <: RewMaliciousVerifier), islossless V0.challenge
                                  => islossless V0.summitup => islossless Sim1(V0).run.
    declare axiom V_summitup_ll  : islossless V.summitup.
    declare axiom V_challenge_ll : islossless V.challenge.
    declare axiom D_guess_ll     : islossless D.guess.

    declare axiom V_rew :  (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState).


    declare axiom sim1_rew_ph :
         forall (x : (glob Sim1(V))),
                  phoare[ Sim1(V).run : (glob Sim1(V)) = x ==> !fst res => (glob Sim1(V)) = x] = 1%r.

   
    declare axiom qqq &m (p : statement) (w : witness)
      (D <: ZKDistinguisher)
         (V <: RewMaliciousVerifier{-D, -HonestProver}):
       islossless D.guess =>
       islossless V.summitup =>
       islossless V.challenge =>
      (exists (f : glob V -> sbits),
         injective f /\
         (forall &m, Pr[ V.getState() @ &m : (glob V) = ((glob V){m})
                                          /\ res = f ((glob V){m} ) ] = 1%r) /\
         (forall &m b (x: glob V), b = f x =>
           Pr[V.setState(b) @ &m : glob V = x] = 1%r) /\
         islossless V.setState) =>
       zk_relation p w =>
        `|Pr[W0(Sim1(V), D).run(p, w) @ &m : fst res.`2 /\ res.`1] /
             Pr[Sim1(V).run(p) @ &m : fst res]
                  - Pr[ ZKD(HonestProver,V,D).main(p,w) @ &m : res ]| <= negl.


    declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].
    
     lemma statistical_zk stat wit N p0 &m:
        zk_relation stat wit => 0 <= N =>
        p0 <= Pr[Sim1(V).run(stat) @ &m : res.`1] =>
        let real_prob = Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res] in
          `|real_prob - ideal_prob| <= negl + 2%r * (1%r - p0)^N.
    proof. progress.
    have ->:
     `|Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res] -
      Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res]|
      = `|Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res]
          - Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res]|. smt.
    have ->: Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N) @ &m : res]
     = Pr[Iter(Sim1(V), D).run(false,stat,wit,N,fst) @ &m : res.`1].
    byequiv (_:  E{2} = fst /\ n{1} = ea{2} /\ fevent{2} = false  /\
      statement{1} = Ny{2} /\ witness{1} = w{2} /\
        ={glob Sim1, glob HonestProver,  glob V, glob MW.IFB.IM.W} ==> _)  ;auto. proc.
    inline Iter(Sim1(V), D).WI.run. wp.  sp. simplify.
    call D_guess_prop.  simplify. inline Simulator(Sim1,V).simulate. wp. sp.
    call (_: ={glob Sim1, glob V, glob MW.IFB.IM.W}).  sim. skip. progress.
    have ->: Pr[ZKReal(HonestProver, V, D).run(stat, wit) @ &m : res]
      = Pr[ ZKD(HonestProver,V,D).main(stat,wit) @ &m : res ].
byequiv(_: arg{2} = (stat,  wit) /\   arg{1} = (stat, wit) /\  ={glob V, glob HonestProver} ==> _).
proc. call D_guess_prop. sim. auto. auto.
    apply (one_to_many_zk (Sim1(V)) D _ _ _ _ _ &m stat wit p0 negl N
    Pr[ZKD(HonestProver, V, D).main(stat, wit) @
 &m : res]  _ _ _
  ) . conseq D_guess_prop. auto.
  apply (sim1_run_ll V).  apply V_challenge_ll. apply V_summitup_ll. apply sim1_rew_ph. apply D_guess_ll. auto.
    apply (qqq &m stat wit  D V);auto.  apply D_guess_ll. apply V_summitup_ll. apply V_challenge_ll. apply V_rew. apply H0. smt.  auto.
    qed.
   end section.
   end StatisticalZK.
end OneShotSimulator.

