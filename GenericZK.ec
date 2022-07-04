pragma Goals:printall.
require import AllCore List Distr.

theory ZKProtocol.

type statement, witness, commitment, response, challenge,  adv_summary, sbits.
type relation = statement -> witness -> bool.
type transcript = commitment * challenge * response.

op in_language (R:relation) statement : bool = exists witness, R statement witness.
op challenge_set : challenge list. (* axiomitize that! *)

axiom challenge_set_size : 0 < size challenge_set.
op verify_transcript : statement -> transcript -> bool.

op completeness_relation : relation.
op soundness_relation : relation.
op zk_relation : relation.

op valid_transcript_pair (statement: statement) (transcript1 transcript2: transcript) : bool 
   = transcript1.`1 = transcript2.`1 
        /\ transcript1.`2 <> transcript2.`2
        /\ verify_transcript statement transcript1 
        /\ verify_transcript statement transcript2.


module type HonestProver = {
  proc commitment(_:statement*witness) : commitment
  proc response(_:challenge) : response
}.

module type SpecialSoundnessExtractor = {
  proc extract(transcript1: transcript, transcript2: transcript) : witness
}.

module type SpecialSoundnessAdversary = { (* computational *)
  proc attack(statement:statement) : transcript * transcript
}.

module type SpecialSoundnessAdvReduction(A: SpecialSoundnessAdversary) = { (* computational *)
  proc run(statement: statement) : bool
}.

module type HonestVerifier = {
  proc challenge(_:statement*commitment) : challenge
  proc verify(_:statement * transcript) : bool
}.

module type MaliciousProver = {  
  proc commitment(s: statement) : commitment
  proc response(challenge: challenge) : response
}.



module type RewMaliciousProver = {
  proc commitment(s : statement) : commitment 
  proc response(challenge : challenge) : response 
  proc getState() : sbits
  proc * setState(b : sbits) : unit 
}.



module type MaliciousVerifier = {
  proc challenge(_:statement * commitment) : challenge
  proc summitup(statement: statement, response: response) : adv_summary

  proc getState() : sbits
  proc * setState(b : sbits) : unit 
}.

module HonestVerifier : HonestVerifier = {
  var c : commitment

  proc challenge(statement: statement, commitment: commitment) : challenge = {
    var challenge : challenge;
    challenge <$ duniform (challenge_set );
    c <- commitment;
    return challenge;
  }

 proc verify(statement: statement, transcript: transcript) : bool = {
      return verify_transcript statement transcript /\ HonestVerifier.c = transcript.`1;
  }
}.

module Completeness(P: HonestProver, V: HonestVerifier) = {
  proc run(s:statement, w:witness) = {
    var commit, challenge, response, accept;
    commit    <@ P.commitment(s,w);
    challenge <@ V.challenge(s,commit);
    response  <@ P.response(challenge);
    accept    <@ V.verify(s, (commit, challenge, response));
    return accept;
  }
}.

module CompletenessAmp(P: HonestProver, V: HonestVerifier) = { 
  proc run(stat:statement,wit:witness,N:int) = {
    var accept : bool;
    var i : int;
    i <- 0;
    accept <- true; 
    while(i <= N /\ accept) {  
      accept <@ Completeness(P,V).run(stat,wit);
      i <- i + 1;
    } 
    return accept; 
  } 
}. 


module Soundness(P: MaliciousProver, V: HonestVerifier) = {
  proc run(statement: statement) : bool = {
    var commit, challenge, response, accept; 
    commit <@ P.commitment(statement);
    challenge <@ V.challenge(statement,commit);
    response <@ P.response(challenge);
    accept <@ V.verify(statement, (commit, challenge, response));
    return accept;
  }
}.

module SoundnessAmp(P: MaliciousProver, V: HonestVerifier) = { 
  proc run(stat:statement,N:int) = {
    var accept : bool;
    var i : int;
    i <- 0;
    accept <- true; 
    while(i <= N /\ accept) {  
      accept <@ Soundness(P,V).run(stat);
      i <- i + 1;
    } 
    return accept; 
  } 
}. 


module type ZKDistinguisher = {
  proc guess(statement: statement, witness: witness, summary: adv_summary) : bool
}.

module type Simulator(V: MaliciousVerifier) = {
  proc * simulate(statement: statement, n : int) : adv_summary
}.

module type Simulator1(V: MaliciousVerifier) = {
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


    (* TODO note: if we add "init", keep "aux". If we don't add "init", remove aux. *)

module ZKIdeal(S: Simulator, V: MaliciousVerifier, D: ZKDistinguisher) = {
  proc run(statement: statement, witness: witness, n : int) = {
    var summary, guess;
    summary <@ S(V).simulate(statement, n);
    guess <@ D.guess(statement, witness, summary);
    return guess;
  }
}.



abstract theory ZKTheory.

op s:statement.
op w:witness.
op n : int.

axiom zkrel_prop : zk_relation s w.

require Hybrid.
(* q -> N *)
clone import Hybrid as Hyb with type input <- unit,
                                type output <- adv_summary,
                                type outputA <- bool,
                                op q <- n.





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


module Obb(P : HonestProver, V : MaliciousVerifier, Sim : Simulator) = {
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
declare module V <: MaliciousVerifier {-Q, -HybOrcl, -P, -Sim, -Count}.
declare module D <: ZKDistinguisher{-Q, - Count}. 


declare axiom sim_run_ll : forall (V0 <: MaliciousVerifier),  
     islossless V0.challenge => islossless V0.summitup => islossless Sim(V0).simulate.
declare axiom V_summitup_ll  : islossless V.summitup.
declare axiom V_challenge_ll : islossless V.challenge.
declare axiom P_response_ll : islossless P.response.
declare axiom P_commitment_ll : islossless P.commitment.
declare axiom D_guess_ll     : islossless D.guess.

declare axiom q_ge1 : 1 <= n. 

declare axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].

module Ob = Obb(P,V,Sim).
module A = Ad(D).



module Y = {
  proc main() = {
   var summary, guess;
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
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
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
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
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
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
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
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
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
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
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
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
seq 4 4 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l0{2} = HybOrcl.l{2} /\ HybOrcl.l0{2} < n
 /\ HybOrcl.l{2} <= n
   ).
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l{2} <= HybOrcl.l0{2}  /\ HybOrcl.l0{2} < n ). inline*.
sp.
rcondf {1} 1 . progress. skip. smt.
rcondf {1} 1 . progress. skip. smt.    
sp. wp. call (_:true).
call (_:true). call (_:true).
call (_:true). skip. progress. smt. 
wp. rnd. skip. progress.  smt. smt. smt. smt.
rcondt {1} 1. progress. 
seq 1 5 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n /\ HybOrcl.l{2} <= n).
inline HybOrcl(Ob, R(Ob)).orcl. sp. 
rcondf {1} 1. progress. 
rcondt {1} 1. progress. 
inline*.
sp. wp.  
call (_:true). call (_:true).
call (_:true). call (_:true). skip. progress. smt.  smt.
while (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n).
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
seq 4 4 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l0{2} = HybOrcl.l{2} /\ HybOrcl.l0{2} < n
 /\ HybOrcl.l{2} <= n
   ).
while (={glob V, glob P, HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\ HybOrcl.l{2} <= HybOrcl.l0{2}  /\ HybOrcl.l0{2} < n ). inline*.
sp.
rcondf {1} 1 . progress. skip. smt.
rcondf {1} 1 . progress. skip. smt.    
sp. wp. call (_:true).
call (_:true). call (_:true).
call (_:true). skip. progress. smt. 
wp. rnd. skip. progress.  smt. smt. smt. smt.
rcondt {1} 1. progress. 
seq 1 2 : (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n /\ HybOrcl.l{2} <= n).
inline HybOrcl(Ob, L(Ob)).orcl. sp. 
rcondf {1} 1. progress. 
rcondt {1} 1. progress. 
inline*.
sp. wp.  
call (_: ={glob V}). sim. sim. sim. sim. skip. progress. smt. smt.
while (={HybOrcl.l, HybOrcl.l0, glob V, glob P, glob Sim, summary} /\
  HybOrcl.l0{2} < HybOrcl.l{2} /\ HybOrcl.l0{2} < n).
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
    = n%r *(Pr[HybGame(A,Ob,L(Ob)).main() @ &m : res]
            - Pr[HybGame(A,Ob,R(Ob)).main() @ &m : res]).
apply (Hybrid_restr Ob A _ _ _ _ _ &m (fun _ _ _ r => r)).
admit. proc. skip. auto. proc.
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
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
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


  (* semi-main goal *)
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


module SimAmp(S: Simulator, V : MaliciousVerifier) = { 
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
          < n%r * deltoid.
move => zk_ass.
have -> : Pr[ZKIdeal(SimAmp(Sim), V, D).run(s, w, n) @ &m : res]
 = Pr[Ln(Ob,A).main() @ &m : res].
byequiv (_:   
  (glob V){2} = (glob V){m} /\ ={glob Sim}/\
  (statement{1}, witness{1}, n{1}) = (s, w, n) /\
   (glob V){1} = (glob V){m} ==> _). proc. inline*. wp. sp.
seq 2 1 : (={glob V, summary} /\ statement{1} = s{2} /\ witness{1} = w{2}).   simplify. wp.
while (={i, glob V, glob Sim} /\ summary0{1} = summary{2} /\ statement0{1} = s /\   N{1} = ZKTheory.n).
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






module V0(V : MaliciousVerifier) : MaliciousVerifier = {
  proc challenge (stat:statement, c: commitment) : challenge = {
   var commit, challenge, response, summary;
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
   HybOrcl.l <- 0;
   summary <- witness;
     challenge <@ V.challenge(s, c);
     response <@ P.response(challenge);
     summary <@ V.summitup(s, response);
     HybOrcl.l <- HybOrcl.l + 1;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     commit <@ P.commitment(s, w);
     challenge <@ V.challenge(s, commit);
     response <@ P.response(challenge);
     summary <@ V.summitup(s, response);
     HybOrcl.l <- HybOrcl.l + 1;
    }
   commit <@ P.commitment(s, w);
   challenge <@ V.challenge(s, commit);
    
   return challenge;
 } 
  proc summitup(s:statement, r:response)  : adv_summary = {
    var summary;
    summary <@ V.summitup(s,r);
   return summary;
  }
  proc getState() : sbits = { 
   var state;
   state <@ V.getState();
   return state;
  }
  proc setState(s:sbits) : unit = { 
     V.setState(s);
  }
}.


module Sim0(Sim:Simulator)(V:MaliciousVerifier) = {
   module S = Sim(V)
   proc simulate(ss:statement, nn:int) = {

   var commit, challenge, response, summary;
   HybOrcl.l0 <$ [0..max 0 (n - 1)];
   HybOrcl.l <- 0;
   summary <- witness;
   while (HybOrcl.l <= n && HybOrcl.l < HybOrcl.l0) {
     commit <@ P.commitment(s, w);
     challenge <@ V.challenge(s, commit);
     response <@ P.response(challenge);
     summary <@ V.summitup(s, response);
     HybOrcl.l <- HybOrcl.l + 1;
   }

   summary <@ S.simulate(s,n);
   return summary;
     
   }
}.


(* lemma nnn &m deltoid N :  *)
(*       0 <= N => *)
(*    Pr[ZKIdeal(Sim0(Sim), V, Dstar).run(s, w, N, aux) @ &m : res] *)
(*     - Pr[ZKReal(P, V0(V), Dstar).run(s, w, aux) @ &m : res]  *)
(*            < deltoid => *)
(*    Pr[HybGame(A1,Ob1,L(Ob1)).main() @ &m : res] *)
(*                - Pr[HybGame(A1,Ob1,R(Ob1)).main() @ &m : res] < deltoid. *)
(* have ->: Pr[HybGame(A1,Ob1,L(Ob1)).main() @ &m : res] = *)
(*          Pr[MemoryPropsLE.P(Amem).main1() @ &m : res]. *)
(* rewrite www. rewrite ww. rewrite w. *)
(* byequiv. proc.  *)
(* inline Amem.run1. inline Amem.init. *)
(* wp.  seq 7 7 : (={summary, glob V}). sim. smt. *)
(* call D_guess_prop. skip. auto. *)
(* auto. auto. *)
(* have ->: Pr[HybGame(A1,Ob1,R(Ob1)).main() @ &m : res] = *)
(*          Pr[MemoryPropsLE.P(Amem).main2() @ &m : res]. *)
(* rewrite yyy. rewrite yy. rewrite y. *)
(* byequiv. proc.  *)
(* inline Amem.run2. inline Amem.init. *)
(* wp. seq 10 10 : (={summary, glob V}). sim. smt.  *)
(* call D_guess_prop. skip. auto. *)
(* auto. auto. *)
(* progress. *)
(* have ->: Pr[MemoryPropsLE.P(Amem).main1() @ &m : res]  *)
(*   = Pr[ZKIdeal(Sim0(Sim), V, Dstar).run(s, w, N, aux) @ &m : res]. *)
(* byequiv (_:   (statement{2}, witness{2}, n{2}, aux{2}) = (s, w, N, ZKTheory.aux) /\ *)
(*   (glob V){2} = (glob V){m} /\ *)
(*   (glob P){2} = (glob P){m} /\ *)
(*   (glob V){1} = (glob V){m} /\ (glob P){1} = (glob P){m} ==> _). proc. inline Amem.run1. *)
(* inline*. *)
(* swap {2} 4 -3. *)
(* wp. *)
(* seq 7 15 : (={glob V} /\ summary{1} = summary1{2}). sim.  *)
(* call D_guess_prop. auto. auto. auto. *)
(* have ->: Pr[MemoryPropsLE.P(Amem).main2() @ &m : res]  *)
(*   = Pr[ZKReal(P, V0(V), Dstar).run(s, w, aux) @ &m : res] . *)
(* byequiv (_: ={glob P, glob V} /\ arg{2} = (s,w,aux) ==> _). proc. *)
(* inline {1} Amem.init. inline V0(V).challenge. swap {2} 5 -4. *)
(* inline Amem.run2. *)
(* unroll {1} 4. *)
(* rcondt {1} 4.   admit. *)
(* inline*. wp. seq 15 26 : (={glob V} /\ summary0{1} = summary2{2}). sim. *)
(* call (_:true). wp. call (_:true). wp. call (_:true). wp. call (_:true). wp.  *)
(* while(={glob V, glob P, glob HybOrcl} /\  challenge{1} = challenge0{2} /\ response{1} = response0{2} *)
(*  /\ summary{1} = summary0{2}  ). *)
(* wp. call (_:true). wp. call (_:true). wp. call (_:true). wp. call (_:true). wp.  skip. progress.  *)
(* wp. wp. call (_:true). wp. call (_:true). wp. call (_:true). wp. call (_:true). wp.   *)
(* rnd. skip. progress.  *)
(* call D_guess_prop. auto. auto. auto.  auto. *)
(* qed. *)


end section.




end ZKTheory.

abstract theory CompletenessTheory.


require WhileNotBProc.
clone import WhileNotBProc as WNBP with type rt <- bool,
                                        type iat <- statement * witness.

section.

declare module P <: HonestProver{-M, -HonestVerifier}.
declare module V <: HonestVerifier{-M, -P}.

declare axiom verify_ll : islossless V.verify.
declare axiom challenge_ll : islossless V.challenge.
declare axiom response_ll : islossless P.response.
declare axiom commitment_ll : islossless P.commitment.

lemma completeness_amp &m statement witness n deltoid:
     completeness_relation statement witness  =>
   (forall &n,
      Pr[Completeness(P,V).run(statement, witness) @ &n : res]
         >= deltoid) =>
     0 <= n =>
     Pr[CompletenessAmp(P, V).run(statement, witness,n) @ &m : res]
     >= deltoid ^ (n + 1).                                        
proof. 
move => nil cb  nz.
have phs : phoare[ Completeness(P,V).run : arg = (statement,witness) ==> res ] >= deltoid.
bypr. progress. 
have  ->: Pr[Completeness(P, V).run(s{m0},w{m0}) @ &m0 :
   res] = Pr[Completeness(P, V).run(statement, witness) @ &m0 :
   res]. smt.
apply cb.
have ->: Pr[CompletenessAmp(P, V).run(statement, witness, n) @ &m : res]    
 = Pr[ M(Completeness(P,V)).whp((statement,witness), fun x => !x,1,n+1, true) @ &m :  res ].
byequiv (_: ={glob P, glob V} /\  arg{1} = (statement, witness, n) /\ arg{2} = ((statement,witness), fun x => !x,1,n+1, true)  ==> _).  
proc.   sp.
while (i{1} + 1 = M.c{2} /\ N{1} + 1 = e{2} /\ accept{1} = !MyP{2} r{2} /\ ={glob P, glob V}
  /\ (i{2}, MyP{2}, s{2}, e{2}) =
  ((stat{1}, wit{1}), fun (x : bool) => !x, 1, N{1}+1)  ).
wp.  call (_: ={glob P, glob V}).
sim. skip. progress. smt. smt.
skip. progress.  smt. smt.
auto.  auto.
byphoare (_: arg = ((statement, witness), fun (x : bool) => !x,
                                       1, n + 1, true) ==> _).
apply (asdsadq_ge (Completeness(P,V))). 
proc.
call verify_ll. call response_ll. call challenge_ll. call commitment_ll. skip. auto.
apply phs. auto. 
auto. auto. auto.
qed.

     

end section.

end CompletenessTheory.


abstract theory SoundnessTheory.

require WhileNotBProc.
clone import WhileNotBProc as WNBP with type rt <- bool,
                                        type iat <- statement.


section.

declare module P <: MaliciousProver {- M, - HonestVerifier}.

  (* are these needed? after all we are proving <= probability *)
declare axiom verify_ll : islossless HonestVerifier.verify.
declare axiom challenge_ll : islossless HonestVerifier.challenge.
declare axiom response_ll : islossless P.response.
declare axiom commitment_ll : islossless P.commitment.






lemma soundness_amp &m statement n deltoid:
    ! in_language soundness_relation statement =>

   (forall &n,
     Pr[Soundness(P, HonestVerifier).run(statement) @ &n : res]
        <= deltoid) =>

     0 <= n =>
     Pr[SoundnessAmp(P, HonestVerifier).run(statement, n) @ &m : res]
     <= deltoid ^ (n + 1).
proof.
move => nil sa nz.
have phs : phoare[ Soundness(P,HonestVerifier).run : arg = (statement) ==> res ] <= deltoid.
bypr. move => &m0 H. 
rewrite H. simplify. apply sa. 
have ->: Pr[SoundnessAmp(P, HonestVerifier).run(statement, n) @ &m : res]    
 = Pr[ M(Soundness(P,HonestVerifier)).whp((statement), fun x => !x,1,n+1, true) @ &m :  res ].
byequiv (_: ={glob P, glob HonestVerifier} /\  arg{1} = (statement, n) /\ arg{2} = ((statement), fun x => !x,1,n+1, true)  ==> _).  
proc.   sp.
while (i{1} + 1 = M.c{2} /\ N{1} + 1 = e{2} /\ accept{1} = !MyP{2} r{2} /\ ={glob P, glob HonestVerifier}
  /\ (i{2}, MyP{2}, s{2}, e{2}) =
  ((stat{1}), fun (x : bool) => !x, 1, N{1}+1)  ).
wp.  call (_: ={glob P, glob HonestVerifier}).
sim. skip. progress. smt. smt.
skip. progress.  smt. smt.
auto.  auto.
byphoare (_: arg = ((statement), fun (x : bool) => !x,
                                       1, n + 1, true) ==> _).
apply (asdsadq_le (Soundness(P,HonestVerifier))). 
proc.
call verify_ll. call response_ll. call challenge_ll. call commitment_ll. skip. auto.
apply phs. auto. 
auto. auto. auto.
qed.

end section.

end SoundnessTheory.







  abstract theory CompletenessStatement.

  op completeness_error : real.

  axiom completeness: 
      exists (HonestProver <: HonestProver),
      forall (statement:statement) (witness:witness) &m,
      completeness_relation statement witness =>
      Pr[Completeness(HonestProver,HonestVerifier).run(statement, witness) @ &m : res] 
           >= 1%r - completeness_error.

  end CompletenessStatement.

  abstract theory SpecialSoundnessStatements. (* Special soundness *)

  op special_soundness_extract : statement -> transcript -> transcript -> witness.

    abstract theory PerfectSpecialSoundnessStatement. (* Special soundness (perfect) *)

    axiom perfect_special_soundness (statement:statement) (transcript1 transcript2: transcript):
        valid_transcript_pair statement transcript1 transcript2
        =>
        soundness_relation statement (special_soundness_extract statement transcript1 transcript2).
    end PerfectSpecialSoundnessStatement.   


    abstract theory ComputationalSpecialSoundnessStatement.
    op special_soundness_red_function : statement -> real -> real.
    abstract theory ExampleStatement.
    axiom computational_special_soundness:
          exists (SpecialSoundnessAdvReduction <: SpecialSoundnessAdvReduction),
          forall statement &m,
          forall (SpecialSoundnessAdversary <: SpecialSoundnessAdversary),
        let attack_prob = Pr[SpecialSoundnessAdversary.attack(statement) @ &m :
          valid_transcript_pair statement res.`1 res.`2
          /\ ! soundness_relation statement (special_soundness_extract statement res.`1 res.`2)] in
        let red_prob = Pr[SpecialSoundnessAdvReduction(SpecialSoundnessAdversary).run(statement) @ &m : res] in
        attack_prob <= special_soundness_red_function statement red_prob.
    end ExampleStatement.

    end ComputationalSpecialSoundnessStatement.

  end SpecialSoundnessStatements.


  


  (* Proof of knowledge *)
  abstract theory PoK.

  module type Extractor(P: RewMaliciousProver) = {
    proc extract(statement: statement) : witness
  }.

    abstract theory ComputationalPoK.

    op special_soundness_extract : statement -> transcript -> transcript -> witness.

    clone import SpecialSoundnessStatements with op special_soundness_extract <- special_soundness_extract.
    

    module type ExtractionReduction(P: MaliciousProver) = {
      proc run(statement: statement) : bool
    }.


module SpecialSoundnessAdversary(P : RewMaliciousProver) : SpecialSoundnessAdversary = {
  proc attack(statement : statement) : transcript * transcript = {
    var i,c1,c2,r1,r2, pstate;
    i <@ P.commitment(statement);


    c1 <$ duniform challenge_set;
    pstate <@ P.getState();
    r1 <@ P.response(c1);

    c2 <$ duniform challenge_set;
    P.setState(pstate);
    r2 <@ P.response(c2);
    return ((i,c1,r1), (i,c2,r2));
  }
}.

    
module (Extractor : Extractor)(P : RewMaliciousProver) = {  
  module SA = SpecialSoundnessAdversary(P)
  proc extract(p : statement) : witness = {
    var t1,t2;
    (t1,t2) <@ SA.attack(p);
    return special_soundness_extract p t1 t2;
 }
}.

    require GenericKE.
    clone import GenericKE as GKE with type pt <- statement,
                                       type auxt <- unit,
                                        type irt <- commitment,
                                        type ct <- challenge,
                                        type rt <- response,
                                        type sbits <- sbits,
                                        op d <- duniform challenge_set,
                                        op allcs <- challenge_set.

    section.

    declare module P <: RewMaliciousProver{-HonestVerifier}.
    
    declare axiom P_response_ll : islossless P.response.

    local module A(P : RewMaliciousProver) : Adv = {
      proc init (p : statement,x:unit) : commitment = {
        var i : commitment;
        i <@ P.commitment(p);
        return i;
     }

     proc run(hcm : commitment, hcc: challenge) : response = {
       var r;
       r <@ P.response(hcc);
       return r;
     }
     proc getState = P.getState
     proc setState = P.setState
    }.


   op hc_verify = fun s cm ch rs => verify_transcript s (cm , ch, rs). (* TODO: remove later *)

      local lemma ex_a_eq_f &m p aux f : 
    Pr[ InitRun2(A(P)).run(p,aux) @ &m 
             : res.`1.`1 <> res.`2.`1  /\
               hc_verify p res.`1.`2.`2 res.`1.`1 res.`1.`2.`1  /\
               hc_verify p res.`2.`2.`2 res.`2.`1 res.`2.`2.`1  /\
     f (soundness_relation  p (special_soundness_extract p (res.`1.`2.`2, res.`1.`1, res.`1.`2.`1) 
                                            (res.`2.`2.`2, res.`2.`1, res.`2.`2.`1))) ] 
     = Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                valid_transcript_pair p res.`1 res.`2 /\
                 f  (soundness_relation  p (special_soundness_extract p res.`1 res.`2))].
   proof. byequiv;auto.
   proc. simplify. inline*. wp.  call (_:true).  wp.  call (_:true). rnd. wp.
     call (_:true). wp.  call (_:true). rnd. wp. call (_:true). wp.  skip. progress.
   smt.  smt. smt. smt. smt. smt.
   qed.
   

    local lemma hc_pok' &m p aux deltoid : 
       Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                 valid_transcript_pair p res.`1 res.`2 /\
                 ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <= deltoid
           =>

      Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                 valid_transcript_pair p res.`1 res.`2 /\
                  soundness_relation p (special_soundness_extract p res.`1 res.`2)]
        >= (Pr[ InitRun1(A(P)).run(p,aux) @ &m  : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]^2
             - (1%r/ (size (challenge_set ) ) %r) * Pr[ InitRun1(A(P)).run(p,aux) @ &m : hc_verify p res.`2.`2 res.`1 res.`2.`1 ])
              - deltoid.
    proof. rewrite -  (ex_a_eq_f &m p aux).
    move => f. simplify.
     rewrite -  (ex_a_eq_f &m p aux (fun x => x) ).
    apply (final_eq_step1 (A(P)) _ &m (fun pq (r : challenge * (response * commitment)) => hc_verify (fst pq) r.`2.`2 r.`1 r.`2.`1) (fun (pq :statement * unit) (r1 r2 : challenge * (response * commitment)) => soundness_relation (fst pq) (special_soundness_extract (fst pq) (r1.`2.`2, r1.`1, r1.`2.`1) (r2.`2.`2, r2.`1, r2.`2.`1)))
      (p, aux)
     deltoid
    _
    ). proc. call P_response_ll;auto.
   auto. 
    qed.


    local lemma qqq &m p : 
      Pr[SpecialSoundnessAdversary(P).attack(p) @ &m :
           valid_transcript_pair p res.`1 res.`2 /\
           soundness_relation p (special_soundness_extract p res.`1 res.`2)]
     <=  Pr[Extractor(P).extract(p) @ &m : soundness_relation p res].
    byequiv. proc.  inline*. wp. call (_:true).
      call (_:true).  rnd. call (_:true). call (_:true).
    rnd. call (_:true). wp.  skip. progress. auto. auto.
    qed.



    local lemma www &m p aux: 
      Pr[ InitRun1(A(P)).run(p,aux) @ &m 
          : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]
     = Pr[Soundness(P, HonestVerifier).run(p) @ &m : res].
    byequiv. proc. inline*. wp. call (_:true).
    wp. rnd.  wp. call (_:true). wp.  
    skip. simplify. progress. auto. auto. 
    qed.



    (* "copy/include/or move"  to special soundness theory (where the spec. sound. axiom is assumed)  *)
    lemma computational_PoK &m p deltoid: 
          Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <=
             deltoid =>
      Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] >=
       (Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]^2
       - (1%r/ (size challenge_set)%r) * Pr[Soundness(P, HonestVerifier).run(p) @ &m : res])
         - deltoid.
    progress.
    have f : Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                 valid_transcript_pair p res.`1 res.`2 /\
                  soundness_relation p (special_soundness_extract p res.`1 res.`2)]
        >= (Pr[ InitRun1(A(P)).run(p,tt) @ &m  : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]^2
             - (1%r/ (size (challenge_set ) ) %r) * Pr[ InitRun1(A(P)).run(p,tt) @ &m : hc_verify p res.`2.`2 res.`1 res.`2.`1 ])
              - deltoid. apply (hc_pok' &m p). auto.
    timeout 20.  

    have g :       Pr[ InitRun1(A(P)).run(p,tt) @ &m 
          : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]
     = Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]. apply www.

     have j :       Pr[SpecialSoundnessAdversary(P).attack(p) @ &m :
           valid_transcript_pair p res.`1 res.`2 /\
           soundness_relation p (special_soundness_extract p res.`1 res.`2)]
     <=  Pr[Extractor(P).extract(p) @ &m : soundness_relation p res].
    apply qqq.

     smt.
    qed.


    lemma statistical_PoK &m p :
      (! exists t1 t2, valid_transcript_pair p t1 t2 /\ ! soundness_relation p (special_soundness_extract p t1 t2))

      =>

      Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] >=
       (Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]).
    proof.  progress.
      have vte : forall t1 t2, valid_transcript_pair p t1 t2 =>  soundness_relation p (special_soundness_extract p t1 t2). smt.

      have f : Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] = 0%r.  
     have -> : 0%r = Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m : false]. smt.
    rewrite Pr[mu_eq]. smt. auto. apply (computational_PoK &m p 0%r). rewrite f. auto.
    qed.
          




    require import Real RealExp.
    lemma qqq1  (a b : real) : a <= b  => sqrt a <= sqrt b.
    smt. qed.
    lemma qqq2  (a b : real) : a ^ 2 <= b  => a <= sqrt b.
    smt. qed.


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


  
    lemma computational_soundness &m p  deltoid:
        ! in_language soundness_relation p =>
       Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <=
            deltoid =>
         Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]
         <=  (sqrt deltoid) + (1%r/ (size (challenge_set))%r).
    proof. progress.
    have f1 : Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] = 0%r.
      have <-: Pr[Extractor(P).extract(p) @ &m : false ] = 0%r.
      rewrite Pr[mu_false]. auto.
    rewrite Pr[mu_eq]. smt. auto.
    have  :   0%r >=
       (Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HonestVerifier).run(p) @ &m : res])
         - deltoid.
     rewrite - f1.
    apply (computational_PoK &m p). auto. 
    pose a := Pr[Soundness(P, HonestVerifier).run(p) @ &m : res].
    pose b := deltoid.
    have f2 : 0%r <= a <= 1%r. smt.
    progress.     
    have f3 : a ^ 2 - 1%r / (size challenge_set)%r * a  <= b.  smt.
    have f4 : a * (a - 1%r / (size challenge_set)%r)  <= b.  smt.

    case (a < 1%r / (size challenge_set)%r). smt. progress.
   have f51:  (a >= 1%r / (size challenge_set)%r). smt.
   have f52:  (a - 1%r / (size challenge_set)%r) <= a. smt.

   have f54 :  0%r <= a. smt.
   have f53:  (a - 1%r / (size challenge_set)%r) * (a - 1%r / (size challenge_set)%r) <= a * (a - 1%r / (size challenge_set)%r). 
   smt.

    have f5 : (a - 1%r / (size challenge_set)%r)^2  <= b.  smt.
   smt. qed.


         (*  depending on the size of challenge_set either computational_soundness or computational_soundness_II provide a better bound *)
    lemma computational_soundness_II &m p deltoid:
        ! in_language soundness_relation p =>
       Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <=
            deltoid =>
         Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]
         <=  ((size (challenge_set))%r * deltoid) + (1%r/ (size (challenge_set))%r).
    proof. progress.
    have f1 : Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] = 0%r.
      have <-: Pr[Extractor(P).extract(p) @ &m : false ] = 0%r.
      rewrite Pr[mu_false]. auto.
    rewrite Pr[mu_eq]. smt. auto.
    have  :   0%r >=
       (Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HonestVerifier).run(p) @ &m : res])
         - deltoid.
     rewrite - f1.
    apply (computational_PoK &m p). auto. 
    pose a := Pr[Soundness(P, HonestVerifier).run(p) @ &m : res].
    pose b := deltoid.
    pose c := (size challenge_set)%r.
    have f2 : 0%r <= a <= 1%r. smt.
    progress.     
    have f3 : a ^ 2 - 1%r / c * a  <= b.  smt.
    have f4 : a * (a - 1%r /c)  <= b.  smt.

   case (a < 1%r /c). smt. progress.
   have f51:  (a >= 1%r / c). smt.
   have f52:  (a - 1%r / c) <= a. smt.
   have f54 :  0%r <= a. smt.

   have f6 : a * c * (a - 1%r / c) <= b * c. smt.
   have f7 : (1%r/c) * c * (a - 1%r / c) <= b * c. smt.
   have f8 : (a - 1%r / c) <= b * c. smt.
   have f9 : a  <= b * c + 1%r/c. smt.

   smt (challenge_set_size). qed.

    
    lemma statistical_soundness &m p  :
        ! in_language soundness_relation p =>
      (! exists t1 t2, valid_transcript_pair p t1 t2 /\ ! soundness_relation p (special_soundness_extract p t1 t2)) =>
         Pr[Soundness(P, HonestVerifier).run(p) @ &m : res]
         <=  ((1%r/ (size (challenge_set))%r)).
     
     proof. progress. 
       have ->: inv (size challenge_set)%r = sqrt 0%r + inv (size challenge_set)%r. smt.

    apply (computational_soundness &m p  0%r H _).
      have -> : Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] = 0%r.  
     have -> : 0%r = Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m : false]. smt.
    rewrite Pr[mu_eq]. smt. auto.   auto. qed.



    end section.


    abstract theory Example.
    op computationally_extractable_function : statement -> real -> real.
    axiom computationally_extractable:
        exists (Extractor <: Extractor),
        exists (ExtractionReduction <: ExtractionReduction),
        forall statement &m,
        forall (MaliciousProver <: RewMaliciousProver),
        let verify_prob = Pr[Soundness(MaliciousProver, HonestVerifier).run(statement) @ &m : res] in
        let extract_prob = Pr[Extractor(MaliciousProver).extract(statement) @ &m 
                 : soundness_relation statement res] in
        let red_prob = Pr[ExtractionReduction(MaliciousProver).run(statement) @ &m : res] in
        extract_prob >= computationally_extractable_function statement verify_prob - red_prob. 
    end Example.

    end ComputationalPoK.


    abstract theory StatisticalPoK.

    op extraction_success_function : statement -> real -> real.

    axiom statistically_extractable:
        exists (Extractor <: Extractor),
        forall statement  &m,
        forall (P <: RewMaliciousProver),
        let verify_prob = Pr[Soundness(P, HonestVerifier).run(statement) @ &m : res] in
        let extract_prob = Pr[Extractor(P).extract(statement) @ &m : soundness_relation statement res] in
        extract_prob >= extraction_success_function statement verify_prob.

    end StatisticalPoK.

  end PoK.


(* ZK *)
  abstract theory ZK.
  
  
    abstract theory ComputationalZK. (* Computational ZK *)

    op zk_red_function : statement -> real -> real.

    module type ZKReduction(V: MaliciousVerifier, D: ZKDistinguisher) = {
      proc run(statement: statement, witness: witness) : bool
    }.

    axiom computational_zk:
        exists (HonestProver <: HonestProver),
        exists (Simulator <: Simulator),
        exists (ZKReduction <: ZKReduction),
        forall statement witness n &m,
        forall (MaliciousVerifier <: MaliciousVerifier),
        forall (Distinguisher <: ZKDistinguisher),
        zk_relation statement witness
        =>
        let real_prob = Pr[ZKReal(HonestProver, MaliciousVerifier, Distinguisher).run(statement, witness) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator, MaliciousVerifier, Distinguisher).run(statement, witness, n) @ &m : res] in
        let red_prob = Pr[ZKReduction(MaliciousVerifier, Distinguisher).run(statement, witness) @ &m : res] in
          `|real_prob - ideal_prob| <= zk_red_function statement red_prob.

    end ComputationalZK.


    abstract theory StatisticalZK.
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



     module  Simulator(S : Simulator1)(V : MaliciousVerifier)  = {
       module M = MW.IFB.IM.W(S(V))
       proc simulate(statement : statement, n : int) :
         adv_summary = {
            var r;
            r <@ M.whp(fst, (statement),1,n,(false,witness));
            return r.`2;
       }
     }.


    theory ComputationalStatisticalZKDeriv.

    section.
    op negl : real.

    declare module HonestProver <: HonestProver.
    declare module Sim1 <: Simulator1 {-MW.IFB.IM.W, -MW.IFB.DW}.
    declare module V <: MaliciousVerifier {-Sim1, -MW.IFB.IM.W, -HonestProver, -MW.IFB.DW}.
    declare module D <: ZKDistinguisher {-MW.IFB.IM.W, -MW.IFB.DW}. 


    declare axiom sim1_run_ll : forall (V0 <: MaliciousVerifier),  
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
       Pr[ZKD(HonestProver, V, D).main(stat, wit) @ &m : res]  _ _ _).   conseq D_guess_prop. auto.
    apply (sim1_run_ll V). apply V_challenge_ll. apply V_summitup_ll. 
    apply sim1_rew_ph. apply D_guess_ll. 
    auto. auto. auto.  smt. auto.
    qed.
    end section.
   end ComputationalStatisticalZKDeriv.

   
   theory StatisticalZKDeriv.

    op negl : real.

    section.
    declare module HonestProver <: HonestProver.
    declare module Sim1 <: Simulator1 {-MW.IFB.IM.W, -MW.IFB.DW}.
    declare module V <: MaliciousVerifier {-Sim1, -MW.IFB.IM.W, -HonestProver, -MW.IFB.DW}.
    declare module D <: ZKDistinguisher{-MW.IFB.IM.W, -MW.IFB.DW}. 

    declare axiom sim1_run_ll : forall (V0 <: MaliciousVerifier), islossless V0.challenge 
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
         (V <: MaliciousVerifier{-D, -HonestProver}): 
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


    axiom D_guess_prop : equiv[ D.guess ~ D.guess : ={glob V, arg} ==> ={res} ].
    
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
    Pr[ZKD(HonestProver, V, D).main(stat, wit) @ &m : res]  _ _ _
  ) . conseq D_guess_prop. auto.
  apply (sim1_run_ll V).  apply V_challenge_ll. apply V_summitup_ll. apply sim1_rew_ph. apply D_guess_ll. auto.  
    apply (qqq &m stat wit  D V);auto.  apply D_guess_ll. apply V_summitup_ll. apply V_challenge_ll. apply V_rew. apply H0. smt. auto.
    qed.
   end section.
   end StatisticalZKDeriv.
   end StatisticalZK.
  end ZK.
end ZKProtocol.


