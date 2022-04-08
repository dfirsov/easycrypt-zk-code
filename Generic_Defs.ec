require import AllCore.
require import FSet.
require import Distr.

theory ZKProtocol.
section.

  (* TODO: In all module types, make the first proc an init-proc ("proc *") *)

type statement.
type witness.
type commitment.
type response.
type challenge.
type auxiliary_input.

type relation = statement -> witness -> bool.
op in_language (R:relation) statement : bool = exists witness, R statement witness.

module type HonestProver = {
  proc commitment(s:statement, w:witness) : commitment
  proc response(challenge: challenge) : response
}.

declare module HonestProver : HonestProver.

op challenge_set : statement -> challenge fset.

  (* Axiom: challenge_set has no duplicates, nonempty *)

type transcript = commitment * challenge * response.

op verify_transcript : statement -> transcript -> bool.

module type HonestVerifier = {
  proc challenge(statement: statement) : challenge
  proc verify(statement: statement, transcript: transcript) : bool
}.

module HonestVerifier : HonestVerifier = {
  proc challenge(statement: statement) : challenge = {
    var challenge : challenge;
    challenge <$ duniform (elems (challenge_set statement));
    return challenge;
  }
      proc verify(statement: statement, transcript: transcript) : bool = {
return verify_transcript statement transcript;
    }
}.

    (* module type Protocol = HonestProver * HonestVerifier *)


    (* Honest Verifier is given implicitly through the ops. *)
module Completeness(P: HonestProver, V: HonestVerifier) = {
  proc run(statement:statement, witness:witness) = {
    var commit, challenge, response, accept;
    commit <@ P.commitment(statement,witness);
    challenge <@ V.challenge(statement);
    response <@ P.response(challenge);
    accept <@ V.verify(statement, (commit, challenge, response));
    return accept;
  }
}.




  (* TODO: Play with theory inheritance below. *)

  (* Example lemma *)
op completeness_relation : relation.
  (* This one is not needed, just use completeness_error = 0. *)
lemma perfect_completeness (statement:statement) (witness:witness) &m:
    completeness_relation statement witness
    =>
    Pr[Completeness(HonestProver,HonestVerifier).run(statement, witness) @ &m : res] = 1%r.
      admitted.


(* Example lemma *)
op completeness_error : real.
lemma statistical_completeness (statement:statement) (witness:witness) &m:
    completeness_relation statement witness
    =>
    Pr[Completeness(HonestProver,HonestVerifier).run(statement, witness) @ &m : res] >= 1%r - completeness_error.
      admitted.
    

      (* Special soundness *)
op soundness_relation : relation.
module type SpecialSoundnessExtractor = {
  proc extract(transcript1: transcript, transcript2: transcript) : witness
}.      

op valid_transcript_pair (statement: statement) (transcript1: transcript) (transcript2: transcript) : bool =
  transcript1.`1 = transcript2.`1 /\ transcript1.`2 <> transcript2.`2
  /\ verify_transcript statement transcript1 /\ verify_transcript statement transcript2.

  (* Special soundness (perfect) *)
(* declare module SpecialSoundnessExtractor : SpecialSoundnessExtractor. *)

op special_soundness_extract : statement -> transcript -> transcript -> witness.

lemma perfect_special_soundness (statement:statement) (transcript1: transcript) (transcript2: transcript) &m:
    valid_transcript_pair statement transcript1 transcript2
    =>
    soundness_relation statement (special_soundness_extract statement transcript1 transcript2).
admitted.
    
    
      (* Special soundness (computational) *)

module type SpecialSoundnessAdversary = {
  proc attack(statement:statement, aux:auxiliary_input) : transcript * transcript
}.

(* Maybe not used explicitly. But SpecialSoundnessAdvReduction inherits from it *)
(* module type Game = {
  proc run() : bool
}. *)

module type SpecialSoundnessAdvReduction(A: SpecialSoundnessAdversary) = {
  proc run(statement: statement, aux: auxiliary_input) : bool
}.

declare module SpecialSoundnessAdvReduction : SpecialSoundnessAdvReduction. (* Give it to me (when instantiating thy) *)
declare module SpecialSoundnessAdversary : SpecialSoundnessAdversary. (* Don't give it to me. *)


op special_soundness_red_function : statement -> real -> real.

lemma computational_special_soundness statement aux &m :
    let attack_prob = Pr[SpecialSoundnessAdversary.attack(statement, aux) @ &m :
      valid_transcript_pair statement res.`1 res.`2
      /\ ! soundness_relation statement (special_soundness_extract statement res.`1 res.`2)] in
    let red_prob = Pr[SpecialSoundnessAdvReduction(SpecialSoundnessAdversary).run(statement, aux) @ &m : res] in
    attack_prob <= special_soundness_red_function statement red_prob. 
admitted.

    (* Soundness *)

module type MaliciousProver = {          (* SoundnessAdv *)
  proc commitment(s: statement, aux: auxiliary_input) : commitment
  proc response(challenge: challenge) : response
}.

module Soundness(P: MaliciousProver, V: HonestVerifier) = {
  proc run(statement: statement, aux: auxiliary_input) : bool = {
    var commit, challenge, response, accept;
    commit <@ P.commitment(statement, aux);
    challenge <@ V.challenge(statement);
    response <@ P.response(challenge);
    accept <@ V.verify(statement, (commit, challenge, response));
    return accept;
  }
}.

    (* Statistical soundness *)

  (* Maybe abbrev for in_language soundness_relation *)
op soundness_error : statement -> real.

lemma statistical_soundness (P <: MaliciousProver) statement aux &m:
    ! in_language soundness_relation statement
    =>
    Pr[Soundness(P, HonestVerifier).run(statement, aux) @ &m : res]
      <= soundness_error statement.
admitted.

      (* Computational soundness *)

module type SoundnessReduction(P: MaliciousProver) = {
  proc run(statement: statement, aux: auxiliary_input) : bool
}.

declare module SoundnessReduction : SoundnessReduction. (* Give it to me (when instantiating thy) *)
declare module MaliciousProver : MaliciousProver. (* Don't give it to me. *)


op soundness_red_function : statement -> real -> real.

lemma computational_soundness statement aux &m :
    let attack_prob = Pr[Soundness(MaliciousProver, HonestVerifier).run(statement, aux) @ &m : res] in
    let red_prob = Pr[SoundnessReduction(MaliciousProver).run(statement, aux) @ &m : res] in
    attack_prob <= soundness_red_function statement red_prob. 
admitted.


    (* Proof of knowledge *)

module type Extractor(P: MaliciousProver) = {
  proc extract(statement: statement, aux: auxiliary_input) : witness
}.

declare module Extractor : Extractor.

op extraction_success_function : statement -> real -> real.


lemma statistically_extractable (P <: MaliciousProver) statement aux &m:
    let verify_prob = Pr[Soundness(P, HonestVerifier).run(statement, aux) @ &m : res] in
    let extract_prob = Pr[Extractor(P).extract(statement, aux) @ &m : soundness_relation statement res] in
    extract_prob >= extraction_success_function statement verify_prob.
admitted.


module type ExtractionReduction(P: MaliciousProver) = {
  proc run(statement: statement, aux: auxiliary_input) : bool
}.

declare module ExtractionReduction : ExtractionReduction.
    
lemma computationally_extractable (* or computational_pok *) statement aux &m:
    let verify_prob = Pr[Soundness(MaliciousProver, HonestVerifier).run(statement, aux) @ &m : res] in
    let extract_prob = Pr[Extractor(MaliciousProver).extract(statement, aux) @ &m : soundness_relation statement res] in
    let red_prob = Pr[ExtractionReduction(MaliciousProver).run(statement, aux) @ &m : res] in
    true.  (* Actually should be something relating extract_prob, verify_prob, red_prob *)
admitted.

    (* ZK *)

type adv_summary.
    
module type MaliciousVerifier = {
  proc challenge(statement: statement, aux: auxiliary_input) : challenge
  proc summitup(statement: statement, response: response) : adv_summary
}.

module type Distinguisher = {
  proc guess(statement: statement, witness: witness, aux: auxiliary_input, summary: adv_summary) : bool
}.


module ZKReal(P: HonestProver, V: MaliciousVerifier, D: Distinguisher) = {
  proc run(statement: statement, witness: witness, aux: auxiliary_input) = {
    var commit, challenge, response, summary, guess;
    commit <@ P.commitment(statement, witness);
    challenge <@ V.challenge(statement, aux);
    response <@ P.response(challenge);
    summary <@ V.summitup(statement, response);
    guess <@ D.guess(statement, witness, aux, summary);
    return guess;
  }
}.

module type Simulator(V: MaliciousVerifier) = {
  proc * simulate(statement: statement, aux: auxiliary_input) : adv_summary
}.

module ZKIdeal(S: Simulator, V: MaliciousVerifier, D: Distinguisher) = {
  proc run(statement: statement, witness: witness, aux: auxiliary_input) = {
    var summary, guess;
    summary <@ S(V).simulate(statement, aux);
    guess <@ D.guess(statement, witness, aux, summary);
    return guess;
  }
}.

declare module Distinguisher : Distinguisher.

  (* Computational ZK *)


module type ZKReduction(V: MaliciousVerifier, D: Distinguisher) = {
  proc run(statement: statement, witness: witness, aux: auxiliary_input) : bool
}.

op zk_relation : relation.

declare module MaliciousVerifier : MaliciousVerifier.

declare module Simulator : Simulator. (* Give it to me! *)

declare module ZKReduction : ZKReduction. (* Give it to me! *)

op zk_red_function : statement -> real -> real.

lemma computational_zk statement witness aux &m:
    zk_relation statement witness
    =>
    let real_prob = Pr[ZKReal(HonestProver, MaliciousVerifier, Distinguisher).run(statement, witness, aux) @ &m : res] in
    let ideal_prob = Pr[ZKIdeal(Simulator, MaliciousVerifier, Distinguisher).run(statement, witness, aux) @ &m : res] in
    let red_prob = Pr[ZKReduction(MaliciousVerifier, Distinguisher).run(statement, witness, aux) @ &m : res] in

      `|real_prob - ideal_prob| <= zk_red_function statement red_prob.
admitted.

module type ZKReduction1(V: MaliciousVerifier) = {
  proc run(statement: statement, witness: witness, aux: auxiliary_input) : bool
}.

declare module ZKReduction1 : ZKReduction1.

      (* V poly, D unlimited *)
lemma statistical_zk1 (D <: Distinguisher) statement witness aux &m:
    zk_relation statement witness
    =>
    let real_prob = Pr[ZKReal(HonestProver, MaliciousVerifier, D).run(statement, witness, aux) @ &m : res] in
    let ideal_prob = Pr[ZKIdeal(Simulator, MaliciousVerifier, D).run(statement, witness, aux) @ &m : res] in
    let red_prob = Pr[ZKReduction1(MaliciousVerifier).run(statement, witness, aux) @ &m : res] in

      `|real_prob - ideal_prob| <= zk_red_function statement red_prob.
admitted.


      (* REMOVE ME:

SD(X,Y) = max_{T} | Pr[X:T] - Pr[Y:T] |

SD(X,Y) = 1/2 sum | Pr[X=a] - Pr[Y=a] |

 *)

      (* V unlimited, D unlimited *)
op zk_error : statement -> real.
    
lemma statistical_zk2 (V <: MaliciousVerifier) (D <: Distinguisher) statement witness aux &m:
    zk_relation statement witness
    =>
    let real_prob = Pr[ZKReal(HonestProver, V, D).run(statement, witness, aux) @ &m : res] in
    let ideal_prob = Pr[ZKIdeal(Simulator, V, D).run(statement, witness, aux) @ &m : res] in

      `|real_prob - ideal_prob| <= zk_error statement.
admitted.

