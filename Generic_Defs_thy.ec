require import AllCore List Distr.

theory ZKProtocol.

type statement, witness, commitment, response, challenge, auxiliary_input, adv_summary.
type relation = statement -> witness -> bool.
type transcript = commitment * challenge * response.

op in_language (R:relation) statement : bool = exists witness, R statement witness.
op challenge_set : statement -> challenge list. (* axiomitize that! *)
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



module type HonestVerifier = {
  proc challenge(_:statement) : challenge
  proc verify(_:statement * transcript) : bool
}.

module type MaliciousProver = {  
  proc commitment(s: statement, aux: auxiliary_input) : commitment
  proc response(challenge: challenge) : response
}.

module type MaliciousVerifier = {
  proc challenge(statement: statement, aux: auxiliary_input) : challenge
  proc summitup(statement: statement, response: response) : adv_summary
}.

module HonestVerifier : HonestVerifier = {
  proc challenge(statement: statement) : challenge = {
    var challenge : challenge;
    challenge <$ duniform (challenge_set statement);
    return challenge;
  }

 proc verify(statement: statement, transcript: transcript) : bool = {
      return verify_transcript statement transcript;
  }
}.

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

    axiom perfect_special_soundness (statement:statement) (transcript1 transcript2: transcript) &m:
        valid_transcript_pair statement transcript1 transcript2
        =>
        soundness_relation statement (special_soundness_extract statement transcript1 transcript2).

    end PerfectSpecialSoundnessStatement.   


    abstract theory ComputationalSpecialSoundnessStatement.

    op special_soundness_red_function : statement -> real -> real.

    module type SpecialSoundnessExtractor = {
      proc extract(transcript1: transcript, transcript2: transcript) : witness
    }.

    module type SpecialSoundnessAdversary = { (* computational *)
      proc attack(statement:statement, aux:auxiliary_input) : transcript * transcript
    }.

    module type SpecialSoundnessAdvReduction(A: SpecialSoundnessAdversary) = { (* computational *)
      proc run(statement: statement, aux: auxiliary_input) : bool
    }.


    abstract theory ExampleStatement.
    axiom computational_special_soundness:
          exists (SpecialSoundnessAdvReduction <: SpecialSoundnessAdvReduction),
          forall statement aux &m,
          forall (SpecialSoundnessAdversary <: SpecialSoundnessAdversary),
        let attack_prob = Pr[SpecialSoundnessAdversary.attack(statement, aux) @ &m :
          valid_transcript_pair statement res.`1 res.`2
          /\ ! soundness_relation statement (special_soundness_extract statement res.`1 res.`2)] in
        let red_prob = Pr[SpecialSoundnessAdvReduction(SpecialSoundnessAdversary).run(statement, aux) @ &m : res] in
        attack_prob <= special_soundness_red_function statement red_prob.
    end ExampleStatement.

    end ComputationalSpecialSoundnessStatement.

  end SpecialSoundnessStatements.


  abstract theory SoundnessStatements. (* Soundness *)


    abstract theory StatisticalSoundnessStatement. (* Statistical soundness *)
    op soundness_error : statement -> real.

    axiom statistical_soundness (P <: MaliciousProver) statement aux &m:
        ! in_language soundness_relation statement
        =>
        Pr[Soundness(P, HonestVerifier).run(statement, aux) @ &m : res]
          <= soundness_error statement.

    end StatisticalSoundnessStatement.


    abstract theory ComputationalSoundnessStatement.       (* Computational soundness *)

    op soundness_red_function : statement -> real -> real.

    module type SoundnessReduction(P: MaliciousProver) = {
      proc run(statement: statement, aux: auxiliary_input) : bool
    }.

    axiom computational_soundness:
        exists (SoundnessReduction <: SoundnessReduction),
        forall statement aux &m,
        forall (MaliciousProver <: MaliciousProver),
        let attack_prob = Pr[Soundness(MaliciousProver, HonestVerifier).run(statement, aux) @ &m : res] in
        let red_prob = Pr[SoundnessReduction(MaliciousProver).run(statement, aux) @ &m : res] in
        attack_prob <= soundness_red_function statement red_prob.

    end ComputationalSoundnessStatement.

  end SoundnessStatements.



    (* Proof of knowledge *)
  abstract theory PoK.

  module type Extractor(P: MaliciousProver) = {
    proc extract(statement: statement, aux: auxiliary_input) : witness
  }.


    abstract theory StatisticalPoK.

    op extraction_success_function : statement -> real -> real.

    axiom statistically_extractable:
        exists (Extractor <: Extractor),
        forall statement aux &m,
        forall (P <: MaliciousProver),
        let verify_prob = Pr[Soundness(P, HonestVerifier).run(statement, aux) @ &m : res] in
        let extract_prob = Pr[Extractor(P).extract(statement, aux) @ &m : soundness_relation statement res] in
        extract_prob >= extraction_success_function statement verify_prob.

    end StatisticalPoK.

    abstract theory ComputationalPoK.

    module type ExtractionReduction(P: MaliciousProver) = {
      proc run(statement: statement, aux: auxiliary_input) : bool
    }.
    op computationally_extractable_function : statement -> real -> real.

    axiom computationally_extractable:
        exists (Extractor <: Extractor),
        exists (ExtractionReduction <: ExtractionReduction),
        forall statement aux &m,
        forall (MaliciousProver <: MaliciousProver),
        let verify_prob = Pr[Soundness(MaliciousProver, HonestVerifier).run(statement, aux) @ &m : res] in
        let extract_prob = Pr[Extractor(MaliciousProver).extract(statement, aux) @ &m : soundness_relation statement res] in
        let red_prob = Pr[ExtractionReduction(MaliciousProver).run(statement, aux) @ &m : res] in
        extract_prob >= computationally_extractable_function statement verify_prob - red_prob.  (* Actually should be something relating extract_prob, verify_prob, red_prob *)


    end ComputationalPoK.
  end PoK.


(* ZK *)


  abstract theory ZK.

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
    proc * simulate(statement: statement, n : int, aux: auxiliary_input) : adv_summary
  }.

  module ZKIdeal(S: Simulator, V: MaliciousVerifier, D: Distinguisher) = {
    proc run(statement: statement, witness: witness, n : int, aux: auxiliary_input) = {
      var summary, guess;
      summary <@ S(V).simulate(statement, n, aux);
      guess <@ D.guess(statement, witness, aux, summary);
      return guess;
    }
  }.


    abstract theory ComputationalZK. (* Computational ZK *)

    op zk_red_function : statement -> real -> real.

    module type ZKReduction(V: MaliciousVerifier, D: Distinguisher) = {
      proc run(statement: statement, witness: witness, aux: auxiliary_input) : bool
    }.

    axiom computational_zk:
        exists (HonestProver <: HonestProver),
        exists (Simulator <: Simulator),
        exists (ZKReduction <: ZKReduction),
        forall statement witness aux n &m,
        forall (MaliciousVerifier <: MaliciousVerifier),
        forall (Distinguisher <: Distinguisher),
        zk_relation statement witness
        =>
        let real_prob = Pr[ZKReal(HonestProver, MaliciousVerifier, Distinguisher).run(statement, witness, aux) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator, MaliciousVerifier, Distinguisher).run(statement, witness, n, aux) @ &m : res] in
        let red_prob = Pr[ZKReduction(MaliciousVerifier, Distinguisher).run(statement, witness, aux) @ &m : res] in
          `|real_prob - ideal_prob| <= zk_red_function statement red_prob.

    end ComputationalZK.


    abstract theory StatisticalZK.
    op zk_error : statement -> int -> real.

    axiom statistical_zk:
        exists (HonestProver <: HonestProver),
        exists (Simulator <: Simulator),
        forall (V <: MaliciousVerifier) (D <: Distinguisher),
        forall statement witness aux n &m,
        zk_relation statement witness => 
        let real_prob = Pr[ZKReal(HonestProver, V, D).run(statement, witness, aux) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator, V, D).run(statement, witness, n, aux) @ &m : res] in
          `|real_prob - ideal_prob| <= zk_error statement n.



    end StatisticalZK.

  end ZK.

end ZKProtocol.


