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


    module type SpecialSoundnessExtractor = {
      proc extract(transcript1: transcript, transcript2: transcript) : witness
    }.

    module type SpecialSoundnessAdversary = { (* computational *)
      proc attack(statement:statement, aux:auxiliary_input) : transcript * transcript
    }.

    module type SpecialSoundnessAdvReduction(A: SpecialSoundnessAdversary) = { (* computational *)
      proc run(statement: statement, aux: auxiliary_input) : bool
    }.

module type HonestVerifier = {
  proc challenge(_:statement*commitment) : challenge
  proc verify(_:statement * transcript) : bool
}.

module type MaliciousProver = {  
  proc commitment(s: statement, aux: auxiliary_input) : commitment
  proc response(challenge: challenge) : response
}.

module type MaliciousVerifier = {
  proc challenge(_:statement * commitment * auxiliary_input) : challenge
  proc summitup(statement: statement, response: response) : adv_summary
}.

module HonestVerifier : HonestVerifier = {
  var c : commitment
  proc challenge(statement: statement, commitment: commitment) : challenge = {
    var challenge : challenge;
    challenge <$ duniform (challenge_set statement);
    c <- commitment;
    return challenge;
  }

 proc verify(statement: statement, transcript: transcript) : bool = {
      return verify_transcript statement transcript /\ HonestVerifier.c = transcript.`1;
  }
}.

module Completeness(P: HonestProver, V: HonestVerifier) = {
  proc run(statement:statement, witness:witness) = {
    var commit, challenge, response, accept;
    commit <@ P.commitment(statement,witness);
    challenge <@ V.challenge(statement,commit);
    response <@ P.response(challenge);
    accept <@ V.verify(statement, (commit, challenge, response));
    return accept;
  }
}.


module Soundness(P: MaliciousProver, V: HonestVerifier) = {
  proc run(statement: statement, aux: auxiliary_input) : bool = {
    var commit, challenge, response, accept;
    commit <@ P.commitment(statement, aux);
    challenge <@ V.challenge(statement,commit);
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

    abstract theory ComputationalPoK.

    clone import SpecialSoundnessStatements.
    

    module type ExtractionReduction(P: MaliciousProver) = {
      proc run(statement: statement, aux: auxiliary_input) : bool
    }.

    module SpecialSoundnessAdversary(P : MaliciousProver) : SpecialSoundnessAdversary = {
      proc attack(statement : statement, aux : auxiliary_input) : transcript * transcript = {
        var i,c1,c2,r1,r2;
        i <@ P.commitment(statement, aux);

        c1 <$ duniform (challenge_set witness);
        r1 <@ P.response(c1);

        c2 <$ duniform (challenge_set witness);
        r2 <@ P.response(c2);
        return ((i,c1,r1), (i,c2,r2));
      }
    }.

    module (Extractor : Extractor)(P : MaliciousProver) = {  
      module SA = SpecialSoundnessAdversary(P)
      proc extract(p : statement, aux : auxiliary_input) : witness = {
        var t1,t2;
        (t1,t2) <@ SA.attack(p, aux);
        return special_soundness_extract p t1 t2;
     }
    }.

    require Generic_KE.
    clone import Generic_KE as GKE with type pt <- statement,
                                        type auxt <- auxiliary_input,
                                        type irt <- commitment,
                                        type ct <- challenge,
                                        type rt <- response,
                                        op d <- duniform (challenge_set witness),
                                        op allcs <- (challenge_set witness).

    section.

    declare module P : MaliciousProver {HonestVerifier}.
    declare module ExtractionReduction : ExtractionReduction.
    
    local module A(P : MaliciousProver) : Adv = {
      proc init (p : statement, aux : auxiliary_input) : commitment = {
        var i : commitment;
        i <@ P.commitment(p,aux);
        return i;
     }

     proc run(hcm : commitment, hcc: challenge) : response = {
       var r;
       r <@ P.response(hcc);
       return r;
     }
    }.


   op hc_verify = fun s cm ch rs => verify_transcript s (cm , ch, rs). (* TODO: remove later *)

   local lemma ex_a_eq_f &m p aux f : 
    Pr[ InitRun2(A(P)).run(p,aux) @ &m 
             : res.`1.`1 <> res.`2.`1  /\
               hc_verify p res.`1.`2.`2 res.`1.`1 res.`1.`2.`1  /\
               hc_verify p res.`2.`2.`2 res.`2.`1 res.`2.`2.`1  /\
     f (soundness_relation  p (special_soundness_extract p (res.`1.`2.`2, res.`1.`1, res.`1.`2.`1) 
                                            (res.`2.`2.`2, res.`2.`1, res.`2.`2.`1))) ] 
     = Pr[ SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
                valid_transcript_pair p res.`1 res.`2 /\
                 f  (soundness_relation  p (special_soundness_extract p res.`1 res.`2))].
   proof. byequiv;auto.
   proc. simplify. inline*. wp.  call (_:true).  wp. rnd. wp. call (_:true). wp. rnd. 
   wp.  call (_:true). wp. skip. progress;smt.
   qed.
   

    local lemma hc_pok' &m p aux : 
       Pr[ SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
                 valid_transcript_pair p res.`1 res.`2 /\
                 ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <=
          Pr[ExtractionReduction(P).run(p, aux) @ &m : res] =>

      Pr[ SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
                 valid_transcript_pair p res.`1 res.`2 /\
                  soundness_relation p (special_soundness_extract p res.`1 res.`2)]
        >= (Pr[ InitRun1(A(P)).run(p,aux) @ &m  : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]^2
             - (1%r/ (size (challenge_set witness) ) %r) * Pr[ InitRun1(A(P)).run(p,aux) @ &m : hc_verify p res.`2.`2 res.`1 res.`2.`1 ])
              - Pr[ExtractionReduction(P).run(p, aux) @ &m : res].
    proof. rewrite - ex_a_eq_f.
    move => f. simplify.
     rewrite -  (ex_a_eq_f &m p aux (fun x => x) ).
    apply (final_eq_step1 (A(P)) _ &m (fun pq (r : challenge * (response * commitment)) => hc_verify (fst pq) r.`2.`2 r.`1 r.`2.`1) (fun (pq :statement * auxiliary_input) (r1 r2 : challenge * (response * commitment)) => soundness_relation (fst pq) (special_soundness_extract (fst pq) (r1.`2.`2, r1.`1, r1.`2.`1) (r2.`2.`2, r2.`1, r2.`2.`1)))
      (p, aux)
     Pr[ExtractionReduction(P).run(p, aux) @ &m : res]  
    _
    ). admit.   auto.
    qed.


    local lemma qqq &m p aux : 
      Pr[SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
           valid_transcript_pair p res.`1 res.`2 /\
           soundness_relation p (special_soundness_extract p res.`1 res.`2)]
     <=  Pr[Extractor(P).extract(p, aux) @ &m : soundness_relation p res].
    byequiv. proc. inline*. wp. call (_:true).
    rnd.  simplify. call (_:true). rnd.  call (_:true).
    wp. simplify. skip. progress. smt. smt. 
    qed.


    local lemma www &m p aux: 
      Pr[ InitRun1(A(P)).run(p,aux) @ &m 
          : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]
     = Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res].
    byequiv. proc. inline*. wp. call (_:true).
    wp. rnd.  wp. call (_:true). wp. 
    skip. simplify. progress. admit. admit. smt. auto. auto. auto.
    qed.


    lemma computational_PoK &m p aux: 
          Pr[ SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <=
             Pr[ExtractionReduction(P).run(p, aux) @ &m : res] =>
      Pr[Extractor(P).extract(p, aux) @ &m : soundness_relation p res] >=
       (Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res]^2
       - (1%r/ (size (challenge_set witness))%r) * Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res])
         - Pr[ExtractionReduction(P).run(p, aux) @ &m : res].
    smt (www hc_pok' qqq).
    qed.
    end section.


    abstract theory Example.
    op computationally_extractable_function : statement -> real -> real.
    axiom computationally_extractable:
        exists (Extractor <: Extractor),
        exists (ExtractionReduction <: ExtractionReduction),
        forall statement aux &m,
        forall (MaliciousProver <: MaliciousProver),
        let verify_prob = Pr[Soundness(MaliciousProver, HonestVerifier).run(statement, aux) @ &m : res] in
        let extract_prob = Pr[Extractor(MaliciousProver).extract(statement, aux) @ &m 
                 : soundness_relation statement res] in
        let red_prob = Pr[ExtractionReduction(MaliciousProver).run(statement, aux) @ &m : res] in
        extract_prob >= computationally_extractable_function statement verify_prob - red_prob. 
    end Example.

    end ComputationalPoK.


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

  end PoK.


(* ZK *)
  abstract theory ZK.

  module type ZKDistinguisher = {
    proc guess(statement: statement, witness: witness, aux: auxiliary_input, summary: adv_summary) : bool
  }.


  module ZKReal(P: HonestProver, V: MaliciousVerifier, D: ZKDistinguisher) = {
    proc run(statement: statement, witness: witness, aux: auxiliary_input) = {
      var commit, challenge, response, summary, guess;
      commit <@ P.commitment(statement, witness);
      challenge <@ V.challenge(statement, commit, aux);
      response <@ P.response(challenge);
      summary <@ V.summitup(statement, response);
      guess <@ D.guess(statement, witness, aux, summary);
      return guess;
    }
  }.

  module type Simulator(V: MaliciousVerifier) = {
    proc * simulate(statement: statement, n : int, aux: auxiliary_input) : adv_summary
  }.

  module ZKIdeal(S: Simulator, V: MaliciousVerifier, D: ZKDistinguisher) = {
    proc run(statement: statement, witness: witness, n : int, aux: auxiliary_input) = {
      var summary, guess;
      summary <@ S(V).simulate(statement, n, aux);
      guess <@ D.guess(statement, witness, aux, summary);
      return guess;
    }
  }.


    abstract theory ComputationalZK. (* Computational ZK *)

    op zk_red_function : statement -> real -> real.

    module type ZKReduction(V: MaliciousVerifier, D: ZKDistinguisher) = {
      proc run(statement: statement, witness: witness, aux: auxiliary_input) : bool
    }.

    axiom computational_zk:
        exists (HonestProver <: HonestProver),
        exists (Simulator <: Simulator),
        exists (ZKReduction <: ZKReduction),
        forall statement witness aux n &m,
        forall (MaliciousVerifier <: MaliciousVerifier),
        forall (Distinguisher <: ZKDistinguisher),
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
        forall (V <: MaliciousVerifier) (D <: ZKDistinguisher),
        forall statement witness aux n &m,
        zk_relation statement witness => 
        let real_prob = Pr[ZKReal(HonestProver, V, D).run(statement, witness, aux) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator, V, D).run(statement, witness, n, aux) @ &m : res] in
          `|real_prob - ideal_prob| <= zk_error statement n.



    end StatisticalZK.

  end ZK.

end ZKProtocol.


