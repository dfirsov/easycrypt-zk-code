require import AllCore List Distr.

theory ZKProtocol.

type statement, witness, commitment, response, challenge, auxiliary_input, adv_summary.
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
    challenge <$ duniform (challenge_set );
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

    op special_soundness_extract : statement -> transcript -> transcript -> witness.

    clone import SpecialSoundnessStatements with op special_soundness_extract <- special_soundness_extract.
    

    module type ExtractionReduction(P: MaliciousProver) = {
      proc run(statement: statement, aux: auxiliary_input) : bool
    }.

    module SpecialSoundnessAdversary(P : MaliciousProver) : SpecialSoundnessAdversary = {
      proc attack(statement : statement, aux : auxiliary_input) : transcript * transcript = {
        var i,c1,c2,r1,r2;
        i <@ P.commitment(statement, aux);

        c1 <$ duniform (challenge_set );
        r1 <@ P.response(c1);

        c2 <$ duniform (challenge_set );
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
                                        op d <- duniform (challenge_set ),
                                        op allcs <- (challenge_set ).

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
             - (1%r/ (size (challenge_set ) ) %r) * Pr[ InitRun1(A(P)).run(p,aux) @ &m : hc_verify p res.`2.`2 res.`1 res.`2.`1 ])
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
    skip. simplify. progress. auto. auto. 
    qed.


    lemma computational_PoK &m p aux: 
          Pr[ SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <=
             Pr[ExtractionReduction(P).run(p, aux) @ &m : res] =>
      Pr[Extractor(P).extract(p, aux) @ &m : soundness_relation p res] >=
       (Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res])
         - Pr[ExtractionReduction(P).run(p, aux) @ &m : res].
    smt (www hc_pok' qqq).
    qed.

    require import Real RealExp.
    lemma qqq1  (a b : real) : a <= b  => sqrt a <= sqrt b.
    smt. qed.
    lemma qqq2  (a b : real) : a ^ 2 <= b  => a <= sqrt b.
    smt. qed.

      
    lemma computational_soundness &m p aux :
        ! in_language soundness_relation p =>
       Pr[ SpecialSoundnessAdversary(P).attack(p, aux) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] <=
             Pr[ExtractionReduction(P).run(p, aux) @ &m : res] =>
         Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res]
         <= sqrt (Pr[ExtractionReduction(P).run(p, aux) @ &m : res] + (1%r/ (size (challenge_set))%r)).
    proof. progress.
    have f1 : Pr[Extractor(P).extract(p, aux) @ &m : soundness_relation p res] = 0%r.
      have <-: Pr[Extractor(P).extract(p, aux) @ &m : false ] = 0%r.
      rewrite Pr[mu_false]. auto.
    rewrite Pr[mu_eq]. smt. auto.
    have  :   0%r >=
       (Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res])
         - Pr[ExtractionReduction(P).run(p, aux) @ &m : res].
     rewrite - f1.
    apply (computational_PoK &m p aux). auto. 
    pose a := Pr[Soundness(P, HonestVerifier).run(p, aux) @ &m : res].
    pose b := Pr[ExtractionReduction(P).run(p, aux) @ &m : res].
    have f2 : 0%r <= a <= 1%r. smt.
    smt (challenge_set_size qqq1 qqq2).
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

  module type Simulator(V: MaliciousVerifier) = {
    proc * simulate(statement: statement, n : int, aux: auxiliary_input) : adv_summary
  }.

  module type Simulator1(V: MaliciousVerifier) = {
    proc run(statement: statement, aux: auxiliary_input) : bool * adv_summary
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


    require OneToManyZK.
    clone import OneToManyZK as OMZK with type prob <- statement, 
                                          type wit <- witness, 
                                          type sbits <- adv_summary, 
                                          type event <- bool, 
                                          type auxiliary_input <- auxiliary_input,
                                          op E <- (fun x => fst x),
                                          op fevent <- false
   rename "Simulator1" as "Simulator1NP".


    module ZKD(P : HonestProver, V : MaliciousVerifier, D : ZKDistinguisher) = {
      proc main(Ny : statement, aux: auxiliary_input, w : witness) = {
        var c,b,r,result,rb;
        c <- P.commitment(Ny,w);
        b <- V.challenge(Ny,c,aux);
        r <- P.response(b);
        result <- V.summitup(Ny,r);
        rb <- D.guess(Ny,w,aux,result);
        return rb;
      }
    }.



    theory StatisticalZKDeriv.

    section.
    op negl : real.

    declare module HonestProver : HonestProver.
    declare module Sim1 : Simulator1 {MW.IFB.IM.W, MW.IFB.DW}.
 
    axiom sim1_run_ll : forall (V <: MaliciousVerifier),  islossless Sim1(V).run.

    axiom qqq &m (p : statement) (w : witness) 
     (aux : auxiliary_input) (D <: ZKDistinguisher{HonestProver, Sim1}) 
         (V <: MaliciousVerifier{D, HonestProver}): 
       islossless D.guess =>
       islossless V.summitup =>
       zk_relation p w =>  
        `|Pr[W0(Sim1(V), D).run(p, w, aux) @ &m : fst res.`2 /\ res.`1] /
             Pr[Sim1(V).run(p,aux) @ &m : fst res] 
                  - Pr[ ZKD(HonestProver,V,D).main(p,aux,w) @ &m : res ]| <= negl.


   
     module  Simulator(S : Simulator1)(V : MaliciousVerifier)  = {
       module M = MW.IFB.IM.W(S(V))
       proc simulate(statement : statement, n : int, aux : auxiliary_input) :
         adv_summary = {
            var r;
            r <@ M.whp(fst, (statement,aux),1,n,(false,witness));
            return r.`2;
       }
     }.

    
     lemma statistical_zk:
        forall (V <: MaliciousVerifier {Sim1, MW.IFB.IM.W, HonestProver, MW.IFB.DW}) 
               (D <: ZKDistinguisher{Sim1, MW.IFB.IM.W, V, HonestProver}),
          islossless V.summitup =>
          islossless D.guess =>
        forall stat wit ax N p0 &m,
        zk_relation stat wit => 0 <= N =>
        p0 <= Pr[Sim1(V).run(stat, ax) @ &m : res.`1] =>
        let real_prob = Pr[ZKReal(HonestProver, V, D).run(stat, wit, ax) @ &m : res] in
        let ideal_prob = Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N, ax) @ &m : res] in
          `|real_prob - ideal_prob| <= negl + 2%r * (1%r - p0)^N.
    proof.
    progress.
    have ->: 
     `|Pr[ZKReal(HonestProver, V, D).run(stat, wit, ax) @ &m : res] -
      Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N, ax) @ &m : res]|
     = `|Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N, ax) @ &m : res] - Pr[ZKReal(HonestProver, V, D).run(stat, wit, ax) @ &m : res]|. smt.
    have ->: Pr[ZKIdeal(Simulator(Sim1), V, D).run(stat, wit, N, ax) @ &m : res]
     = Pr[Iter(Sim1(V), D).run(false,stat,wit,ax,N,fst) @ &m : res.`1].
    byequiv (_:  E{2} = fst /\ aux{1} = aux{2} /\ n{1} = ea{2} /\ fevent{2} = false  /\
      statement{1} = Ny{2} /\ witness{1} = w{2} /\
        ={glob Sim1, glob HonestProver, glob D, glob V, glob MW.IFB.IM.W} ==> _)  ;auto. proc.
    inline Iter(Sim1(V), D).WI.run. wp.  sp. simplify.
    call (_:true).  simplify. inline Simulator(Sim1,V).simulate. wp. sp.
    call (_: ={glob Sim1, glob V, glob MW.IFB.IM.W}).  sim. skip. progress.
    progress.
    have ->: Pr[ZKReal(HonestProver, V, D).run(stat, wit, ax) @ &m : res]
      = Pr[ ZKD(HonestProver,V,D).main(stat,ax,wit) @ &m : res ].
    byequiv.  proc. sim. auto. auto.
    apply (one_to_many_zk (Sim1(V)) D _ _ _ &m stat wit p0 negl N
    Pr[ZKD(HonestProver, V, D).main(stat, ax, wit) @ &m : res] ax _ _ _
    ) .  apply (sim1_run_ll V). apply H0. auto. 
    apply (qqq &m stat wit ax D V H0 H H1). apply H2. auto.
    qed.
end section.


   end StatisticalZKDeriv.

   end StatisticalZK.

  end ZK.

end ZKProtocol.


