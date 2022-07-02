pragma Goals:printall.
require import AllCore List Distr.

require GenericExtractability.
clone include GenericExtractability. (* inherit defs. *)


module type SpecialSoundnessExtractor = {
  proc extract(transcript1: transcript, transcript2: transcript) : witness
}.

module type SpecialSoundnessAdversary = { (* computational *)
  proc attack(statement:statement) : transcript * transcript
}.



op valid_transcript_pair (statement: statement) (transcript1 transcript2: transcript) : bool 
   = transcript1.`1 = transcript2.`1 
        /\ transcript1.`2 <> transcript2.`2
        /\ verify_transcript statement transcript1 
        /\ verify_transcript statement transcript2.


op special_soundness_extract : statement -> transcript -> transcript -> witness.

module SpecialSoundnessAdversary(P : MaliciousProver) : SpecialSoundnessAdversary = {
  proc attack(statement : statement) : transcript * transcript = {
    var i,c1,c2,r1,r2;
    i <@ P.commitment(statement);

    c1 <$ duniform challenge_set;
    r1 <@ P.response(c1);

    c2 <$ duniform challenge_set;
    r2 <@ P.response(c2);
    return ((i,c1,r1), (i,c2,r2));
  }
}.


module (Extractor : Extractor)(P : MaliciousProver) = {  
  module SA = SpecialSoundnessAdversary(P)
  proc extract(p : statement) : witness = {
    var t1,t2;
    (t1,t2) <@ SA.attack(p);
    return special_soundness_extract p t1 t2;
 }
}.



abstract theory SpecialSoundnessTheory.

    abstract theory ComputationalSpecialSoundness.   

    require GenericKE.
    clone import GenericKE as GKE with type pt <- statement,
                                       type auxt <- unit,
                                        type irt <- commitment,
                                        type ct <- challenge,
                                        type rt <- response,
                                        op d <- duniform challenge_set,
                                        op allcs <- challenge_set.

    section.

    declare module P <: MaliciousProver{-HV}.
    
    declare axiom P_response_ll : islossless P.response.

    local module A(P : MaliciousProver) : Adv = {
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
   proc. simplify. inline*. wp.  call (_:true).  wp. rnd. wp. call (_:true). wp. rnd. 
   wp.  call (_:true). wp.  skip. progress;smt.
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
    byequiv. proc. inline*. wp. call (_:true).
    rnd.  simplify. call (_:true). rnd.  call (_:true).
    wp. simplify. wp. skip. progress. smt. smt. 
    qed.



    local lemma www &m p aux: 
      Pr[ InitRun1(A(P)).run(p,aux) @ &m 
          : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]
     = Pr[Soundness(P, HV).run(p) @ &m : res].
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
       (Pr[Soundness(P, HV).run(p) @ &m : res]^2
       - (1%r/ (size challenge_set)%r) * Pr[Soundness(P, HV).run(p) @ &m : res])
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
     = Pr[Soundness(P, HV).run(p) @ &m : res]. apply www.

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
       (Pr[Soundness(P, HV).run(p) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HV).run(p) @ &m : res]).
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
       f Pr[Soundness(P, HV).run(p) @ &m : res]
        => (forall s, f s <= 0%r => s <= epsilon) =>
        Pr[Soundness(P, HV).run(p) @ &m : res]
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
         Pr[Soundness(P, HV).run(p) @ &m : res]
         <=  (sqrt deltoid) + (1%r/ (size (challenge_set))%r).
    proof. progress.
    have f1 : Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] = 0%r.
      have <-: Pr[Extractor(P).extract(p) @ &m : false ] = 0%r.
      rewrite Pr[mu_false]. auto.
    rewrite Pr[mu_eq]. smt. auto.
    have  :   0%r >=
       (Pr[Soundness(P, HV).run(p) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HV).run(p) @ &m : res])
         - deltoid.
     rewrite - f1.
    apply (computational_PoK &m p). auto. 
    pose a := Pr[Soundness(P, HV).run(p) @ &m : res].
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
         Pr[Soundness(P, HV).run(p) @ &m : res]
         <=  ((size (challenge_set))%r * deltoid) + (1%r/ (size (challenge_set))%r).
    proof. progress.
    have f1 : Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] = 0%r.
      have <-: Pr[Extractor(P).extract(p) @ &m : false ] = 0%r.
      rewrite Pr[mu_false]. auto.
    rewrite Pr[mu_eq]. smt. auto.
    have  :   0%r >=
       (Pr[Soundness(P, HV).run(p) @ &m : res]^2
       - (1%r/ (size (challenge_set ))%r) * Pr[Soundness(P, HV).run(p) @ &m : res])
         - deltoid.
     rewrite - f1.
    apply (computational_PoK &m p). auto. 
    pose a := Pr[Soundness(P, HV).run(p) @ &m : res].
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
         Pr[Soundness(P, HV).run(p) @ &m : res]
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

    end ComputationalSpecialSoundness.

end SpecialSoundnessTheory.