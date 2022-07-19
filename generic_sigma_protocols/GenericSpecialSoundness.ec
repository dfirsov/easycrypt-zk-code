pragma Goals:printall.
require import AllCore List Distr Real RealExp.

require GenericExtractability.
clone include GenericExtractability. (* inherit defs. *)


require RewBasics.
clone import RewBasics as Rew with type sbits <- sbits.


module type SpecialSoundnessAdversary = { 
  proc attack(statement:statement) : transcript * transcript
}.


op valid_transcript_pair (s: statement) 
  (t1 t2: transcript) : bool 
   = t1.`1 = t2.`1 
        /\ t1.`2 <> t2.`2
        /\ verify_transcript s t1 
        /\ verify_transcript s t2.

   
module SpecialSoundnessAdversary(P : RewMaliciousProver) 
 : SpecialSoundnessAdversary = {

  proc attack(statement:statement):transcript * transcript = {
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


abstract theory SpecialSoundnessTheory.

op special_soundness_extract (s:statement)(t1 t2:transcript): witness.

module (Extractor : Extractor)(P : RewMaliciousProver) = {  
  module SA = SpecialSoundnessAdversary(P)
  proc extract(p : statement) : witness = {
    var t1,t2;
    (t1,t2) <@ SA.attack(p);
    return special_soundness_extract p t1 t2;
 }
}.

 theory Computational.

   abstract theory Statement.
   axiom computational_special_soundness: forall (P <: RewMaliciousProver), 
     forall s &m, exists special_soundness_error,
       Pr[ SpecialSoundnessAdversary(P).attack(s) @&m: valid_transcript_pair s res.`1 res.`2
         /\ !(soundness_relation s (special_soundness_extract s res.`1 res.`2))]
        <= special_soundness_error.
   end Statement.


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

   declare module P <: RewMaliciousProver{-HV}.    
   declare axiom P_response_ll : islossless P.response.


   (* rewindability assumption *)
   declare axiom rewindable_P_plus :
           (exists (f : glob P -> sbits),
            injective f /\
            (forall &m, Pr[ P.getState() @ &m : (glob P) = ((glob P){m})
                                             /\ res = f ((glob P){m} ) ] = 1%r) /\
            (forall &m b (x: glob P), b = f x =>
              Pr[P.setState(b) @ &m : glob P = x] = 1%r) /\
            islossless P.setState).



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
                ! soundness_relation p 
             (special_soundness_extract p res.`1 res.`2)] <= deltoid           
      => Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                valid_transcript_pair p res.`1 res.`2 /\
                 soundness_relation p (special_soundness_extract p res.`1 res.`2)]
            >= (Pr[ InitRun1(A(P)).run(p,aux) @ &m  
                  : hc_verify p res.`2.`2 res.`1 res.`2.`1 ]^2
            - (1%r/ (size (challenge_set ) ) %r) 
                 * Pr[ InitRun1(A(P)).run(p,aux) @ &m 
                        : hc_verify p res.`2.`2 res.`1 res.`2.`1 ])
             - deltoid.
   proof. rewrite -  (ex_a_eq_f &m p aux).
   move => f. simplify.
    rewrite -  (ex_a_eq_f &m p aux (fun x => x) ).
   apply (final_eq_step1 (A(P)) _ _ &m (fun pq (r : challenge * (response * commitment)) => 
     hc_verify (fst pq) r.`2.`2 r.`1 r.`2.`1) (fun (pq :statement * unit) 
        (r1 r2 : challenge * (response * commitment)) => soundness_relation (fst pq) 
          (special_soundness_extract (fst pq) (r1.`2.`2, r1.`1, r1.`2.`1) (r2.`2.`2, r2.`1, r2.`2.`1)))
     (p, aux)
    deltoid
   _). proc. call P_response_ll;auto. 
   simplify. 
   apply (rewindable_A_plus P rewindable_P_plus). 
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
    = Pr[Soundness(P, HV).run(p) @ &m : res].
   byequiv. proc. inline*. wp. call (_:true).
   wp. rnd.  wp. call (_:true). wp.  
   skip. simplify. progress. smt. auto. 
   qed.


   lemma computational_extractability &m p deltoid: 
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



   local lemma qqq1  (a b : real) : a <= b  => sqrt a <= sqrt b.
   smt. qed.
   local lemma qqq2  (a b : real) : a ^ 2 <= b  => a <= sqrt b.
   smt. qed.


   lemma computational_soundness &m p deltoid:
    ! in_language soundness_relation p =>
      Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
            valid_transcript_pair p res.`1 res.`2 /\
            ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] 
          <= deltoid
        => Pr[Soundness(P, HV).run(p) @ &m : res]
             <= (sqrt deltoid) + (1%r/(size challenge_set)%r).
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
   apply (computational_extractability &m p). auto. 
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
  smt. 
  qed.

   (*  depending on the size of challenge_set either computational_soundness 
       or computational_soundness_II provide a better bound *)
   lemma computational_soundness_II &m p deltoid:
       ! in_language soundness_relation p =>
      Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
           valid_transcript_pair p res.`1 res.`2 /\
            ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] 
      <= deltoid =>
        Pr[Soundness(P, HV).run(p) @ &m : res]
           <= ((size challenge_set)%r * deltoid) 
                 + (1%r/ (size challenge_set)%r).
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
   apply (computational_extractability &m p). auto. 
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
  smt (challenge_set_size). 
  qed.
  end section.

  end Computational.



   theory Perfect.

    abstract theory Statement.
    axiom perfect_special_soundness p : 
      (forall t1 t2, valid_transcript_pair p t1 t2 =>
        soundness_relation p (special_soundness_extract p t1 t2)).
    end Statement.

    import Computational.
    section.
    declare module P <: RewMaliciousProver{-HV}.
    

   (* rewindability assumption *)
   declare axiom rewindable_P_plus :
           (exists (f : glob P -> sbits),
            injective f /\
            (forall &m, Pr[ P.getState() @ &m : (glob P) = ((glob P){m})
                                             /\ res = f ((glob P){m} ) ] = 1%r) /\
            (forall &m b (x: glob P), b = f x =>
              Pr[P.setState(b) @ &m : glob P = x] = 1%r) /\
            islossless P.setState).


    declare axiom P_response_ll : islossless P.response.  
    declare axiom perfect_special_soundness p : 
     (forall t1 t2, valid_transcript_pair p t1 t2 =>
         soundness_relation p (special_soundness_extract p t1 t2)).
 

    lemma statistical_extractability &m p :
      Pr[Extractor(P).extract(p) @ &m : soundness_relation p res] 
       >= Pr[Soundness(P, HV).run(p) @ &m : res]^2
            - 1%r/(size challenge_set)%r 
                * Pr[Soundness(P, HV).run(p) @ &m : res].
    proof.  progress.
      have f : Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] = 0%r.  
     have -> : 0%r = Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m : false]. smt.
    rewrite Pr[mu_eq]. smt. auto. apply (Computational.computational_extractability P P_response_ll _ &m p 0%r). apply rewindable_P_plus. rewrite f. auto.
    qed.
     
    
   lemma statistical_soundness &m p  :
       ! in_language soundness_relation p
       => Pr[Soundness(P, HV).run(p) @ &m : res] 
           <= ((1%r/ (size (challenge_set))%r)).     
     proof. progress. 
     have ->: inv (size challenge_set)%r = sqrt 0%r + inv (size challenge_set)%r. smt.
     apply (computational_soundness P P_response_ll _ &m p  0%r H _). apply rewindable_P_plus.
     have -> : Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m :
                    valid_transcript_pair p res.`1 res.`2 /\
                    ! soundness_relation p (special_soundness_extract p res.`1 res.`2)] = 0%r.  
     have -> : 0%r = Pr[ SpecialSoundnessAdversary(P).attack(p) @ &m : false]. smt.
     rewrite Pr[mu_eq]. smt. auto.   auto. qed.

    end section.

  end Perfect.

end SpecialSoundnessTheory.

