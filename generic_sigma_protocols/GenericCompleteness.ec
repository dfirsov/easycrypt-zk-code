pragma Goals:printall.
require import AllCore List Distr.
require WhileNotBProc.

require GenericBasics.
clone include GenericBasics. (* inherit defs.  *)


op completeness_relation : relation.


module type HonestProver = {
  proc commitment(s:statement,w:witness) : commitment
  proc response(ch:challenge) : response
}.


module type HonestVerifier = {
  proc challenge(s:statement,c:commitment) : challenge
  proc verify(r:response) : bool
}.


module Completeness(P: HonestProver, V: HonestVerifier) = {
  proc run(s:statement, w:witness) = {
    var commit, challenge, response, accept;
    commit    <@ P.commitment(s,w);
    challenge <@ V.challenge(s,commit);
    response  <@ P.response(challenge);
    accept    <@ V.verify(response);
    return accept;
  }
}.


module CompletenessAmp(P: HonestProver, V: HonestVerifier) = { 
  proc run(stat:statement,wit:witness,N:int) = {
    var accept : bool;
    var i : int;
    i <- 0;
    accept <- true; 
    while(i < N /\ accept) {  
      accept <@ Completeness(P,V).run(stat,wit);
      i <- i + 1;
    } 
    return accept; 
  } 
}. 



module HV : HonestVerifier = {
  var c : commitment
  var s : statement
  var ch : challenge

  proc challenge(statement: statement, commitment: commitment) : challenge = {
    ch <$ duniform challenge_set;
    c <- commitment;
    s <- statement;
    return ch;
  }

 proc verify(r:response) : bool = {
      return verify_transcript s (c,ch,r);
  }
}.


theory CompletenessTheory.

  theory Statistical.

    abstract theory Statement.
    op completeness_error : statement -> real.
    axiom completeness : exists (HP <: HonestProver) (HV  <: HonestVerifier),
      forall  statement witness &m,
        completeness_relation statement witness  =>
         Pr[Completeness(HP,HV).run(statement, witness) @ &m : res]
              >= (1%r - completeness_error statement).
    end Statement.


    section.
    declare module P <: HonestProver{-HV}.
    declare module V <: HonestVerifier{-P}.
    declare axiom verify_ll     : islossless V.verify.
    declare axiom challenge_ll  : islossless V.challenge.
    declare axiom response_ll   : islossless P.response.
    declare axiom commitment_ll : islossless P.commitment.

    local clone import WhileNotBProc as WNBP with type rt <- bool,
                                                  type iat <- statement * witness.


    lemma completeness_seq &m statement witness n deltoid:
        completeness_relation statement witness 
        => (forall &n, Pr[Completeness(P,V).run(statement,witness) @ &n : res]
             >= deltoid)
        => 1 <= n
        => Pr[CompletenessAmp(P, V).run(statement,witness,n) @ &m : res]
               >= deltoid ^ n. 
    proof. 
    move => nil completeness nz.
    have phs : phoare[ Completeness(P,V).run : arg = (statement,witness) 
                             ==> res ] >= deltoid.
    bypr. progress. 
    have  ->: Pr[Completeness(P, V).run(s{m0},w{m0}) @ &m0 :
       res] = Pr[Completeness(P, V).run(statement, witness) @ &m0 :
       res]. rewrite H. simplify. auto.
    apply completeness.  auto.
    have ->: Pr[CompletenessAmp(P, V).run(statement, witness, n) @ &m : res]    
     = Pr[ M(Completeness(P,V)).whp((statement,witness), fun x => !x,1,n, true) 
                @ &m :  res ].
    byequiv (_: ={glob P, glob V} /\  arg{1} = (statement, witness, n) 
       /\ arg{2} = ((statement,witness), fun x => !x,1,n, true)  ==> _).  
    proc.   sp.
    while (i{1} + 1 = M.c{2} /\ N{1}  = e{2} 
      /\ accept{1} = !MyP{2} r{2} /\ ={glob P, glob V}
      /\ (i{2}, MyP{2}, s{2}, e{2}) =
         ((stat{1}, wit{1}), fun (x : bool) => !x, 1, N{1})).
    wp.  call (_: ={glob P, glob V}).
    sim. skip. progress. smt. smt.
    skip. progress. smt. auto. 
    auto.
    byphoare (_: arg = ((statement, witness), fun (x : bool) => !x,
                                           1, (n-1) + 1 , true) ==> _).
    apply (asdsadq_ge (Completeness(P,V))). 
    proc.
    call verify_ll. call response_ll. 
    call challenge_ll. 
    call commitment_ll. 
    skip. auto.
    apply phs. auto. smt. 
    auto. auto. 
    qed.  
    end section.


  end Statistical.



  theory Perfect.

    abstract theory Statement.
    axiom completeness  : exists (HP <: HonestProver) (HV  <: HonestVerifier),
      forall  statement witness &m,
        completeness_relation statement witness  =>
         Pr[Completeness(HP,HV).run(statement, witness) @ &m : res]
              = 1%r.
    end Statement.




    section.
    declare module P <: HonestProver{-HV}.
    declare module V <: HonestVerifier{-P}.

    declare axiom verify_ll     : islossless V.verify.
    declare axiom challenge_ll  : islossless V.challenge.
    declare axiom response_ll   : islossless P.response.
    declare axiom commitment_ll : islossless P.commitment.

    (* assumption of perfect completeness *)
    declare axiom completeness &n statement witness :
     completeness_relation statement witness  =>
       Pr[Completeness(P,V).run(statement, witness) @ &n : res]
             = 1%r.

    local clone import Statistical as SC.

    lemma completeness_seq &m statement witness n:
      completeness_relation statement witness
       => 1 <= n
       => Pr[CompletenessAmp(P, V).run(statement, witness,n) @ &m : res] = 1%r.
    progress.
    have f :   (1%r - 0%r) ^ n <=
      Pr[CompletenessAmp(P, V).run(statement, witness, n) @ &m : res].
    apply (SC.completeness_seq P V verify_ll 
               challenge_ll response_ll commitment_ll _  
               statement witness n _ _ );auto. 
    move => &n.
    progress. rewrite completeness;auto.
    smt.
    qed.

    end section.
  end Perfect.

end CompletenessTheory.