pragma Goals:printall.
require import AllCore List Distr.
require WhileNotBProc.

(* parameter types  *)
type statement, witness, commitment, response, challenge.

(* synonyms   *)
type relation   = statement -> witness -> bool.
type transcript = commitment * challenge * response.

op in_language (R:relation) statement: bool = exists witness, R statement witness.

(* parameter functions *)
op challenge_set : challenge list. 

axiom challenge_set_size : 0 < size challenge_set.

op verify_transcript : statement -> transcript -> bool.

op completeness_relation : relation.


module type HonestProver = {
  proc commitment(_:statement*witness) : commitment
  proc response(_:challenge) : response
}.

module type HonestVerifier = {
  proc challenge(_:statement*commitment) : challenge
  proc verify(_:response) : bool
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



(* completeness for sequentially composed sigma protocol *)
theory SequentialCompositionCompleteness.


  theory StatisticalCompleteness.

  op completeness_error : statement -> real.

  section.

  declare module P <: HonestProver{-HV}.
  declare module V <: HonestVerifier{-P}.

  declare axiom verify_ll     : islossless V.verify.
  declare axiom challenge_ll  : islossless V.challenge.
  declare axiom response_ll   : islossless P.response.
  declare axiom commitment_ll : islossless P.commitment.


  local clone import WhileNotBProc as WNBP with type rt <- bool,
                                                type iat <- statement * witness.


  (* assumption of statistical completeness *)
  declare axiom completeness &n statement witness :
   completeness_relation statement witness  =>
     Pr[Completeness(P,V).run(statement, witness) @ &n : res]
           >= (1%r - completeness_error statement).

  (* detloid can depend on P and V *)
  lemma completeness_seq &m statement witness n:
      completeness_relation statement witness
      => 1 <= n
      => Pr[CompletenessAmp(P, V).run(statement, witness,n) @ &m : res]
             >= (1%r - completeness_error statement) ^ n. 
  proof. 
  move => nil nz.
  have phs : phoare[ Completeness(P,V).run : arg = (statement,witness) ==> res ] >= (1%r - completeness_error statement).
  bypr. progress. 
  have  ->: Pr[Completeness(P, V).run(s{m0},w{m0}) @ &m0 :
     res] = Pr[Completeness(P, V).run(statement, witness) @ &m0 :
     res]. smt.
  apply completeness.  auto.
  have ->: Pr[CompletenessAmp(P, V).run(statement, witness, n) @ &m : res]    
   = Pr[ M(Completeness(P,V)).whp((statement,witness), fun x => !x,1,n, true) @ &m :  res ].
  byequiv (_: ={glob P, glob V} /\  arg{1} = (statement, witness, n) /\ arg{2} = ((statement,witness), fun x => !x,1,n, true)  ==> _).  
  proc.   sp.
  while (i{1} + 1 = M.c{2} /\ N{1}  = e{2} /\ accept{1} = !MyP{2} r{2} /\ ={glob P, glob V}
    /\ (i{2}, MyP{2}, s{2}, e{2}) =
    ((stat{1}, wit{1}), fun (x : bool) => !x, 1, N{1})  ).
  wp.  call (_: ={glob P, glob V}).
  sim. skip. progress. smt. smt.
  skip. progress.  smt. smt.
  auto.  auto.
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

  end StatisticalCompleteness.



  theory PerfectCompleteness.

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


  local clone import StatisticalCompleteness as SC with 
    op completeness_error <- (fun x => 0%r).


  lemma completeness_seq &m statement witness n:
      completeness_relation statement witness  =>
       1 <= n =>
       Pr[CompletenessAmp(P, V).run(statement, witness,n) @ &m : res]
       = 1%r.
  progress.
  have f :   (1%r - 0%r) ^ n <=
    Pr[CompletenessAmp(P, V).run(statement, witness, n) @ &m : res].
  apply (SC.completeness_seq P V verify_ll challenge_ll response_ll commitment_ll _  
            &m statement witness n _ _ );auto. 
  move => &n.
  progress. rewrite completeness;auto.
  smt.
  qed.

  end section.

  end PerfectCompleteness.


end SequentialCompositionCompleteness.

(* print SequentialCompositionCompleteness. *)





   
