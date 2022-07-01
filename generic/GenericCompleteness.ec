pragma Goals:printall.
require import AllCore List Distr.

type statement, witness, commitment, response, challenge,  sbits.
type relation = statement -> witness -> bool.
type transcript = commitment * challenge * response.

op in_language (R:relation) statement : bool = exists witness, R statement witness.

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
  proc verify(_:statement * transcript) : bool
}.


module HV : HonestVerifier = {
  var c : commitment

  proc challenge(statement: statement, commitment: commitment) : challenge = {
    var challenge : challenge;
    challenge <$ duniform challenge_set;
    c <- commitment;
    return challenge;
  }

 proc verify(statement: statement, transcript: transcript) : bool = {
      return verify_transcript statement transcript /\ HV.c = transcript.`1;
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



theory CompletenessTheory.

op completeness_error : statement -> real.



require WhileNotBProc.
clone import WhileNotBProc as WNBP with type rt <- bool,
                                        type iat <- statement * witness.

section.

declare module P <: HonestProver{-M, -HV}.
declare module V <: HonestVerifier{-M, -P}.

declare axiom verify_ll : islossless V.verify.
declare axiom challenge_ll : islossless V.challenge.
declare axiom response_ll : islossless P.response.
declare axiom commitment_ll : islossless P.commitment.


declare axiom completeness &n statement witness :
 completeness_relation statement witness  =>
   Pr[Completeness(P,V).run(statement, witness) @ &n : res]
         >= (1%r - completeness_error statement).

lemma completeness_seq &m statement witness n:
    completeness_relation statement witness  =>
     0 <= n =>
     Pr[CompletenessAmp(P, V).run(statement, witness,n) @ &m : res]
     >= (1%r - completeness_error statement) ^ (n + 1).                                        
proof. 
move => nil nz .
have phs : phoare[ Completeness(P,V).run : arg = (statement,witness) ==> res ] >= (1%r - completeness_error statement).
bypr. progress. 
have  ->: Pr[Completeness(P, V).run(s{m0},w{m0}) @ &m0 :
   res] = Pr[Completeness(P, V).run(statement, witness) @ &m0 :
   res]. smt.
apply completeness. assumption.
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


