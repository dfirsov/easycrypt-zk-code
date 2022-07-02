pragma Goals:printall.
require import AllCore List Distr.

require GenericCompleteness.
clone include GenericCompleteness. (* inherit defs.  *)

op soundness_relation : relation.

module type MaliciousProver = {  
  proc commitment(s: statement) : commitment
  proc response(challenge: challenge) : response
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


theory SoundnessTheory.

require WhileNotBProc.
clone import WhileNotBProc as WNBP with type rt <- bool,
                                        type iat <- statement.

section.

declare module P <: MaliciousProver {-M, -HV}.

(* are these needed? after all we are proving <= probability *)
declare axiom verify_ll : islossless HV.verify.
declare axiom challenge_ll : islossless HV.challenge.
declare axiom response_ll : islossless P.response.
declare axiom commitment_ll : islossless P.commitment.

op deltoid : real.

declare axiom soundness &n statement:
    ! in_language soundness_relation statement =>
     Pr[Soundness(P,HV).run(statement) @ &n : res]
         <= deltoid.

lemma soundness_seq &m statement n:
    ! in_language soundness_relation statement =>
     0 <= n =>
     Pr[SoundnessAmp(P,HV).run(statement, n) @ &m : res]
       <= deltoid ^ (n + 1).
proof.
move => nil nz.
have phs : phoare[ Soundness(P,HV).run : arg = (statement) ==> res ] <= deltoid.
bypr. move => &m0 H. 
rewrite H. simplify. apply soundness.  assumption.
have ->: Pr[SoundnessAmp(P, HV).run(statement, n) @ &m : res]    
 = Pr[ M(Soundness(P,HV)).whp((statement), fun x => !x,1,n+1, true) @ &m :  res ].
byequiv (_: ={glob P, glob HV} /\  arg{1} = (statement, n) /\ arg{2} = ((statement), fun x => !x,1,n+1, true)  ==> _).  
proc.   sp.
while (i{1} + 1 = M.c{2} /\ N{1} + 1 = e{2} /\ accept{1} = !MyP{2} r{2} /\ ={glob P, glob HV}
  /\ (i{2}, MyP{2}, s{2}, e{2}) =
  ((stat{1}), fun (x : bool) => !x, 1, N{1}+1)  ).
wp.  call (_: ={glob P, glob HV}).
sim. skip. progress. smt. smt.
skip. progress.  smt. smt.
auto.  auto.
byphoare (_: arg = ((statement), fun (x : bool) => !x,
                                       1, n + 1, true) ==> _).
apply (asdsadq_le (Soundness(P,HV))). 
proc.
call verify_ll. call response_ll. call challenge_ll. call commitment_ll. skip. auto.
apply phs. auto. 
auto. auto. auto.
qed.

end section.

end SoundnessTheory.
