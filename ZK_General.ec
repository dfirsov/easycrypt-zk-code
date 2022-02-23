require import AllCore.

type prob, wit, chal, com, resp, sbits.


module type Prover = {
  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.

module type Verifier = {
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
  proc summitup(c : com, r : resp)   : sbits
}.


module type RewProver = {
  proc * setState(s : sbits) : unit
  proc getState() : sbits
  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.

module type RewVerifier = {
  proc * setState(s : sbits) : unit
  proc getState() : sbits
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
  proc summitup(c : com, r : resp)   : sbits
}.

module type Simulator = {
  proc simulate(Ny : prob) : sbits
}.

(* Correctness *)
module Correct(P : Prover, V : Verifier) = {
  proc run(Ny:prob, w : wit) = {
    var c,b,r,result;
    c <- P.commit(Ny,w);  
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.verify(c,r);  
    return result;
  }
}.

(* ZK *)
module ZK(P : Prover, V : Verifier) = {
  proc main(Ny : prob, w : wit) = {
    var c,b,r,result;
    c <- P.commit(Ny,w);
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.summitup(c,r);
    return result;
  }
}.


require While_not_b_proc.
clone import While_not_b_proc as IF with type iat <- (prob * wit),
                                         type rt <- bool.

(* 
1/ if one proves soundness
  forall P &m x, x \notin  L => 
    Pr[ Correct(P,HV).run(x) @ &m : res ] <= p
then we can iterate "Correct(P,V).run" (without rewinding)
to lower probabiliy to success to arbitrary level.

2/ At the same time we also get "completeness"
since if P succeeds in correctness game with prob. 1
then iteration preserves it.
*)
section.
declare module P : Prover{M}.
declare module V : Verifier{M}.

axiom V_verify_ll : islossless V.verify.
axiom V_challenge_ll : islossless V.challenge.
axiom P_commit_ll : islossless P.commit.
axiom P_response_ll : islossless P.response.


lemma iterated_correctness_ph (p : real) ia  :  
 (phoare[ Correct(P,V).run : arg = ia ==> res ] = p) 
   => forall e, 0 <= e =>
   phoare[ M(Correct(P,V)).whp : arg = (ia,[!],1,e+1,true) 
       ==> res ] = (p ^ (e+1)).
proof. move => H1 e ep .
have fact1  : phoare[ M(Correct(P,V)).whp_if_end : arg = (ia,[!],1,e,true) ==> res ] = (p ^ (e+1)).
conseq (asdsad (Correct(P,V)) _  p  ia true [!] _ _ e ep ). 
proc. 
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
simplify. conseq H1. auto.
conseq (whp_split_if_end' (Correct(P,V)) _ [!] ia 1 e true (p^(e+1))  (fun x => x) _). 
proc.
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
apply fact1.
qed.

lemma iterated_correctness_le_ph (p : real) ia  :  
 (phoare[ Correct(P,V).run : arg = ia ==> res ] <= p) 
   => forall e, 0 <= e =>
   phoare[ M(Correct(P,V)).whp : arg = (ia,[!],1,e+1,true) 
       ==> res ] <= (p ^ (e+1)).
proof. move => H1 e ep .
have fact1  : phoare[ M(Correct(P,V)).whp_if_end : arg = (ia,[!],1,e,true) ==> res ] <= (p ^ (e+1)).
conseq (asdsad_le (Correct(P,V)) _  p  ia true [!] _ _ e ep ). 
proc. 
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
simplify. conseq H1. auto.
conseq (whp_split_if_end_le (Correct(P,V)) _ [!] ia 1 e true (p^(e+1))  (fun x => x) _). 
proc.
call V_verify_ll.
call P_response_ll.
call V_challenge_ll.
call P_commit_ll.
skip. auto.
apply fact1.
qed.

end section.
