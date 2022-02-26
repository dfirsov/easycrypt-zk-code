require import AllCore.

(* Dominique: prob to statement[in language]?


*)
type prob, wit, chal, com, resp, sbits.

(*  *)
module type Prover = {
  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.

(* module type GenProver = { *)
(*   proc *init() : unit *)
(*   (* proc rounds() : int *) *)
(*   proc interact(m : msg) : msg option *)
(* }. *)

(* module type GenVerifier = { *)
(*   proc *init() : unit *)
(*   proc interact(m: msg) : msg option *)
(*   proc result(): bool *)
(* } *)

(* module 3ToGen(HV: Verifier3) = { *)
(*   proc init() = HV.init() *)
(*   proc interact(m:msg) : msg  *)
(*   if (i==0) HV.comm *)
(*   ... *)
(*   if (i==3) 3ToGen.result = HV.finalmsgreaction(m) *)
(* } *)
(* proc result()  = {return 3ToGen.result} *)
(* } *)

(* module SeqComposeP(P : GenProver) : GenProver = { ... } *)

(* If P is e-sound, then SeqComposeV(HV,n) is e^n-sound 

M(Correct(P, HV : Verifier3)) = Correct(M(P), SeqComposeV(3ToGen(HV) : GenVerifier))

(!P. M(Correct(P, HV)) <= e) = (!P. Correct(M(P), SeqComposeV(HV)) <= e) = (!P. Correct(P, SeqComposeV(HV)))

pros of new approach: more general -> proofs harder

*)

(* AProver, aux in &m of state Pr exper*)
module type AProver = {
  proc commit(x : prob) : com
  proc response(ch : chal) : resp
}.


module type RewProver = {
  proc * setState(s : sbits) : unit
  proc getState() : sbits

  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.


module type HVerifier = {
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
}.

(* rename Verifier to AVerifier  *)
module type Verifier = {
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
  proc summitup(c : com, r : resp)   : sbits
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

(* Correctness

Prover  -> H..
Verifier -> H..

use for completeness only
Correct -> Completeness

*)
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



(* either give all arguments to V queries each time or only new ones
and store the previous ones in the state *)
module Soundness(P : AProver, V : Verifier) = {
  proc run(Ny:prob) = {
    var com,ch,resp,result;
    com <- P.commit(Ny);  
    ch <- V.challenge(Ny,com);
    resp <- P.response(ch);
    result <- V.verify(com,resp);  
    return result;
  }
}.



(* ZK -> ZK_Real
Verifier -> AVerifier

 *)
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


section.
declare module P : Prover{M}.
declare module V : Verifier{M}.

axiom V_verify_ll : islossless V.verify.
axiom V_challenge_ll : islossless V.challenge.
axiom P_commit_ll : islossless P.commit.
axiom P_response_ll : islossless P.response.

(* check if e+1 => e changes/simplifies the proof?

Honest Prover never depends on the initial state.

*)
lemma iterated_correctness_ph (p : real) ia  :  
 (phoare[ Correct(P,V).run : arg = ia ==> res ] = p) 

   => forall e, 0 <= e =>
   phoare[ M(Correct(P,V)).whp 
         : arg = (ia,[!],1,e+1,true) 
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
