pragma Goals:printall.
require import AllCore DBool Bool.


(*
- computationally unbounded
- knows the proof
- wants to convinvce the verifier that the knows the proof

*)


(* require import Group. *)
(* clone import ZModPCyclic. *)



(* independence and group op *)
module Exp = {
  var b1, b2 : bool
  proc main1() = {
   b1 <$ {0,1};
   b2 <$ {0,1};
   return (b1, b2);
  }

  proc main2() = {
   b1 <$ {0,1};
   b2 <$ {0,1};
   return (b1 ^^  b2, b2);
  }
  
}.


lemma exp_lemma : equiv[ Exp.main1 ~ Exp.main2 : true ==> ={res} ].
proof. proc. swap 1 1.
rnd (fun x => x ^^ Exp.b2{1}). rnd. 
skip. progress;smt.
qed.





module type Prover = {
  proc commit() : int
  proc response(b : bool) : int
}.


module type Verifier = {
  proc challenge(c : int) : bool  
  proc verify(c : int, b : bool, r : int) : bool
}.


module QR_Protocol(P : Prover, V : Verifier) = {
  
  proc main() = {
    var c,b,r,result;
    c <- P.commit();  
    b <- V.challenge(c);
    r <- P.response(b);
    result <- V.verify(c,b,r);
    return result;
  }
}.



op zn :  int distr.

module HonestProver : Prover = {
    var c : int
  proc commit() : int = {  
    c <$ zn;
    return c*c;
  }

  proc response(b : bool) : int = {
    return c * (if b then witness else 1);
 } 
}.




module HonestVerifier : Verifier = {
  proc challenge(c : int) : bool = {
   var b : bool;
   b <$ {0,1};
   return b;
  }

  proc verify(c : int,b : bool, r : int) : bool = {
    return witness;
 } 
}.



