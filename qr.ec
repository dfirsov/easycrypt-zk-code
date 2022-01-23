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
  proc commit(N : int, y : int) : int
  proc response(b : bool) : int
}.


module type Verifier = {
  proc challenge(N : int, y : int, c : int) : bool  
  proc verify(c : int, b : bool, r : int) : bool
}.


module type Simulator = {
  proc simulate(N : int, y : int) : int * bool * int * bool
}.




module QRP(P : Prover, V : Verifier) = {
  var c, r : int
  var b, result : bool
  proc main(N : int, y : int) = {
    c <- P.commit(N, y);  
    b <- V.challenge(N,y,c);
    r <- P.response(b);
    result <- V.verify(c,b,r);
    return result;
  }
}.



op zn :  int -> int distr.
op qr : int -> int -> int option.

axiom qr_prop1 (Na ya z : int) : qr Na ya = Some z => z * z = ya.
axiom qr_prop2 (Na ya z : int) : z * z = ya => qr Na ya = Some z.


module HP : Prover = {
  var z, n, y : int

  proc commit(n1 : int, y1 : int) : int = {  
    (n,y) <- (n1, y1);
    z <$ zn n;
    return z*z;
  }

  proc response(b : bool) : int = {
    return z * (if b then (oget (qr n y)) else 1);
 } 
}.


module HV : Verifier = {
  var n,y : int

  proc challenge(n1 : int, y1 : int, c : int) : bool = {
   var b : bool;
   (n,y) <- (n1,y1);
   b <$ {0,1};
   return b;
  }

  proc verify(c : int,b : bool, r : int) : bool = {
    return (if b then c * y = r * r else c = r * r);
 } 
}.



lemma qrp_complt Na ya z :
 qr Na ya = Some z => hoare [ QRP(HP,HV).main : arg = (Na,ya) ==> res  ].
proof. move => qra.
proc.  inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress. rewrite qra. simplify.
(* smt. *)
admit.
qed.


section.

declare module P : Prover.

lemma qrp_sound Na ya :
 qr Na ya = None => phoare [ QRP(P,HV).main : arg = (Na,ya) ==> res ] = (1%r/2%r).
proof. move => qra.
proc. inline*. swap 6 -5.
admitted. 

end section.



section.

declare module V : Verifier.

module Sim : Simulator = {
  proc simulate(n : int, y : int) : int * bool * int * bool = {
    return witness;
  }
}.


lemma qrp_zk Na ya : equiv [QRP(HP, V).main ~ Sim.simulate : ={arg} /\ arg{1} = (Na, ya) ==> 
  (QRP.c,QRP.b,QRP.r, QRP.result){1} = res{2} ].

end section.
