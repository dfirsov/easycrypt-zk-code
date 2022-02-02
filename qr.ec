pragma Goals:printall.
require import AllCore DBool Bool List.


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


lemma exp_lemmaaa : equiv[ Exp.main1 ~ Exp.main2 : true ==> ={res} /\ (res{2}.`2 = false => res{1}.`1 = res{2}.`1) ].
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



module type VerifierA = {
  proc challenge(N : int, y : int, c : int) : bool  
  proc summitup(c : int, b : bool, r : int) : bool list
}.




module type Simulator = {
  proc simulate(N : int, y : int) : bool list
}.




module QRP(P : Prover, V : Verifier) = {
  var c, r : int
  var b, result : bool
  proc main(N : int, y : int) = {
    c <- P.commit(N, y);  
    b <- V.challenge(N,y,c);
    r <- P.response(b);
    result <- V.verify(c,b,r);  (*  *)
    return result;
  }
}.



op sqDist :  int -> int distr.
op sqRoot : int -> int -> int.


axiom qr_prop1 (Na ya z : int) : sqRoot Na ya = z => z * z = ya.
axiom qr_prop2 (Na ya z : int) : z * z = ya => sqRoot Na ya = z.


module HP : Prover = {
  var rr, n, y : int

  proc commit(n1 : int, y1 : int) : int = {  
    (n,y) <- (n1, y1);
    rr <$ sqDist n;
    return rr;
  }

  proc response(b : bool) : int = {
    return (sqRoot n rr) * (if b then (sqRoot n y) else 1);
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
 sqRoot Na ya =  z => hoare [ QRP(HP,HV).main : arg = (Na,ya) ==> res  ].
proof. move => qra.
proc.  inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress. rewrite qra. simplify. smt.
(* smt. *)
admit.
qed.


section.

declare module P : Prover.

lemma qrp_sound Na ya :
 sqRoot Na ya = 0 => phoare [ QRP(P,HV).main : arg = (Na,ya) ==> res ] = (1%r/2%r).
proof. move => qra.
proc. inline*. swap 6 -5.
admitted. 

end section.



section.

declare module V : VerifierA {HP}.



(*
?? transcript := network messages AND internal states

Defs:
- ZK wrt. transcript
- ZK wrt. transcript + output bitstring
- ZK wrt. output bitstring

All equiv.

*)



local module Inits = {
    
  proc init1(N : int, y : int) = {
    var z,c,b;
    b <$ {0,1};
    z  <$ sqDist N;    
    c  <- z * if b then y else 1;
    return (b, z);
  }

  proc init1_t(N : int, y : int) = {
    var z,c;
    z  <$ sqDist N;    
    c  <- z * if true then y else 1;
    return (true, c);
  }

  proc init1_f(N : int, y : int) = {
    var z,c;
    z  <$ sqDist N;    
    c  <- z * if false then y else 1;
    return (false, c);
  }
  
  
  proc init2(N : int, y : int) = {
    var z,b;
    b <$ {0,1};
    z  <$ sqDist N;    
    return (b, z);
  }  

  proc init2_t(N : int, y : int) = {
    var z;
    z  <$ sqDist N;    
    return (true, z);
  }    

  proc init2_f(N : int, y : int) = {
    var z;
    z  <$ sqDist N;    
    return (false, z);
  }    
  
}.


local lemma init_lemma_f :
 equiv[ Inits.init1_f ~ Inits.init2_f : ={arg} ==> ={res} ].
proof. proc. simplify.
wp.
rnd.
skip. progress;smt.
qed.


op inv : int -> int -> int.
local lemma init_lemma_t :
 equiv[ Inits.init1_t ~ Inits.init2_t : ={arg} ==> ={res} ].
proof. proc. simplify.
wp. simplify.
rnd (fun x => x * y{1}) (fun x => x * (inv N{1} y{1})). 
skip. progress;admit.
qed.




local module Sim1  = {
  var result : bool list



  proc sinit(N : int, y : int) : bool * int * int = {
    var rr,bb,zz;
    bb <$ {0,1};
    rr  <$ sqDist N;    
    zz  <- rr * if bb then (inv N y) else 1;
    return (bb,zz,rr);
  }

  proc simulate(N : int, y : int) : bool * bool list  = {
    var rr,z,b',b,ryb;

    (b',z,rr) <- sinit(N,y);
    b  <- V.challenge(N,y,z);
   

    ryb  <- (sqRoot N rr);
    result <- V.summitup(z,b,ryb); 
    return (b = b', result);    
  }
}.




local module Sim1'  = {
  var result : bool list

  proc sinit(N : int, y : int) : bool * int = {
    var rr,bb;
    rr  <$ sqDist N;    
    bb <$ {0,1};
    return (bb,rr);
  }
    
  proc simulate(N : int, y : int) : bool * bool list  = {
    var z,b',b,ryb,result;
  
    (b',z) <- sinit(N,y);
    
    b  <- V.challenge(N,y,z);

    ryb  <- (sqRoot N (z * (if b then y else 1)));
    result <- V.summitup(z,b,ryb); 
    return (b = b', result);
  }
}.


local lemma exss Na ya : equiv[ Sim1.sinit ~ Sim1'.sinit : ={arg} /\ arg{1} = (Na,ya) ==> (res{1}.`1, res{1}.`2) = res{2} /\ (res{1}.`1 = true => res{1}.`2 = res{1}.`3 * (inv Na ya)) /\ (res{1}.`1 = false => res{1}.`2 = res{1}.`3 /\ res{1}.`2 = res{2}.`2)  ].
proof. proc. swap {2} 1 1.
seq 1 1 : (={N,y,bb} /\ (N{1},y{1}) = (Na,ya)). rnd. skip. auto.
exists* bb{1}. elim*. progress.
wp.

case (bb_L = true).
rnd  (fun x => x * (inv N{1} y{1})) (fun x => x * y{1}).  skip. progress.
admit. admit.  admit. admit.
progress. rnd. skip. progress . smt.
qed.



local lemma qkok Na ya P : 
  equiv [ Sim1.simulate ~ Sim1'.simulate : ={arg, glob V} /\ (Na,ya) = (N{1},y{1}) ==> res{1}.`1 /\ P res{1}.`2 => res{2}.`1 /\ P res{2}.`2   ].
proof. proc.

seq 1 1 : (={N,y,glob V,b',z} /\ (b'{1} = true => z{1} = rr{1} * (inv Na ya)) /\ (b'{2} = false => z{1} = rr{1} /\ z{1} = z{2}) ).

call (exss Na ya). skip. progress.

seq 1 1 : (={b,N,y,glob V,b',z} /\ (b'{1} = true => z{1} = rr{1} * (inv Na ya)) /\ (b'{2} = false => z{1} = rr{1} /\ z{1} = z{2})).
call (_:true). skip. progress.

exists* b'{1}. elim*. progress.

case (b'_L = true).
exists* b{1}. elim*. progress.
case (b_L = true).


seq 1 1 : (={b,N,y,glob V,b',z,ryb} /\ (b'{1} = true => z{1} = rr{1} * (inv Na ya)) /\ (b'{2} = false => z{1} = rr{1} /\ z{1} = z{2})).
wp. skip. progress. rewrite H. auto.

  call (_:true). skip. progress.

sp.



seq 1 1 : ((b'_L = b'{1} /\ ={N, y, b', glob V}) /\ b'_L = true /\ rr{2} *  inv N{2} y{2} = rr{1} ).


skip. progress. admit.
admit.
admit.
admit.
admit.
sp.

conseq (_:  z{1} = rr{1} * inv N{1} y{1} /\ b'{1} = true /\ ={N, y, b', glob V} /\ rr{2} * inv N{2} y{2} = rr{1} ==> _).
smt.

seq 1 1 : (z{1} = rr{1} * inv N{1} y{1} /\ b'{1} = true /\ ={N, y, b', b, glob V} /\ rr{2} * inv N{2} y{2} = rr{1}).
call (_:true). skip. progress.


module ZK(P : Prover, V : VerifierA) = {
  proc main(N : int, y : int) = {
    var c,b,r,result;
    c <- P.commit(N, y);  
    b <- V.challenge(N,y,c);
    r <- P.response(b);
    result <- V.summitup(c,b,r); 
    return result;
  }
}.



local lemma qrp_zk2_eq Na ya : equiv [ZK(HP, V).main ~ Sim1'.simulate
    : ={arg, glob V} /\ arg{1} = (Na, ya) ==> 
        res{1} = res{2}.`2 ].
proc.
inline*. sp.
call (_:true).
wp. call (_:true).
wp. swap {2} 2 -1.
rnd. rnd {2}. skip. progress.
qed.


local lemma qrp_zk2_pr &m Na ya a :
    Pr[ZK(HP, V).main(Na,ya) @ &m : res = a ] 
     = Pr[ Sim1'.simulate(Na,ya) @ &m : res.`2 = a ].
proof. byequiv.
conseq (_: _ ==> res{1} = res{2}.`2 ). progress.
conseq (qrp_zk2_eq Na ya). auto. auto. auto.
qed.






local lemma qrp_zk Na ya : equiv [ZK(HP, V).main ~ Sim1.simulate : ={arg} /\ arg{1} = (Na, ya) ==> 
  ={res} ].
proof.
proc.  inline*.
admitted.





(* rewinds Sim1 N times *)
local module SimN = {


    
}.


end section.

