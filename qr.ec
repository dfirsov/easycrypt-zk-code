pragma Goals:printall.
require import AllCore DBool Bool List Distr.


(*

https://crypto.stanford.edu/pbc/notes/numbertheory/qr.html


  *)

(* require import Group.  *)
(* clone import ZModPCyclic. *)
(* clone import ZModRing as Z. *)

op sqDist :  int -> int distr. 
op sqRoot :  int -> int -> int.
op inv : int -> int -> int.
op IsQR : int -> int -> bool.

axiom sqDistr_uni N :  is_uniform (sqDist N).
axiom sqDist_prop0 N x : IsQR N x => x \in sqDist N.
axiom sqDist_prop N x : x \in sqDist N => IsQR N x.
axiom qr_prop (N x : int) : IsQR N x => (sqRoot N x) * (sqRoot N x) = x.
axiom qr_prop1 (N x : int) : IsQR N x => x * (inv N x) = 1.
axiom qr_prop2 (N x : int) : IsQR N x => IsQR N (inv N x).
axiom qr_prop3 (N x y : int) : IsQR N x => IsQR N y => IsQR N (x * y).
axiom qr_prop4 (N : int) : sqRoot N 1 = 1.
axiom qr_prop5 (N x y : int) : IsQR N x => IsQR N y =>
  sqRoot N (x * y) = sqRoot N x * sqRoot N y.
axiom qr_prop6 (N x y r : int) : IsQR N x => !IsQR N y => (x * y) <> r * r.
axiom qr_prop7 (N y r : int) : !IsQR N y => y <> r * r.




(*
- computationally unbounded
- knows the proof
- wants to convinvce the verifier that he knows the proof
*)
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



(* correctness of quadratic resisdue protocol  *)
module Correct(P : Prover, V : Verifier) = {
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

(* honest prover  *)
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


lemma qrp_complete_ph Na ya : IsQR Na ya
   => hoare [ Correct(HP,HV).main : arg = (Na,ya) ==> res ].
move => qra.
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.  simplify. smt. smt. 
qed.


section.

declare module P : Prover {HV,Correct}.

axiom P_ax1 : islossless P.commit.
axiom P_ax2 : islossless P.response.

lemma qrp_sound Na ya :
 !IsQR Na ya => phoare [ Correct(P,HV).main : arg = (Na,ya) ==> res ] <= (1%r/2%r).
proof. move => qra.
proc. inline*. 
wp.
seq 5 : ((N,y) = (Na,ya) /\ HV.y = y) (1%r) (1%r/2%r) (0%r) (1%r). auto.
auto.
exists* Correct.c. elim*. move => cv.
case (!IsQR Na cv).
seq 1 : (!b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = Correct.c /\ (N,y) = (Na,ya) /\ HV.y = y /\ !IsQR Na cv).
rnd.  skip. auto.
hoare. call (_:true ==> true). auto.
wp. auto. progress. rewrite H0. simplify.  smt (qr_prop7 ). 
simplify.
rnd. skip. smt.
conseq (_: _ ==> true). call (_: true ==> true). auto. 
wp. skip. auto. auto.
  simplify.
seq 1 : (b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = Correct.c /\ (N,y) = (Na,ya) /\ IsQR Na cv /\ HV.y = y). 
rnd. skip. auto.
hoare. 
call (_:true ==> true). auto.  
wp. skip. progress. rewrite H0. simplify. 
apply (qr_prop6 N{hr} Correct.c{hr} y{hr} result). auto. auto.
rnd. skip. progress. smt.
conseq (_: _ ==> true). call (_:true ==> true). auto.
wp. skip. auto. auto.
hoare.
simplify. auto. call (_ : true ==> true).  auto.    skip. auto. auto.
qed.


end section.


section.

declare module V : VerifierA {HP}.

axiom summitup_ll :  islossless V.summitup.

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


local lemma exss Na ya : IsQR Na ya => equiv[ Sim1.sinit ~ Sim1'.sinit : ={arg} /\ arg{1} = (Na,ya) ==> (res{1}.`1, res{1}.`2) = res{2} /\ (res{1}.`1 = true => res{1}.`2 = res{1}.`3 * (inv Na ya)) /\ (res{1}.`1 = false => res{1}.`2 = res{1}.`3 /\ res{1}.`2 = res{2}.`2)  ].
proof. move => isqr. proc. swap {2} 1 1.
seq 1 1 : (={N,y,bb} /\ (N{1},y{1}) = (Na,ya)). rnd. skip. auto.
exists* bb{1}. elim*. progress.
wp.
case (bb_L = true).
rnd  (fun x => x * (inv N{1} y{1})) (fun x => x * y{1}).  skip. progress.
smt. smt. smt. smt. 
progress. rnd. skip. progress. smt.
qed.


local lemma qkok Na ya P : IsQR Na ya =>
  equiv [ Sim1.simulate ~ Sim1'.simulate
  : ={arg, glob V} /\ (Na,ya) = (N{1},y{1})
      ==> (res{1}.`1 /\ P res{1}.`2) <=> (res{2}.`1 /\ P res{2}.`2) ].
proof. move => isqr. proc.
seq 1 1 : (={N,y,glob V,b',z} /\ (b'{1} = true => z{1} = rr{1} * (inv Na ya)) /\ (b'{2} = false => z{1} = rr{1} /\ z{1} = z{2}) /\  (Na, ya) = (Na{2},y{2}) ).
call (exss Na ya). skip. progress.
seq 1 1 : (={b,N,y,glob V,b',z} /\ (b'{1} = true => z{1} = rr{1} * (inv Na ya)) /\ (b'{2} = false => z{1} = rr{1} /\ z{1} = z{2}) /\  (Na, ya) = (Na{2},y{2}) ).
call (_:true). skip. progress.
exists* b'{1}. elim*. progress.
case (b'_L = true).
exists* b{1}. elim*. progress.
case (b_L = true).
seq 1 1 : (={b,N,y,glob V,b',z,ryb} /\ (b'{1} = true => z{1} = rr{1} * (inv Na ya)) /\ (b'{2} = false => z{1} = rr{1} /\ z{1} = z{2}) /\  (Na, ya) = (Na{2},y{2})).
wp. skip. progress. rewrite H. auto.
smt.
auto.
  call (_:true). skip. progress.
sp.
conseq (_:   b{1} <> b'{1}
 ==> b{1} <> b'{1}). smt. smt.
call {1}  (_: true ==> true). apply summitup_ll. 
call {2}  (_: true ==> true). apply summitup_ll. 
   skip. auto.
exists* b{1}. elim*. progress.
case (b_L = false).
sp. call (_:true). skip. progress.  smt.
conseq (_:   b{1} <> b'{1}
 ==> b{1} <> b'{1}). smt. smt.
call {1}  (_: true ==> true). apply summitup_ll. 
call {2}  (_: true ==> true). apply summitup_ll. 
wp.  skip. auto.
qed.


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


local lemma qrp_zk2_eq Na ya : IsQR Na ya => equiv [ZK(HP, V).main ~ Sim1'.simulate
    : ={arg, glob V} /\ arg{1} = (Na, ya) ==> 
        res{1} = res{2}.`2 ].
move => isqr. proc.
inline*. sp.
call (_:true).
wp. call (_:true).
wp. swap {2} 2 -1.
rnd. rnd {2}. skip. progress.
smt.
qed.


local lemma qrp_zk2_pr &m Na ya a : IsQR Na ya =>
    Pr[ZK(HP, V).main(Na,ya) @ &m : res = a ] 
     = Pr[ Sim1'.simulate(Na,ya) @ &m : res.`2 = a ].
proof. move => isqr. byequiv.
conseq (_: _ ==> res{1} = res{2}.`2). progress.
conseq (qrp_zk2_eq Na ya isqr). auto. auto. auto.
qed.



end section.

