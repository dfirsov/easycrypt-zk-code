pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv.


(* https://crypto.stanford.edu/pbc/notes/numbertheory/qr.html *)


(*  
replace IsQR with IsSqRoot ((N, y), w)
add invertability assumption into qr_prop7
*)

op ZNS_dist :  int -> (int * int) distr.     (* ZN* *)
op inv : int -> int -> int.
op invertible : int -> int -> bool.


type qr_c  =  int * int.
type qr_w  = int.
type sbits.


op IsSqRoot (Ny : qr_c) (w : qr_w) = Ny.`2 %% Ny.`1  = (w * w) %% Ny.`1. 
op IsQR (Ny : qr_c) = exists w, IsSqRoot Ny w.


axiom d_prop0 N : is_uniform (ZNS_dist N).
axiom d_prop1 N r rr :  (r, rr) \in ZNS_dist N => r * r %% N = rr %% N.
axiom d_prop2 N r rr :  (r, rr) \in ZNS_dist N => (r, rr) = (r %% N, rr %% N).
axiom d_prop3 (N r rr : int) :  r * r %% N = rr %% N => (r %%N, rr %%N) \in ZNS_dist N.
axiom d_prop4 N r rr :  (r, rr) \in ZNS_dist N => invertible N rr.
axiom d_prop5 N : weight (ZNS_dist N) = 1%r.


axiom qr_prop1 (N x : int) : invertible N x => x * (inv N x) %% N = 1.
axiom qr_prop2 (N x y w : int) : invertible N y => IsSqRoot (N, y) w => invertible N w.
axiom qr_prop3 (N y w : int) : invertible N y => IsSqRoot (N, y) w => inv N (w * w %%N) %%N = (inv N w) * (inv N w) %%N.
axiom qr_prop4 (N y : int) : invertible N y => inv N y = inv N (y %%N).
axiom qr_prop5 (N x y r : int) : IsQR (N, x) => invertible N x => !IsQR (N, y) => invertible N y => x * y %% N <> r * r %% N.


lemma qr_prop11 (N x : int) : invertible N x => (inv N x) * x  %% N = 1.
proof.  smt. qed.


(*
- computationally unbounded
- knows the proof
- wants to convinvce the verifier that he knows the proof
*)
module type Prover = {
  proc commit(Ny : qr_c, w : int) : int
  proc response(b : bool) : int
}.

module type Verifier = {
  proc challenge(Ny : qr_c, c : int) : bool  
  proc verify(c : int, b : bool, r : int) : bool
}.


module type VerifierA = {
  proc challenge(Ny : qr_c, c : int) : bool  
  proc summitup(c : int, b : bool, r : int) : bool list
}.


module type Simulator = {
  proc simulate(Ny : qr_c) : bool list
}.


(* correctness *)
module Correct(P : Prover, V : Verifier) = {
  var c, r : int
  var b, result : bool
  proc main(Ny:qr_c, w : int) = {
    c <- P.commit(Ny,w);  
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.verify(c,b,r);  
    return result;
  }
}.

(* honest prover  *)
module HP : Prover = {
  var r,rr, n, y, w : int

  proc commit(Ny1 : qr_c, w1 : int) : int = {  
    (n,y,w) <- (Ny1.`1,Ny1.`2, w1);
    (r,rr) <$ ZNS_dist n;
    return rr;
  }

  proc response(b : bool) : int = {
    return (r * (if b then w else 1)) %% n;
 } 
 proc getState() : sbits = {
   return witness;
 }

 proc setState(s : sbits) : unit = {
     (HP.n, HP.r, HP.rr, HP.w, HP.y) <- witness;
 }
}.

(* honest verifier *)
module HV : Verifier = {
  var n,y : int

  proc challenge(Ny1 : qr_c, c : int) : bool = {
   var b : bool;
   (n,y) <- (Ny1.`1,Ny1.`2);
   b <$ {0,1};
   return b;
  }

  proc verify(c : int,b : bool, r : int) : bool = {
    return  (if b then invertible n c /\ invertible n y /\ (c * y)  %% n = (r * r) %% n else invertible n c /\ (c %% n) = (r * r)%%n);
 } 
}.


lemma qr_complete_h Na ya wa : IsSqRoot (Na, ya) wa => invertible Na ya
   => hoare [ Correct(HP,HV).main : arg = ((Na,ya),wa) ==> res ].
move => qra invrtbl.
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.   smt.  
 have f : ya %% Na = (w{hr} * w{hr}) %% Na.
apply qra. 
clear qra. 
rewrite - (modzMml rrr.`2 ya Na).   
rewrite -  (d_prop1 Na rrr.`1 rrr.`2). smt.
rewrite (modzMml (rrr.`1 * rrr.`1) ya Na ).
smt (modzMml modzMmr modzMm). smt (d_prop4). smt (d_prop1 modzMml modzMmr modzMm).
qed.



lemma qr_complete_ph Na ya wa : IsSqRoot (Na, ya) wa => invertible Na ya
   => phoare [ Correct(HP,HV).main : arg = ((Na,ya),wa) ==> res ] = 1%r.
move => qra invrtbl. 
proc*.
seq 1 : (true) 1%r 1%r 1%r 0%r (r).
call (qr_complete_h Na ya wa). auto.
conseq (_: true ==> true). inline*. sp. 
wp.  progress. rnd. simplify.
conseq (_: true ==> true). smt.
wp.  rnd. skip. simplify.
progress. apply d_prop5. auto. auto. auto.
qed.


section.
declare module P : Prover {HV,Correct}.

axiom P_ax1 : islossless P.commit.
axiom P_ax2 : islossless P.response.

lemma qr_sound_ph Na ya :
 !IsQR (Na, ya) => phoare [ Correct(P,HV).main : arg = ((Na,ya),witness) ==> res ] <= (1%r/2%r).
proof. move => qra.
proc. inline*. 
wp.
seq 4 : ((Ny) = (Na,ya) /\ HV.y = Ny.`2 /\ HV.n = Ny.`1) (1%r) (1%r/2%r) (0%r) (1%r).  auto.
auto.
exists* Correct.c. elim*. move => cv.
case (!IsQR (Na, cv)).
seq 1 : (!b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = Correct.c /\ Ny = (Na,ya) /\ HV.y = Ny.`2 /\ HV.n = Ny.`1 /\ !IsQR (Na, cv)).
rnd.  skip. auto.
hoare. call (_:true ==> true). auto.
wp. auto. progress. rewrite H0. simplify.   
have : forall (w : int), Correct.c{hr} %% HV.n{hr} <> w * w %% HV.n{hr}. clear qra H0. 
   move => w.  
  case (Correct.c{hr} %% HV.n{hr} = w * w %% HV.n{hr}). move => ass.
  simplify. apply H. rewrite /IsQR. exists w. rewrite /IsSqRoot. apply ass. auto.
progress. smt. 
simplify.
rnd. skip. smt.
conseq (_: _ ==> true). call (_: true ==> true). auto. 
wp. skip. auto. auto.
  simplify.
seq 1 : (b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = Correct.c /\ (Ny) = (Na,ya) /\ IsQR (Na, cv) /\ HV.y = Ny.`2 /\ HV.n = Ny.`1). 
rnd. skip. auto.
hoare. 
call (_:true ==> true). auto.  
wp. skip. progress. rewrite H0. simplify. 
smt (qr_prop5).
rnd. skip. progress. smt.
conseq (_: _ ==> true). call (_:true ==> true). auto.
wp. skip. auto. auto.
hoare.
simplify. auto. call (_ : true ==> true).  auto. skip. auto. auto.
qed.


end section.


(* one-time simulator  *)
module Sim1(V : VerifierA)  = {
  var result : bool list

  proc sinit(N : int, y : int) : bool * int * int = {
    var r,rr,bb;
    (r,rr)  <$ ZNS_dist N;    
    bb <$ {0,1};
    return (bb,(rr * if bb then (inv N y) else 1) %% N,r);
  }

  proc simulate(Ny : int * int) : bool * bool list  = {
    var r,z,b',b,ryb;
    (b',z,r) <- sinit(Ny);
    b  <- V.challenge(Ny,z);   
    ryb  <- r %% Ny.`1;
    result <- V.summitup(z,b,ryb); 
    return (b = b', result);    
  }
}.



section.

declare module V : VerifierA {HP}.

axiom summitup_ll :  islossless V.summitup.
axiom challenge_ll :  islossless V.challenge.


local module Sim1'  = {
  var result : bool list

  proc sinit(N : int, y : int) : bool * int * int  = {
    var r,rr,bb;
    (r,rr)  <$ ZNS_dist N;    
    bb <$ {0,1};
    return (bb,rr %% N,r);
  }
    
  proc simulate(Ny : int * int, w : int) : bool * bool list  = {
    var z,r,b',b,ryb,result;
    (b',z,r) <- sinit(Ny);
    b  <- V.challenge(Ny,z);
    ryb  <- (r * if b then w else 1) %% Ny.`1  ;
    result <- V.summitup(z,b,ryb);
    return (b = b', result);
  }

 proc allinone(Ny : int * int, w : int) = {
    var z,r,bb,rr,b',b,ryb,result;
    (r,rr)  <$ ZNS_dist Ny.`1;    
    bb <$ {0,1};
    b' <- bb;
    z <- rr %%Ny.`1;
    b  <- V.challenge(Ny,z);
    ryb  <- (r * if b then w else 1) %% Ny.`1  ;
    result <- V.summitup(z,b,ryb);
    return (b = b', result);

  }
}.


module ZK(P : Prover, V : VerifierA) = {
  proc main(Ny : int * int, w : int) = {
    var c,b,r,result;
    c <- P.commit((Ny.`1, Ny.`2),w);
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.summitup(c,b,r);
    return result;
  }
}.


local lemma qrp_zk2_eq Na ya wa : IsSqRoot (Na, ya) wa =>
  equiv [ZK(HP, V).main ~ Sim1'.simulate
         : ={arg, glob V} /\ arg{1} = ((Na, ya), wa)
          ==> res{1} = res{2}.`2 ].
move => isqr. proc.
inline*. sp.
call (_:true).
wp. call (_:true).
wp. swap {2} 2 -1.
rnd. rnd {2}. skip. progress. 
smt (d_prop2).
qed.



local lemma exss Na ya wa : IsSqRoot (Na, ya) wa => invertible Na ya =>
 equiv[ Sim1(V).sinit ~ Sim1'.sinit
   : ={arg} /\ arg{1} = (Na,ya) ==>
       (res{1}.`1, res{1}.`2) = (res{2}.`1, res{2}.`2)
        /\ (res{1}.`1 = true  => res{1}.`2 %% Na = res{1}.`3 * res{1}.`3 * (inv Na ya) %% Na
                /\ res{1}.`3 * (inv Na wa) %% Na  = res{2}.`3 %% Na )
        /\ (res{1}.`1 = false => res{1}.`2 %% Na = res{1}.`3 * res{1}.`3 %% Na
                /\ res{1}.`2  = res{2}.`2 
                /\ res{1}.`3  = res{2}.`3 ) ].
move => isqr invrtbl. proc. swap 2 -1.
seq 1 1 : (={N,y,bb} /\ (N{1},y{1}) = (Na,ya)). rnd. skip. auto.
exists* bb{1}. elim*. progress.
wp. case (bb_L = true).     
rnd (fun (x : int * int) => (x.`1 * inv N{1} wa %% N{1}, x.`2 * (inv N{1} y{1}) %% N{1} ))
      (fun (x : int * int) => (x.`1 * wa %% N{1}, x.`2 * y{1} %% N{1})). skip. progress.
have ->: rrrR = (rrrR.`1 %% N{2}, rrrR.`2 %% N{2}). smt (d_prop2).
simplify. split. 
  have : invertible N{2} wa.  smt.
move => iwa. 
have ->:  rrrR.`1 %% N{2} * wa %% N{2} * inv N{2} wa %% N{2}
 =  (rrrR.`1  * wa  * inv N{2} wa) %% N{2}.
smt (modzMml modzMmr modzMm).
have ->: rrrR.`1 * wa * inv N{2} wa = rrrR.`1 * (wa * inv N{2} wa).
smt.
smt (modzMml modzMmr modzMm qr_prop1).
have ->:  rrrR.`2 %% N{2} * y{2} %% N{2} * inv N{2} y{2} %% N{2}
 =  (rrrR.`2  * y{2}  * inv N{2} y{2}) %% N{2}.
smt (modzMml modzMmr modzMm).
have ->: rrrR.`2 * y{2} * inv N{2} y{2} = rrrR.`2 * (y{2} * inv N{2} y{2}).
smt.
smt (modzMml modzMmr modzMm qr_prop1).
apply (d_prop0 N{2}). auto.
apply (d_prop3 N{2}).
 have ->: rrrR.`1 * wa * (rrrR.`1 * wa) =
(rrrR.`1 * rrrR.`1) * (wa *  wa). smt.
 have ->: (rrrR.`1 * rrrR.`1) * (wa *  wa) %%N{2}
 = (rrrR.`1 * rrrR.`1) %%N{2} * ( wa *  wa) %%N{2}. 
smt (modzMml modzMmr modzMm).
 have ->: (rrrR.`1 * rrrR.`1) %%N{2} = (rrrR.`2) %%N{2}.
  smt.
have ->: rrrR.`2 %% N{2} * ( wa *  wa) %% N{2}
 = ( wa *  wa) %% N{2} * rrrR.`2 %% N{2}. 
smt (modzMml modzMmr modzMm).
rewrite - isqr. 
smt (modzMml modzMmr modzMm).
apply d_prop3. 
have f1 : invertible N{2} wa. smt.
clear H H0.
 have ->: rrrL.`1 * inv N{2} wa * (rrrL.`1 * inv N{2} wa) =
(rrrL.`1 * rrrL.`1) * (inv N{2} wa * inv N{2} wa). smt.
 have ->: (rrrL.`1 * rrrL.`1) * (inv N{2} wa * inv N{2} wa) %%N{2}
 = (rrrL.`1 * rrrL.`1) %%N{2} * (inv N{2} wa * inv N{2} wa) %%N{2}. 
smt (modzMml modzMmr modzMm).
 have ->: (rrrL.`1 * rrrL.`1) %%N{2} = (rrrL.`2) %%N{2}.
  smt.
have ->: rrrL.`2 %% N{2} * (inv N{2} wa * inv N{2} wa) %% N{2}
 = (inv N{2} wa * inv N{2} wa) %% N{2} * rrrL.`2 %% N{2}.
smt (modzMml modzMmr modzMm).
have ->: inv N{2} wa * inv N{2} wa %% N{2}
 = inv N{2} y{2} %% N{2}. 
rewrite -  (qr_prop3 N{2} y{2} wa).    auto.
auto. rewrite - isqr. smt (qr_prop4). 
smt (modzMml modzMmr modzMm).
have ->: rrrL = (rrrL.`1 %% N{2}, rrrL.`2 %% N{2}). smt (d_prop2).
simplify. split. 
  have : invertible N{2} wa.  smt.
move => iwa. 
have ->:  rrrL.`1 %% N{2} *  inv N{2} wa %% N{2} * wa %% N{2}
 =  (rrrL.`1  * inv N{2} wa * wa ) %% N{2}.
smt (modzMml modzMmr modzMm).
have ->: rrrL.`1 * inv N{2} wa * wa = rrrL.`1 * (wa * inv N{2} wa).
smt.
smt (modzMml modzMmr modzMm qr_prop1).
have ->:  rrrL.`2 %% N{2} *  inv N{2} y{2} %% N{2} * y{2} %% N{2}
 =  (rrrL.`2  * inv N{2} y{2} * y{2} ) %% N{2}.
smt (modzMml modzMmr modzMm).
have ->: rrrL.`2 * inv N{2} y{2} * y{2} = rrrL.`2 * (y{2} * inv N{2} y{2}).
smt.
smt (modzMml modzMmr modzMm qr_prop1).
smt.
have ->: rrrL.`2 * inv N{2} y{2} %% N{2} %% N{2} 
  = rrrL.`2 * inv N{2} y{2} %% N{2} . smt.
have ->:  rrrL.`2 * inv N{2} y{2} %% N{2}
     = rrrL.`2 %%N{2} * inv N{2} y{2} %% N{2}. smt.  
have <-: rrrL.`1 * rrrL.`1 %%N{2} = rrrL.`2 %%N{2} . smt.  
smt (modzMml modzMmr modzMm d_prop1).
smt. 
rnd. skip. progress. smt. smt. smt.
have ->: rrrL.`2  %% N{2} %% N{2} 
  = rrrL.`2  %% N{2} . smt.
smt (d_prop1).
qed.


local lemma qkok Na ya wa P : IsSqRoot (Na, ya) wa => invertible Na ya =>
  equiv [ Sim1(V).simulate ~ Sim1'.simulate
   :   ={glob V} /\ (Na,ya) = (Ny{1}) /\ ((Na,ya),wa) = (Ny{2},w{2})
       ==> (res{1}.`1 /\ P res{1}.`2) <=> (res{2}.`1 /\ P res{2}.`2) ].
move => isqr invrtbl. proc.
seq 1 1 : (={Ny,glob V,b',z} 
         /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na
                     /\ r{1} * (inv Na wa) %% Na = r{2} %% Na )
         /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2})
         /\ ((Na, ya),wa) = (Ny{2},w{2}) ).
call (exss Na ya wa). skip. progress. smt.  smt.     
seq 1 1 : (={b,Ny,glob V,b',z} 
         /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na
                     /\ r{1} * (inv Na wa) %% Na = r{2} %% Na )
         /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2})
         /\ ((Na, ya),wa) = (Ny{2},w{2}) ).
call (_:true). skip. progress.
exists* b'{1}. elim*. progress.
case (b'_L = true).
exists* b{1}. elim*. progress.
case (b_L = true).    
seq 1 1 : (={ryb,b,Ny,glob V,b',z} 
         /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na
                     /\ r{1} * (inv Na wa) %% Na = r{2} %% Na )
         /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2})
         /\ ((Na, ya),wa) = (Ny{2},w{2}) ).
wp. skip. progress.    
have : r{1} * inv Na w{2} %% Na = r{2} %% Na.  smt.
move => qq. clear H H0. 
have : r{1} * inv Na w{2} %% Na * w{2} = r{2} %% Na * w{2}.
smt. clear qq. move => qq. 
have : r{1} * inv Na w{2} %% Na * w{2} %% Na = r{2} %% Na * w{2} %% Na.
smt. clear qq. move => qq.
have : invertible Na w{2}. smt.
move => iwa.
have <-: r{1} * inv Na w{2} %% Na * w{2} %% Na = r{1} %% Na.
  have ->: r{1} * inv Na w{2} %% Na * w{2} %% Na
          = r{1} * inv Na w{2} * w{2} %% Na.
smt (modzMml modzMmr modzMm qr_prop1).
  have ->: r{1} * inv Na w{2} * w{2} = r{1} * (inv Na w{2} * w{2}).
  smt .
      smt (modzMml modzMmr modzMm qr_prop11).
      smt (modzMml modzMmr modzMm ).
         smt. smt.
auto. call (_:true). skip. progress. sp.
conseq (_: b{1} <> b'{1} ==> b{1} <> b'{1}). smt. smt.
call {1}  (_: true ==> true). apply summitup_ll. 
call {2}  (_: true ==> true). apply summitup_ll. 
skip. auto.
exists* b{1}. elim*. progress.
case (b_L = false).
sp. call (_:true). skip. progress. smt.
conseq (_: b{1} <> b'{1} ==> b{1} <> b'{1}). smt. smt.
call {1} (_: true ==> true). apply summitup_ll. 
call {2} (_: true ==> true). apply summitup_ll. 
wp. skip. auto.
qed.




local lemma ssim Na ya wa  : IsSqRoot (Na, ya) wa => invertible Na ya =>
 equiv [ Sim1(V).simulate ~ Sim1'.simulate : ={glob V} /\ (Na,ya) = (Ny{1}) /\ ((Na,ya),wa) = (Ny{2},w{2}) ==> res.`1{1} = res.`1{2} ].
move => isr invr.
conseq (qkok Na ya wa (fun x => true) isr invr). smt.
qed.

local lemma sim1'not &m Na ya wa : 
     Pr[Sim1'.simulate((Na, ya), wa) @ &m : ! res.`1] = inv 2%r.
proof.
have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : ! res.`1] = Pr[Sim1'.allinone((Na, ya), wa) @ &m : ! res.`1]. byequiv. proc.
sim. wp.  inline*.  wp. rnd.  rnd.  wp. skip. progress. auto. auto.
byphoare. proc. inline*. simplify. 
swap [2..3] 4. wp.
seq 5 : true (1%r) (1%r/2%r) 1%r 0%r.
auto.
call summitup_ll. wp. 
call challenge_ll. wp. rnd. skip. smt. rnd. skip. progress.
smt. exfalso. auto. auto.  auto. auto.
qed.


lemma simnres Na ya wa : IsSqRoot (Na, ya) wa => invertible Na ya =>
  phoare[ Sim1(V).simulate : arg = (Na,ya) ==> !res.`1 ] = (1%r/2%r).
move => isr invr.
bypr. progress.
rewrite H. clear H.
have <-: Pr[Sim1'.simulate((Na, ya),wa) @ &m : ! res.`1] = inv 2%r.
apply sim1'not.
byequiv (_: _ ==> res.`1{1} = res.`1{2}). conseq (ssim Na ya wa isr invr). smt.  progress. smt.
qed.
  
    

local lemma qrp_zk2_pr_l &m Na ya wa q : IsSqRoot (Na, ya) wa =>
    Pr[ZK(HP, V).main((Na,ya),wa) @ &m : q res  ] 
     = Pr[ Sim1'.simulate((Na,ya),wa) @ &m : q res.`2  ].
proof. move => isqr. byequiv.
conseq (_: _ ==> res{1} = res{2}.`2). progress.
conseq (qrp_zk2_eq Na ya wa isqr).  progress. smt. smt.  auto. auto.
qed.



local lemma sd &m (P : bool list -> bool) Na ya wa : 
     Pr[ Sim1'.simulate((Na,ya),wa) @ &m : res.`1 /\ P res.`2 ]
    = (1%r/2%r) * Pr[ Sim1'.simulate((Na,ya),wa) @ &m : P res.`2 ].
have : Pr[ Sim1'.simulate((Na,ya),wa) @ &m : res.`1 /\ P res.`2 ]
 = Pr[ Sim1'.simulate((Na,ya),wa) @ &m : !res.`1 /\ P res.`2 ].
byequiv (_: ={glob Sim1',arg} ==> _).  
proc.  inline*.
call (_:true). wp. 
call (_:true). wp. 
rnd (fun x => !x). rnd. wp. skip. progress.
smt. smt. auto. auto.
have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : P res.`2] =
 Pr[Sim1'.simulate((Na, ya), wa) @ &m : res.`1 /\ P res.`2] +
   Pr[Sim1'.simulate((Na, ya), wa) @ &m : ! res.`1 /\ P res.`2].
rewrite Pr[mu_split res.`1]. 
have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : P res.`2 /\ res.`1]
 = Pr[Sim1'.simulate((Na, ya), wa) @ &m : res.`1 /\ P res.`2]. smt.
have ->: Pr[Sim1'.simulate((Na, ya), wa) @ &m : P res.`2 /\ !res.`1]
 = Pr[Sim1'.simulate((Na, ya), wa) @ &m : !res.`1 /\ P res.`2]. smt.
auto.
move => q.
rewrite - q. smt.
qed.
 


lemma sim1zk &m Na ya wa q :
  IsSqRoot (Na, ya) wa => invertible Na ya =>
       Pr[Sim1(V).simulate(Na, ya) @ &m : res.`1 /\  q res.`2] = Pr[ZK(HP, V).main((Na, ya), wa) @ &m : q res] / 2%r.
move => isr invr.
have ->: Pr[Sim1(V).simulate(Na, ya) @ &m : res.`1 /\ q res.`2]
 = Pr[Sim1'.simulate((Na,ya),wa) @ &m : res.`1 /\ q res.`2].
byequiv. 
conseq (qkok Na ya wa q isr invr). progress;smt. auto. auto.
rewrite (sd &m q Na ya wa).
rewrite (qrp_zk2_pr_l &m Na ya wa q isr). auto.
qed.

    
end section.

