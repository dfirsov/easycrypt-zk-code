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

op IsSqRoot (N y w : int) = y %% N  = (w * w) %% N. 
op IsQR (N y : int) = exists w, IsSqRoot N y w.


axiom d_prop0 N : is_uniform (ZNS_dist N).
axiom d_prop1 N r rr :  (r, rr) \in ZNS_dist N => r * r %% N = rr %% N.
axiom d_prop2 N r rr :  (r, rr) \in ZNS_dist N => (r, rr) = (r %% N, rr %% N).
axiom d_prop3 (N r rr : int) :  r * r %% N = rr %% N => (r %%N, rr %%N) \in ZNS_dist N.
axiom d_prop4 N r rr :  (r, rr) \in ZNS_dist N => invertible N rr.



axiom qr_prop1 (N x : int) : invertible N x => x * (inv N x) %% N = 1.
axiom qr_prop2 (N x y w : int) : invertible N y => IsSqRoot N y w => invertible N w.
axiom qr_prop3 (N y w : int) : invertible N y => IsSqRoot N y w => inv N (w * w %%N) %%N = (inv N w) * (inv N w) %%N.
axiom qr_prop4 (N y : int) : invertible N y => inv N y = inv N (y %%N).
axiom qr_prop5 (N x y r : int) : IsQR N x => invertible N x => !IsQR N y => invertible N y => x * y %% N <> r * r %% N.


lemma qr_prop11 (N x : int) : invertible N x => (inv N x) * x  %% N = 1.
proof.  smt. qed.


(*
- computationally unbounded
- knows the proof
- wants to convinvce the verifier that he knows the proof
*)
module type Prover = {
  proc commit(N : int, y : int, w : int) : int
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
  proc main(N : int, y : int, w : int) = {
    c <- P.commit(N, y,w);  
    b <- V.challenge(N,y,c);
    r <- P.response(b);
    result <- V.verify(c,b,r);  
    return result;
  }
}.

(* honest prover  *)
module HP : Prover = {
  var r,rr, n, y, w : int

  proc commit(n1 : int, y1 : int, w1 : int) : int = {  
    (n,y,w) <- (n1, y1, w1);
    (r,rr) <$ ZNS_dist n;
    return rr;
  }

  proc response(b : bool) : int = {
    return (r * (if b then w else 1)) %% n;
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
    return  (if b then invertible n c /\ invertible n y /\ (c * y)  %% n = (r * r) %% n else invertible n c /\ (c %% n) = (r * r)%%n);
 } 
}.

lemma qrp_complete_ph Na ya wa : IsSqRoot Na ya wa => invertible Na ya
   => hoare [ Correct(HP,HV).main : arg = (Na,ya,wa) ==> res ].
move => qra invrtbl.
proc. inline*.  wp. 
rnd. wp.  rnd.  wp. 
skip. progress.   
 have f : y{hr} %% N{hr} = (w{hr} * w{hr}) %% N{hr}.
apply qra. 
clear qra. smt( d_prop4).
rewrite - (modzMml rrr.`2 y{hr} N{hr}).   
rewrite -  (d_prop1 N{hr} rrr.`1 rrr.`2). smt.
rewrite (modzMml (rrr.`1 * rrr.`1) y{hr} N{hr} ).
smt (modzMml modzMmr modzMm). smt (d_prop4). smt (d_prop1 modzMml modzMmr modzMm).
qed.



section.
declare module P : Prover {HV,Correct}.

axiom P_ax1 : islossless P.commit.
axiom P_ax2 : islossless P.response.

lemma qrp_sound Na ya :
 !IsQR Na ya => phoare [ Correct(P,HV).main : arg = (Na,ya,witness) ==> res ] <= (1%r/2%r).
proof. move => qra.
proc. inline*. 
wp.
seq 5 : ((N,y) = (Na,ya) /\ HV.y = y /\ HV.n = N) (1%r) (1%r/2%r) (0%r) (1%r). auto.
auto.
exists* Correct.c. elim*. move => cv.
case (!IsQR Na cv).
seq 1 : (!b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = Correct.c /\ (N,y) = (Na,ya) /\ HV.y = y /\ HV.n = N /\ !IsQR Na cv).
rnd.  skip. auto.
hoare. call (_:true ==> true). auto.
wp. auto. progress. rewrite H0. simplify.   
have : forall (w : int), Correct.c{hr} %% N{hr} <> w * w %% N{hr}. clear qra H0. 
   move => w.  

  case (Correct.c{hr} %% N{hr} = w * w %% N{hr}). move => ass.
  simplify. apply H. rewrite /IsQR. exists w. rewrite /IsSqRoot. apply ass. auto.
progress. smt. 

simplify.
rnd. skip. smt.
conseq (_: _ ==> true). call (_: true ==> true). auto. 
wp. skip. auto. auto.
  simplify.
seq 1 : (b) (1%r/2%r) (0%r) (1%r/2%r) (1%r) (cv = Correct.c /\ (N,y) = (Na,ya) /\ IsQR Na cv /\ HV.y = y /\ HV.n = N). 
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



  (* 
  lemma nosmt modzMml: forall (m n d : int), m %% d * n %% d = m * n %% d.
  lemma nosmt modzMmr: forall (m n d : int), m * (n %% d) %% d = m * n %% d.
  lemma nosmt modzMm:
    forall (m n d : int), m %% d * (n %% d) %% d = m * n %% d.
  lemma nosmt modzNm: forall (m d : int), (- m %% d) %% d = (-m) %% d.
  lemma nosmt mulz_modr:
    forall (p m d : int), 0 < p => p * (m %% d) = p * m %% (p * d).
  lemma nosmt mulz_modl:
    forall (p m d : int), 0 < p => m %% d * p = m * p %% (d * p).

 *)


section.
declare module V : VerifierA {HP}.

axiom summitup_ll :  islossless V.summitup.

local module Sim1  = {
  var result : bool list

  proc sinit(N : int, y : int) : bool * int * int = {
    var r,rr,bb;
    (r,rr)  <$ ZNS_dist N;    
    bb <$ {0,1};
    return (bb,(rr * if bb then (inv N y) else 1) %% N,r);
  }

  proc simulate(N : int, y : int) : bool * bool list  = {
    var r,z,b',b,ryb;
    (b',z,r) <- sinit(N,y);
    b  <- V.challenge(N,y,z);   
    ryb  <- r %% N;
    result <- V.summitup(z,b,ryb); 
    return (b = b', result);    
  }
}.


local module Sim1'  = {
  var result : bool list

  proc sinit(N : int, y : int) : bool * int * int  = {
    var r,rr,bb;
    (r,rr)  <$ ZNS_dist N;    
    bb <$ {0,1};
    return (bb,rr %% N,r);
  }
    
  proc simulate(N : int, y : int, w : int) : bool * bool list  = {
    var z,r,b',b,ryb,result;
    (b',z,r) <- sinit(N,y);
    b  <- V.challenge(N,y,z);
    ryb  <- (r * if b then w else 1) %% N  ;
    result <- V.summitup(z,b,ryb);
    return (b = b', result);
  }
}.


module ZK(P : Prover, V : VerifierA) = {
  proc main(N : int, y : int, w : int) = {
    var c,b,r,result;
    c <- P.commit(N, y,w);
    b <- V.challenge(N,y,c);
    r <- P.response(b);
    result <- V.summitup(c,b,r);
    return result;
  }
}.


local lemma qrp_zk2_eq Na ya wa : IsSqRoot Na ya wa =>
  equiv [ZK(HP, V).main ~ Sim1'.simulate
         : ={arg, glob V} /\ arg{1} = (Na, ya, wa)
          ==> res{1} = res{2}.`2 ].
move => isqr. proc.
inline*. sp.
call (_:true).
wp. call (_:true).
wp. swap {2} 2 -1.
rnd. rnd {2}. skip. progress. 
smt (d_prop2).
qed.



local lemma exss Na ya wa : IsSqRoot Na ya wa => invertible Na ya =>
 equiv[ Sim1.sinit ~ Sim1'.sinit
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


local lemma qkok Na ya wa P : IsSqRoot Na ya wa => invertible Na ya =>
  equiv [ Sim1.simulate ~ Sim1'.simulate
   :   ={glob V} /\ (Na,ya) = (N{1},y{1}) /\ (Na,ya,wa) = (N{2},y{2},w{2})
       ==> (res{1}.`1 /\ P res{1}.`2) <=> (res{2}.`1 /\ P res{2}.`2) ].
move => isqr invrtbl. proc.
seq 1 1 : (={N,y,glob V,b',z} 
         /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na
                     /\ r{1} * (inv Na wa) %% Na = r{2} %% Na )
         /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2})
         /\ (Na, ya,wa) = (N{2},y{2},w{2}) ).

call (exss Na ya wa). skip. progress. smt.  smt. 
    
seq 1 1 : (={b,N,y,glob V,b',z} 
         /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na
                     /\ r{1} * (inv Na wa) %% Na = r{2} %% Na )
         /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2})
         /\ (Na, ya,wa) = (N{2},y{2},w{2}) ).


call (_:true). skip. progress.
exists* b'{1}. elim*. progress.
case (b'_L = true).
exists* b{1}. elim*. progress.
case (b_L = true).
    
seq 1 1 : (={ryb,b,N,y,glob V,b',z} 
         /\ (b'{1} = true => z{1} %% Na = r{1} * r{1} * (inv Na ya) %% Na
                     /\ r{1} * (inv Na wa) %% Na = r{2} %% Na )
         /\ (b'{2} = false => z{1} %% Na = r{1} * r{1} %% Na /\ r{1} = r{2})
         /\ (Na, ya,wa) = (N{2},y{2},w{2}) ).


wp. skip. progress.  
  
have : r{1} * inv N{2} w{2} %% N{2} = r{2} %% N{2}.  smt.
move => qq. clear H H0. 

have : r{1} * inv N{2} w{2} %% N{2} * w{2} = r{2} %% N{2} * w{2}.
smt. clear qq. move => qq. 
have : r{1} * inv N{2} w{2} %% N{2} * w{2} %% N{2} = r{2} %% N{2} * w{2} %% N{2}.
smt. clear qq. move => qq.
have : invertible N{2} w{2}. smt.
move => iwa.

have <-: r{1} * inv N{2} w{2} %% N{2} * w{2} %% N{2} = r{1} %% N{2}.
  have ->: r{1} * inv N{2} w{2} %% N{2} * w{2} %% N{2}
          = r{1} * inv N{2} w{2} * w{2} %% N{2}.
smt (modzMml modzMmr modzMm qr_prop1).
  have ->: r{1} * inv N{2} w{2} * w{2} = r{1} * (inv N{2} w{2} * w{2}).
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



local lemma qrp_zk2_pr &m Na ya wa a : IsSqRoot Na ya wa =>
    Pr[ZK(HP, V).main(Na,ya,wa) @ &m : res = a ] 
     = Pr[ Sim1'.simulate(Na,ya,wa) @ &m : res.`2 = a ].
proof. move => isqr. byequiv.
conseq (_: _ ==> res{1} = res{2}.`2). progress.
conseq (qrp_zk2_eq Na ya wa isqr ). auto. auto. auto.
qed.


end section.

