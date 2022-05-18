pragma Goals:printall.
require import Int.

type rrt, irt, sbits.

module type Dist = {
  proc run(r:rrt) : bool
}.


module type Run = {
  proc init() : unit
  proc run(i:irt) : rrt
}.                                  

require WhileNoSuccess.
clone import WhileNoSuccess as IFB with 
  type rrt <- rrt,
  type irt <- irt,
  type iat <- (rrt -> bool) * irt * int * int * rrt,
  type sbits <- sbits.

import IM.

require PrIntervalToSum.
clone import PrIntervalToSum as PIT with type rt <- bool * rrt,
                                            type iat <- (rrt -> bool) * irt * int * int * rrt .

section.

declare module A : Run {W, DW}.
declare module D : Dist {A, W, DW}.

declare axiom A_ll : islossless A.run.
declare axiom A_rew_ph x : phoare[ A.run : (glob A) = x ==> (glob A) = x ] = 1%r.

declare axiom D_ll : islossless D.run.

lemma if_whp_prop : 
  equiv [ W(A).whp ~ W(A).if_whp : ={glob W, glob A, arg} ==>  ={glob W, glob A, res} ].
proc. inline*.
unroll {1} 2.
sp.
if. progress.
seq 2 8 : (={glob A, glob W} /\ e{1} = e0{2} /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} 
  /\ e{2} = e0{2} /\ p{2} = p0{2} /\ r{2} = r0{2} /\ i{2} = i0{2} ).
wp.  call (_:true). skip. progress.
wp.
 while (={glob A, glob W} /\ e{1} = e0{2} /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} ).
wp.
call (_: true). skip. progress.
skip. progress.
sp.
rcondf {1} 1. progress.
rcondf {2} 1. progress. wp. skip. progress. 
qed.


lemma whp_if_prop : 
  equiv [ W(A).whp ~ W(A).whp_if : ={glob W, glob A, arg} ==>  ={glob W, glob A, res} ].
proc.
inline*. sp. 
case (s{2} <= e{2}).
splitwhile {1} 1 : (W.c <= e-1).
seq 1 1 : (={W.c, glob A,e,p,i} /\ e{1} = e0{2} + 1  /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} /\ (! p r => W.c = e){1}).
while (={W.c, glob A,e,p,i} /\ e{1} = e0{2} + 1 /\ p{1} = p0{2}  /\ r{1} = r0{2} /\ i{1} = i0{2} /\ (! p r => W.c <= e){1}).
wp. call (_:true). skip. progress.
smt. smt.
skip. progress. smt.
sp.
unroll {1} 1.
seq 1 1 : (={glob A, W.c,e,p,i} /\ ri{2} = r{1} /\ (! p{1} r{1} => W.c{1} = e{1}+1)). 
if. progress. wp. call (_:true). skip. progress. smt. skip. progress. smt.
rcondf {1} 1. progress. skip. progress. smt. skip. progress.
rcondf {1} 1. progress. skip. progress. smt.
rcondf {2} 1. progress. skip. progress. smt.
sp. 
rcondf {2} 1. progress. skip. progress. smt.
skip. progress.
qed.




lemma whp_split_prop : 
  equiv [ W(A).whp ~ W(A).whp_split : m{2} <= e{2}  /\ ={glob W, glob A, p, i, s, e, r}
        ==>  ={glob W, glob A, res} ].
proc.  inline*.
exists* m{2}. elim*. progress.
splitwhile {1} 2 : (W.c <= m_R).      
sp.
seq 1 1 : (={glob A, W.c,p,i,e} /\ m_R = m{2} /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r0{2} /\ p{1} = p0{2} /\ i{1} = i0{2}).
while (={glob A, W.c,p,i,e} /\ m_R = m{2}  /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r0{2} /\ p{1} = p0{2} /\ i{1} = i0{2}).
wp. call (_:true). skip. progress. smt. 
skip. progress. smt.
sp. 
wp.
while (={glob A, W.c,p,i,e} /\ m_R = m{2}  /\ e{2} = e1{2} /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r1{2} /\ p{1} = p1{2} /\ i{1} = i1{2}).
wp. call (_:true). skip. progress. 
skip. progress.
qed.


local module W0 = {
  proc run(a : irt ) = {
      var r, b;
      r <- A.run(a);
      b <- D.run(r);
      return (b, r);
  }
}.

local module W1 = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * rrt ) = {
      var r, b;
      r <- M.whp(a);
      b <- D.run(r);
      return (b, r);
  }
}.


local module W2 = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * int * rrt ) = {
      var r, b;
      r <- M.whp_split(a);
      b <- D.run(r);
      return (b, r);
  }
}.

local module W3 = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * rrt ) = {
      var r, b;
      r <- M.whp_if(a);
      b <- D.run(r);
      return (b, r);
  }
}.


local module W4 = {
  module M = W(A)
  proc run(a : (rrt -> bool) * irt * int * int * rrt ) = {
      var r;
      M.whp(a);
      r <- W0.run(a.`2);
      return r;
  }
}.

local lemma whp_premat_1_eq  pa ia sa ea ra ja : sa <= ja => ja <= ea + 1 =>
  equiv [ W(A).whp ~  W(A).whp_split : arg{1} = (pa,ia,sa,ja-1,ra) 
  /\ arg{2} = (pa,ia,sa,ja-1,ea,ra) /\  ={glob A} ==>  ((W.c = ja /\ pa res){1} /\ (W.c = ja /\ pa res){2} => ={res})    /\ (W.c = ja /\ pa res){1}  <=> (W.c = ja /\ pa res){2}  ].
proof. move => hp ph.
proc*.
inline W(A).whp_split. sp.
seq 1 1 : (={glob A, glob W} /\ p{1} = pa /\ p0{2} = pa /\ r0{1} = r1{2} /\ p{1} = p0{2} /\ e{1} = ja-1 /\ i{1} = i0{2} /\ s{1} = s0{2} /\ (!p r0 => W.c = e + 1){1} /\ e0{2} = ea).
inline*.  sp. wp.
while (={glob A, glob W} /\ (e0,p0,r1,i0){1} = (e1,p1,r2,i1){2} /\ (!p0 r1 => W.c <= e0 + 1){1}). wp. call (_:true). skip. progress.
smt. skip. progress. smt.
inline*.  sp.
case (pa r0{1}).
rcondf {2} 1. progress.  skip. progress. smt.
wp. skip. progress. wp.
conseq (_:  (p1{2} = pa /\ r2{2} = r0{1}) /\ ja  -1 <= e0{2}  /\  (! pa r0{1}) /\ W.c{1} = ja  /\ W.c{2} = W.c{1} /\ e1{2} = e0{2} /\ e1{2} = ea  ==> _ ). progress. smt.  smt.
case ((W.c <= e1 /\ ! p1 r2){2}).
unroll {2} 1. rcondt{2} 1. progress.
seq 0 2 : (ja < W.c{2} /\ ! pa r0{1}).
wp. call {2} (_: true ==> true). apply A_ll.
skip. progress. smt.
while {2} (ja < W.c{2} /\ ! pa r0{1}) (e1{2} + 1 - W.c{2}).
progress. wp. call (_: true ==> true). apply A_ll. skip. progress. smt. smt.
skip.    progress;smt.
rcondf {2} 1. progress. skip. smt. 
qed.




local lemma whp_premat_1 &m pa ia sa ea ra ja : sa <= ja => ja <= ea + 1 =>
  Pr[ W1.run(pa,ia,sa,ja-1,ra) @ &m : W.c = ja /\ pa res.`2 /\ res.`1 ]
   =   Pr[ W2.run(pa,ia,sa,ja-1,ea,ra) @ &m : W.c = ja /\ pa res.`2 /\  res.`1 ].
proof. move => hp ph.
byequiv. proc*. inline W1.run. inline W2.run. sp. wp. 
seq 1 1 : ( ={glob D} /\ ((W.c = ja/\ pa r0 ){1} <=> (W.c = ja/\ pa r0 ){2})  /\  (((W.c = ja/\ pa r0 ){1} /\ (W.c = ja/\ pa r0 ){2})  => ={r0})    ).
call (whp_premat_1_eq  pa ia sa ea ra ja hp ph). skip. smt.
case (W.c{1} = ja /\ pa r0{1}).
conseq (_: ={glob W, glob D, r0} ==> _). smt.
call (_:true). skip. smt. simplify.
call {1} (_: true ==> true ).  apply D_ll.
call {2} (_: true ==> true ).  apply D_ll.
skip. smt. auto.  auto.
qed.





local lemma whp_cap &m p i s ea r ja :  s <= ja => ja <= ea + 1 =>
   Pr[ W1.run(p,i,s,ea,r) @ &m : W.c = ja /\ p res.`2 /\ res.`1 ]  
   = Pr[ W1.run(p,i,s,ja-1,r) @ &m : W.c = ja /\ p res.`2 /\ res.`1 ].
proof.
move => sjp jap.
have ->:  Pr[ W1.run(p,i,s,ja-1,r) @ &m : W.c = ja /\ p res.`2 /\ res.`1 ]
  =   Pr[ W2.run(p,i,s,ja-1,ea,r) @ &m : W.c = ja /\ p res.`2 /\  res.`1 ].
apply whp_premat_1;auto.
byequiv (_: a{2} = (p, i, s, ja - 1, ea, r) /\
  (glob D){2} = (glob D){m} /\
  (glob A){2} = (glob A){m} /\
  a{1} = (p, i, s, ea, r) /\
  (glob D){1} = (glob D){m} /\ (glob A){1} = (glob A){m} /\ (glob W){1} = (glob W){2} ==> _).
proc*. inline W1.run W2.run. wp. sp.
seq 1 1 : (={glob W, glob D, r0}).
call whp_split_prop.
skip. progress. smt.
call (_:true). skip. progress. auto.
auto.
qed.


require import Real.

local lemma whp_cap_fin &m pa ia (ea : int) r ja   :
  2  <= ja     =>
  ja <= ea + 1 =>
  pa r = false =>
  (hoare[ A.run : (glob A) = (glob A){m} 
             ==> (glob A) = (glob A){m} ]) => 
   Pr[ W1.run(pa,ia,1,ea,r) @ &m : W.c = ja /\ pa res.`2 /\ res.`1 ]
     = (Pr[ A.run(ia) @ &m : !pa res ] ^ (ja - 2)) 
        * Pr[ W0.run(ia) @ &m : pa res.`2 /\ res.`1 ]. 
proof. progress.
have FG :  phoare[ W0.run : arg = ia /\ (glob A) = (glob A){m}  /\ (glob D) = (glob D){m}
  ==> pa res.`2 /\ res.`1 ] = Pr[ W0.run(ia) @ &m : pa res.`2 /\ res.`1 ].

bypr. move => &m0 [eq1 eq2].  rewrite eq1. rewrite -eq1.
byequiv (_: ={glob A, glob D, arg} ==> ={res}).  sim. auto. auto.

have FF : forall ea, 0 <= ea => phoare[ W(A).whp : 
   arg = (pa,ia,1,ea,r) /\ (glob A) = (glob A){m}
     ==> !pa res ] = (Pr[ A.run(ia) @ &m : !pa res ] ^ ea).
move => ea0 ea0p.
  conseq (final_zz_ph_m A _ _ &m Pr[A.run(ia) @ &m : ! pa res] pa ia ea0 r _ _ _). auto. apply A_ll. apply A_rew_ph. auto. auto. 
bypr. move => &m0 [eq1 eq2]. rewrite eq1. 
byequiv (_: ={arg, glob A} ==> ={res}). sim. progress. rewrite eq2.
auto. auto.

pose p1 := Pr[ W0.run(ia) @ &m : pa res.`2 /\ res.`1 ].

rewrite  (whp_cap &m pa ia 1 ea r ja ). smt. smt.
have ->: Pr[W1.run(pa, ia, 1, ja - 1, r) @ &m : W.c = ja /\ pa res.`2 /\ res.`1]
 = Pr[W3.run(pa, ia, 1, ja-1, r) @ &m : W.c = ja /\ pa res.`2 /\  res.`1].
byequiv (_: ={glob W(A), arg, glob D} ==> _). proc*. inline W1.run. 
inline W3.run. sp. wp. 
call (_:true). 
call whp_if_prop. skip. progress. 
auto. auto.


byphoare (_: arg = (pa, ia, 1, ja - 1, r) /\ (glob A) = (glob A){m} ==> _);auto.
proc. inline W3.M.whp_if. 
seq 3 : (! p ri) (Pr[ A.run(ia) @ &m : !pa res ] ^ (ja - 2))  p1 1%r 0%r (e = ja - 1 /\ W.c <= e  /\ i = ia /\ p = pa 
 /\ (!p ri => W.c = e)  /\  (glob A) = (glob A){m} );auto.
inline W(A).whp. sp.
wp.
while (W.c <= e0 + 1 /\  (glob A) = (glob A){m} ). wp. 
call H2.
   skip. progress. smt. skip. progress.   smt. smt.  
  call (FF (ja - 2)  ).  smt. wp. skip. progress.  
rcondt 1. skip. progress. simplify. 

admit.                          (* TODO: show that p1 = Pr[A @ m] * Pr[D @ m] then  *)
(* wp. call FG. skip. progress.  *)
(* smt. *)
hoare.
simplify.
if. wp. call (_:true ==> true). auto.
wp.  call (_:true ==> true).
auto. skip. smt.
call (_: true ==> true). auto. wp. skip.   smt.  
qed.


require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.




local module CAW = {
  proc run(a : (rrt -> bool) * irt * int * int * rrt) = {
    var r;
    r <@ W1.run(a);
    return r;
  }
}.


local lemma whp_cap_fin_int_sum_D &m ia pa M (ea : int) ra :
   Pr[ W1.run(pa,ia,1,ea,ra) @ &m : 1 < W.c <= ea + 1  /\ M res ] = 
    big predT
      (fun i => Pr[ W1.run(pa,ia,1,ea,ra) @ &m : W.c = i /\ M res ])
      (range 2 (ea + 2)).
progress.
pose f := fun (x : glob CAW) => x.`1.
have ->: Pr[ W1.run(pa,ia,1,ea,ra) @ &m : 1 < W.c <= ea + 1 /\ M res ]
  = Pr[ CAW.run(pa,ia,1,ea,ra) @ &m : 2 <= f (glob CAW) <= ea + 1  /\ M res ].
byequiv (_: ={arg, glob CAW} ==> ={res, glob CAW}). proc.
inline*. sp.  wp. 
progress.
sim. auto. smt. 
rewrite (pr_interval_to_sum_lemma CAW &m (pa, ia, 1, ea, ra) f (fun _ x _ => M x)).
simplify.
have <-:  (fun (i : int) => Pr[W1.run(pa, ia, 1, ea, ra) @ &m : W.c = i /\ M res])
 = (fun (i : int) =>
     Pr[CAW.run(pa, ia, 1, ea, ra) @ &m : f ( (glob CAW)) = i /\ M res]).
apply fun_ext. move => x.
byequiv (_: ={arg, glob CAW} ==> ={res, glob CAW}). proc.
inline*.  wp.  sp.
sim. auto. smt. 
auto.
qed.


lemma whp_cap_fin_int pa ia (ea : int) ra :
  pa ra = false => 1 <= ea =>
   phoare[ W(A).whp : arg = (pa,ia,1,ea,ra) ==> 1 < W.c <= ea + 1 ] = 1%r.
progress. proc. sp.
unroll 1.
rcondt 1. skip. smt.
seq 2 : (W.c = 2 /\ (p, i, s, e) = (pa, ia, 1, ea)).
wp. call (_: true ==> true). auto.
skip. auto.
wp. call (_: true ==> true). apply A_ll.
skip. progress.
while (1 < W.c && W.c <= e + 1) (e + 1 - W.c).
progress. 
wp. call (_: true ==> true). apply A_ll.
skip. progress. smt. smt. smt. skip. progress.
smt.  smt.
hoare. simplify.
wp. call (_: true ==> true). auto. skip. auto. auto. 
qed.


local lemma whp_cap_fin_int_D &m pa ia (ea : int) ra :
  pa ra = false => 1 <= ea =>
   Pr[ W1.run(pa,ia,1,ea,ra) @ &m : 1 < W.c <= ea + 1 ] = 1%r.
progress. byphoare (_: arg = (pa, ia, 1, ea, ra) ==> _).
proc.  call (_:true ==> true). apply D_ll. 
call (whp_cap_fin_int pa ia ea ra). skip. auto. auto. auto.
qed.


local lemma whp_cap_fin_sum' &m pa ia (ea : int) r :
  pa r = false =>
  1 <= ea =>
  hoare[ A.run : (glob A) = (glob A){m} 
           ==> (glob A) = (glob A){m} ] => 
  Pr[ W1.run(pa,ia,1,ea,r) @ &m : pa res.`2 /\ res.`1 ]  
     = big predT
        (fun i => (Pr[ A.run(ia) @ &m : !pa res ] ^ (i - 2)) 
          * Pr[ W0.run(ia) @ &m : pa res.`2 /\ res.`1 ]  )
        (range 2 (ea + 2)). 
proof. progress.
have ->: Pr[ W1.run(pa,ia,1,ea,r) @ &m : pa res.`2 /\ res.`1 ]  
 = Pr[ W1.run(pa,ia,1,ea,r) @ &m : (1 < W.c <= ea + 1) 
        /\ pa res.`2 /\ res.`1 ].
rewrite Pr[mu_split (1 < W.c && W.c <= ea + 1)].
  have ->: Pr[W1.run(pa, ia, 1, ea, r) @ &m :
   (pa res.`2 /\ res.`1) /\ ! (1 < W.c && W.c <= ea + 1)] = 0%r.
   have : Pr[W1.run(pa, ia, 1, ea, r) @ &m : ! (1 < W.c && W.c <= ea + 1)] = 0%r.
    have f3 : Pr[W1.run(pa, ia, 1, ea, r) @ &m : (1 < W.c && W.c <= ea + 1)] = 1%r. rewrite (whp_cap_fin_int_D &m). smt.
  smt. 
    have f2 : 1%r = Pr[W1.run(pa, ia, 1, ea, r) @ &m : ! (1 < W.c && W.c <= ea + 1)] + Pr[W1.run(pa, ia, 1, ea, r) @ &m : (1 < W.c && W.c <= ea + 1)]. 
    have  <- : Pr[W1.run(pa, ia, 1, ea, r) @ &m : true ] = 1%r.
    smt.
   rewrite Pr[mu_split (1 < W.c && W.c <= ea + 1)]. simplify.
   smt. auto. timeout 20. smt. smt. smt.
rewrite big_int_cond.
rewrite (whp_cap_fin_int_sum_D &m ia pa (fun x => pa (snd x) /\   fst x) ea r).
simplify.
rewrite big_int_cond.
apply eq_big. auto.
progress.
rewrite (whp_cap_fin &m).  auto. smt.
auto.
auto.
auto.
qed.


local lemma whp_cap_fin_sum'' &m pa ia (ea : int) r :
  pa r = false =>
  1 <= ea =>
  hoare[ A.run : (glob A) = (glob A){m} 
           ==> (glob A) = (glob A){m} ] => 
   Pr[ W1.run(pa,ia,1,ea,r) @ &m : pa res.`2 /\ res.`1 ]  
      = big predT
         (fun i => (Pr[ A.run(ia) @ &m : !pa res ] ^ i) 
           * Pr[ W0.run(ia) @ &m : pa res.`2 /\ res.`1 ])
         (range 0 ea). 
proof. progress.
rewrite (whp_cap_fin_sum' &m);auto.
rewrite (PIT.big_reindex (fun (i : int) =>
     Pr[A.run(ia) @ &m : ! pa res] ^ i * Pr[W0.run(ia) @ &m : pa res.`2 /\  res.`1]) 2 ea). auto.
qed.


local lemma whp_cap_fin_sum &m pa ia (ea : int) r :
  pa r = false =>
  hoare[ A.run : (glob A) = (glob A){m} 
           ==> (glob A) = (glob A){m} ] => 
  Pr[ W1.run(pa,ia,1,ea,r) @ &m : pa res.`2 /\ res.`1 ]  
     = big predT
        (fun i => (Pr[ A.run(ia) @ &m : !pa res ] ^ i) 
          * Pr[ W0.run(ia) @ &m : pa res.`2 /\ res.`1 ])
        (range 0 ea). 
proof.
case (1 <= ea).
progress. rewrite (whp_cap_fin_sum'' &m);auto.
progress.
have ->: bigi predT
  (fun (i : int) =>
     Pr[A.run(ia) @ &m : ! pa res] ^ i * Pr[W0.run(ia) @ &m : pa res.`2 /\ res.`1])
  0 ea = 0%r.
smt.
byphoare (_: arg = (pa, ia, 1, ea, r) ==> _).
hoare.
conseq (_: _ ==> ! pa res.`2). smt.
proc. sp. simplify. inline W1.M.whp. sp.
rcondf 1. skip. smt. call (_: true ==> true). auto. wp. skip. smt. auto. auto.
qed.



end section.
  
