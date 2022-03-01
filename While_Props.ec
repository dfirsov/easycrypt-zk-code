pragma Goals:printall.
require import Int.

type rrt, irt, sbits.


module type Run = {
  proc run(i:irt) : rrt
}.                                  

require Iterated_Failure_better.
clone import Iterated_Failure_better as IFB with 
  type rrt <- rrt,
  type irt <- irt,
  type iat <- (rrt -> bool) * irt * int * int * rrt,
  type sbits <- sbits.

import IM.

require Pr_interval_to_sum.
clone import Pr_interval_to_sum as PIT with type rt <- rrt,
                                            type iat <- (rrt -> bool) * irt * int * int * rrt .

section.

declare module A : Run {W, DW}.

axiom A_ll : islossless A.run.

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





local lemma whp_premat_1 q &m pa ia sa ea ra ja : sa <= ja => ja <= ea + 1 =>
  Pr[ W(A).whp(pa,ia,sa,ja-1,ra) @ &m : W.c = ja /\ pa res /\ q res ]
   =   Pr[ W(A).whp_split(pa,ia,sa,ja-1,ea,ra) @ &m : W.c = ja /\ pa res /\ q res ].
proof. move => hp ph.
byequiv.
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
skip. progress;smt.
rcondf {2} 1. progress. skip. smt. auto. auto.
qed.


lemma whp_cap q &m p i s ea r ja :  s <= ja => ja <= ea + 1 =>
   Pr[ W(A).whp(p,i,s,ea,r) @ &m : W.c = ja /\ p res /\ q res ] 
   =   Pr[ W(A).whp(p,i,s,ja-1,r) @ &m : W.c = ja /\ p res /\ q res ].
move => sjp jap.
have ->:  Pr[ W(A).whp(p,i,s,ja-1,r) @ &m : W.c = ja /\ p res /\ q res ] 
  =  Pr[ W(A).whp_split(p,i,s,ja-1,ea,r) @ &m : W.c = ja /\ p res  /\ q res] .
rewrite - whp_premat_1. auto. 
auto. auto.
byequiv (_: ={p,i,s,e,r, glob A, glob W} /\ e{2} = ea
    /\ m{2} = ja -1 /\ m{2} <= e{2} ==> _) .
conseq whp_split_prop.
progress.
progress.
progress.
smt. auto.
qed.


require import Real.
print final_zz_ph_m.
lemma whp_cap_fin &m pa q ia (ea : int) r ja   :
  2  <= ja     =>
  ja <= ea + 1 =>
  pa r = false =>

  (hoare[ A.run : (glob A) = (glob A){m} 
             ==> (glob A) = (glob A){m} ]) => 

   Pr[ W(A).whp(pa,ia,1,ea,r) @ &m 
           : W.c = ja /\ pa res /\ q res ]  
     = (Pr[ A.run(ia) @ &m : !pa res ] ^ (ja - 2)) 
        * Pr[ A.run(ia) @ &m : pa res /\ q res ]. 
proof. progress.

have FG :  phoare[ A.run : arg = ia /\ (glob A) = (glob A){m} 
  ==> pa res /\  q res ] = Pr[ A.run(ia) @ &m : pa res /\ q res ].
bypr. move => &m0 [eq1 eq2].  rewrite eq1.
byequiv (_: ={glob A, arg} ==> ={res}).  sim. auto. auto.


have FF : forall ea, 0 <= ea => phoare[ W(A).whp : 
   arg = (pa,ia,1,ea,r) /\ (glob A) = (glob A){m}
     ==> !pa res ] = (Pr[ A.run(ia) @ &m : !pa res ] ^ ea).
move => ea0 ea0p.
  conseq (final_zz_ph_m A _ &m Pr[A.run(ia) @ &m : ! pa res] pa ia ea0 r _ _ _). auto. apply A_ll. auto. auto. 
bypr. move => &m0 [eq1 eq2]. rewrite eq1. 
byequiv (_: ={arg, glob A} ==> ={res}). sim. progress. rewrite eq2.
auto. auto.
pose p1 := Pr[ A.run(ia) @ &m : pa res /\ q res ].
rewrite  (whp_cap q &m pa ia 1 ea r ja ). smt. smt.
have ->: Pr[W(A).whp(pa, ia, 1, ja-1, r) @ &m : W.c = ja /\ pa res /\ q res]
 = Pr[W(A).whp_if(pa, ia, 1, ja-1, r) @ &m : W.c = ja /\ pa res /\ q res].
byequiv (_: ={glob W(A), arg} ==> _) . conseq whp_if_prop. progress.  
progress. auto. auto.
 byphoare (_: arg = (pa, ia, 1, ja - 1, r) /\ (glob A) = (glob A){m} ==> _).
proc.
seq 2 : (! p ri) (Pr[ A.run(ia) @ &m : !pa res ] ^ (ja - 2))  p1 1%r 0%r (e = ja - 1 /\ W.c <= e  /\ i = ia /\ p = pa 
 /\ (!p ri => W.c = e)  /\  (glob A) = (glob A){m} ).
inline*. sp.
wp.
while (W.c <= e0 + 1 /\  (glob A) = (glob A){m} ). wp. 
call H2.
   skip. progress. smt. skip. progress.   smt. smt.  
  call (FF (ja - 2)  ).  smt. wp. skip. progress.  
rcondt 1. skip. progress. 
wp. call FG. skip. progress. 
smt.
hoare.
simplify.
if. wp. call (_:true ==> true). auto.
skip. smt.
skip. smt.  auto. auto. auto.
qed.


require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.

local module CA = {
  proc run(a : (rrt -> bool) * irt * int * int * rrt) = {
    var r;
    r <@ W(A).whp(a);
    return r;
  }

}.


lemma whp_cap_fin_int_sum &m ia pa M (ea : int) ra :
   Pr[ W(A).whp(pa,ia,1,ea,ra) @ &m : 1 < W.c <= ea + 1  /\ M res ] = 
    big predT
      (fun i => Pr[ W(A).whp(pa,ia,1,ea,ra) @ &m : W.c = i /\ M res ])
      (range 2 (ea + 2)).
progress.
pose f := fun (x : glob CA) => x.`1.
have ->: Pr[ W(A).whp(pa,ia,1,ea,ra) @ &m : 1 < W.c <= ea + 1  /\ M res ]
 = Pr[ CA.run(pa,ia,1,ea,ra) @ &m : 2 <= f (glob CA) <= ea + 1  /\ M res ].
byequiv (_: ={arg, glob CA} ==> ={res, glob CA}). proc.
inline*. sp.  wp. 
conseq (_: ={glob CA} /\ ={e, p, i} /\ r{1} = r0{2} ==> ={glob CA} /\ r{1} = r0{2}). smt. smt.
sim. auto. smt. 
rewrite (pr_interval_to_sum_lemma CA &m (pa, ia, 1, ea, ra) f (fun _ x _ => M x)).
simplify.
have <-: 
 (fun (i : int) => Pr[W(A).whp(pa, ia, 1, ea, ra) @ &m : W.c = i /\ M res])
 = (fun (i : int) =>
     Pr[CA.run(pa, ia, 1, ea, ra) @ &m : f (W.c, (glob A)) = i /\ M res]).
apply fun_ext. move => x.
byequiv (_: ={arg, glob CA} ==> ={res, glob CA}). proc.
inline*.  wp.  sp.
conseq (_: ={glob CA} /\ ={e, p, i} /\ r{1} = r0{2} ==> ={glob CA} /\ r{1} = r0{2}). smt. smt.
sim. auto. smt. 
auto.
qed.

   
lemma whp_cap_fin_int &m pa ia (ea : int) ra :
  pa ra = false => 1 <= ea =>
   Pr[ W(A).whp(pa,ia,1,ea,ra) @ &m : 1 < W.c <= ea + 1 ] = 1%r.
progress.
byphoare (_: arg = (pa, ia, 1, ea, ra) ==> _).
proc. sp.
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
wp. call (_: true ==> true). auto. skip. auto. auto. auto.
auto.
qed.


lemma whp_cap_fin_sum' &m pa q ia (ea : int) r :
  pa r = false =>
  1 <= ea =>
  hoare[ A.run : (glob A) = (glob A){m} 
           ==> (glob A) = (glob A){m} ] => 
  Pr[ W(A).whp(pa,ia,1,ea,r) @ &m : pa res /\ q res ]  
     = big predT
        (fun i => (Pr[ A.run(ia) @ &m : !pa res ] ^ (i - 2)) 
          * Pr[ A.run(ia) @ &m : pa res /\ q res ])
        (range 2 (ea + 2)). 
proof. progress.
have ->: Pr[ W(A).whp(pa,ia,1,ea,r) @ &m : pa res /\ q res ]  
 = Pr[ W(A).whp(pa,ia,1,ea,r) @ &m : (1 < W.c <= ea + 1) 
        /\ pa res /\ q res ].
rewrite Pr[mu_split (1 < W.c && W.c <= ea + 1)].
  have ->: Pr[W(A).whp(pa, ia, 1, ea, r) @ &m :
   (pa res /\ q res) /\ ! (1 < W.c && W.c <= ea + 1)] = 0%r.
   have : Pr[W(A).whp(pa, ia, 1, ea, r) @ &m : ! (1 < W.c && W.c <= ea + 1)] = 0%r.
    have f3 : Pr[W(A).whp(pa, ia, 1, ea, r) @ &m : (1 < W.c && W.c <= ea + 1)] = 1%r. rewrite (whp_cap_fin_int &m). smt.
  smt. 
    have f2 : 1%r = Pr[W(A).whp(pa, ia, 1, ea, r) @ &m : ! (1 < W.c && W.c <= ea + 1)] + Pr[W(A).whp(pa, ia, 1, ea, r) @ &m : (1 < W.c && W.c <= ea + 1)]. 
    have  <- : Pr[W(A).whp(pa, ia, 1, ea, r) @ &m : true ] = 1%r.
    smt.
   rewrite Pr[mu_split (1 < W.c && W.c <= ea + 1)]. simplify.
   smt. auto. timeout 20. smt. smt. smt.
rewrite big_int_cond.
rewrite (whp_cap_fin_int_sum &m ia pa (fun x => pa x /\ q x) ea r).
simplify.
rewrite big_int_cond.
apply eq_big. auto.
progress.
rewrite (whp_cap_fin &m).  auto. smt.
auto.
auto.
auto.
qed.


lemma whp_cap_fin_sum'' &m pa q ia (ea : int) r :
  pa r = false =>
  1 <= ea =>
  hoare[ A.run : (glob A) = (glob A){m} 
           ==> (glob A) = (glob A){m} ] => 
  Pr[ W(A).whp(pa,ia,1,ea,r) @ &m : pa res /\ q res ]  
     = big predT
        (fun i => (Pr[ A.run(ia) @ &m : !pa res ] ^ i) 
          * Pr[ A.run(ia) @ &m : pa res /\ q res ])
        (range 0 ea). 
progress.
rewrite (whp_cap_fin_sum' &m);auto.
rewrite (PIT.big_reindex (fun (i : int) =>
     Pr[A.run(ia) @ &m : ! pa res] ^ i * Pr[A.run(ia) @ &m : pa res /\ q res]) 2 ea). auto.
qed.


lemma whp_cap_fin_sum &m pa q ia (ea : int) r :
  pa r = false =>
  hoare[ A.run : (glob A) = (glob A){m} 
           ==> (glob A) = (glob A){m} ] => 
  Pr[ W(A).whp(pa,ia,1,ea,r) @ &m : pa res /\ q res ]  
     = big predT
        (fun i => (Pr[ A.run(ia) @ &m : !pa res ] ^ i) 
          * Pr[ A.run(ia) @ &m : pa res /\ q res ])
        (range 0 ea). 
case (1 <= ea).
progress. rewrite (whp_cap_fin_sum'' &m);auto.
progress.
have ->: bigi predT
  (fun (i : int) =>
     Pr[A.run(ia) @ &m : ! pa res] ^ i * Pr[A.run(ia) @ &m : pa res /\ q res])
  0 ea = 0%r.
smt.
byphoare (_: arg = (pa, ia, 1, ea, r) ==> _).
hoare.
conseq (_: _ ==> ! pa res). smt.
proc. sp.
rcondf 1. skip. smt. skip. smt. auto. auto.
qed.



end section.
  
