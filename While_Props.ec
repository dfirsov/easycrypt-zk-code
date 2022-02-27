pragma Goals:printall.
require import Int.

type rrt, irt.


module type Run = {
  proc main(i:irt) : rrt
}.                                  

module WW(A : Run) = {
  var c : int
  proc whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    while(c <= e /\ !p r){
     r <- A.main(i);
     c <- c + 1;
    }
    return r;
  }

  proc if_whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    if(c <= e /\ !p r){
     r <- A.main(i);
     c <- c + 1;
    }
    r <- whp(p,i,WW.c,e,r);
    return r;
  }

  proc whp_if(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    var ri;
    c <- s;
    ri <- whp(p,i,s,e-1,r);
    if(c <= e /\ !p ri){
     ri <- A.main(i);
     c <- c + 1;
    }
    return ri;
  }

  proc whp_split(p : rrt -> bool, i : irt, s : int, m : int, e : int, r : rrt) = {
    c <- s;
    r <- whp(p,i,s,m,r);
    r <- whp(p,i,WW.c,e,r);
    return r;
  }
  
}.



require Pr_interval_to_sum.
clone import Pr_interval_to_sum as PIT with type rt <- rrt,
                                            type iat <- (rrt -> bool) * irt * int * int * rrt .

section.

declare module A : Run {WW}.

axiom A_ll : islossless A.main.

lemma if_whp_prop : 
  equiv [ WW(A).whp ~ WW(A).if_whp : ={glob WW, glob A, arg} ==>  ={glob WW, glob A, res} ].
proc. inline*.
unroll {1} 2.
sp.
if. progress.
seq 2 8 : (={glob A, glob WW} /\ e{1} = e0{2} /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} 
  /\ e{2} = e0{2} /\ p{2} = p0{2} /\ r{2} = r0{2} /\ i{2} = i0{2} ).
wp.  call (_:true). skip. progress.
wp.
 while (={glob A, glob WW} /\ e{1} = e0{2} /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} ).
wp.
call (_: true). skip. progress.
skip. progress.
sp.
rcondf {1} 1. progress.
rcondf {2} 1. progress. wp. skip. progress. 
qed.


lemma whp_if_prop : 
  equiv [ WW(A).whp ~ WW(A).whp_if : ={glob WW, glob A, arg} ==>  ={glob WW, glob A, res} ].
proc.
inline*. sp. 
case (s{2} <= e{2}).
splitwhile {1} 1 : (WW.c <= e-1).
seq 1 1 : (={WW.c, glob A,e,p,i} /\ e{1} = e0{2} + 1  /\ p{1} = p0{2} /\ r{1} = r0{2} /\ i{1} = i0{2} /\ (! p r => WW.c = e){1}).
while (={WW.c, glob A,e,p,i} /\ e{1} = e0{2} + 1 /\ p{1} = p0{2}  /\ r{1} = r0{2} /\ i{1} = i0{2} /\ (! p r => WW.c <= e){1}).
wp. call (_:true). skip. progress.
smt. smt.
skip. progress. smt.
sp.
unroll {1} 1.
seq 1 1 : (={glob A, WW.c,e,p,i} /\ ri{2} = r{1} /\ (! p{1} r{1} => WW.c{1} = e{1}+1)). 
if. progress. wp. call (_:true). skip. progress. smt. skip. progress. smt.
rcondf {1} 1. progress. skip. progress. smt. skip. progress.
rcondf {1} 1. progress. skip. progress. smt.
rcondf {2} 1. progress. skip. progress. smt.
sp. 
rcondf {2} 1. progress. skip. progress. smt.
skip. progress.
qed.




lemma whp_split_prop : 
  equiv [ WW(A).whp ~ WW(A).whp_split : m{2} <= e{2}  /\ ={glob WW, glob A, p, i, s, e, r}
        ==>  ={glob WW, glob A, res} ].
proc.  inline*.
exists* m{2}. elim*. progress.
splitwhile {1} 2 : (WW.c <= m_R).      
sp.
seq 1 1 : (={glob A, WW.c,p,i,e} /\ m_R = m{2} /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r0{2} /\ p{1} = p0{2} /\ i{1} = i0{2}).
while (={glob A, WW.c,p,i,e} /\ m_R = m{2}  /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r0{2} /\ p{1} = p0{2} /\ i{1} = i0{2}).
wp. call (_:true). skip. progress. smt. 
skip. progress. smt.
sp. 
wp.
while (={glob A, WW.c,p,i,e} /\ m_R = m{2}  /\ e{2} = e1{2} /\ m{2} <= e{2} /\ e0{2} = m_R /\ r{1} = r1{2} /\ p{1} = p1{2} /\ i{1} = i1{2}).
wp. call (_:true). skip. progress. 
skip. progress.
qed.





local lemma whp_premat_1 q &m pa ia sa ea ra ja : sa <= ja => ja <= ea + 1 =>
  Pr[ WW(A).whp(pa,ia,sa,ja-1,ra) @ &m : WW.c = ja /\ pa res /\ q res ]
   =   Pr[ WW(A).whp_split(pa,ia,sa,ja-1,ea,ra) @ &m : WW.c = ja /\ pa res /\ q res ].
proof. move => hp ph.
byequiv.
proc*. 
inline WW(A).whp_split. sp. 
seq 1 1 : (={glob A, glob WW} /\ p{1} = pa /\ p0{2} = pa /\ r0{1} = r1{2} /\ p{1} = p0{2} /\ e{1} = ja-1 /\ i{1} = i0{2} /\ s{1} = s0{2} /\ (!p r0 => WW.c = e + 1){1} /\ e0{2} = ea).
inline*.  sp. wp.
while (={glob A, glob WW} /\ (e0,p0,r1,i0){1} = (e1,p1,r2,i1){2} /\ (!p0 r1 => WW.c <= e0 + 1){1}). wp. call (_:true). skip. progress.
smt. skip. progress. smt.

inline*.  sp. 
case (pa r0{1}).
rcondf {2} 1. progress.  skip. progress. smt.
wp. skip. progress. wp. 
conseq (_:  (p1{2} = pa /\ r2{2} = r0{1}) /\ ja  -1 <= e0{2}  /\  (! pa r0{1}) /\ WW.c{1} = ja  /\ WW.c{2} = WW.c{1} /\ e1{2} = e0{2} /\ e1{2} = ea  ==> _ ). progress. smt.  smt.
case ((WW.c <= e1 /\ ! p1 r2){2}).
unroll {2} 1. rcondt{2} 1. progress.
seq 0 2 : (ja < WW.c{2} /\ ! pa r0{1}).
wp. call {2} (_: true ==> true). apply A_ll.
skip. progress. smt.
while {2} (ja < WW.c{2} /\ ! pa r0{1}) (e1{2} + 1 - WW.c{2}).
progress. wp. call (_: true ==> true). apply A_ll. skip. progress. smt. smt.
skip. progress;smt.
rcondf {2} 1. progress. skip. smt. auto. auto.
qed.


lemma whp_cap q &m p i s ea r ja :  s <= ja => ja <= ea + 1 =>
   Pr[ WW(A).whp(p,i,s,ea,r) @ &m : WW.c = ja /\ p res /\ q res ] 
   =   Pr[ WW(A).whp(p,i,s,ja-1,r) @ &m : WW.c = ja /\ p res /\ q res ].
move => sjp jap.
have ->:  Pr[ WW(A).whp(p,i,s,ja-1,r) @ &m : WW.c = ja /\ p res /\ q res ] 
  =  Pr[ WW(A).whp_split(p,i,s,ja-1,ea,r) @ &m : WW.c = ja /\ p res  /\ q res] .
rewrite - whp_premat_1. auto. 
auto. auto.
byequiv (_: ={p,i,s,e,r, glob A, glob WW} /\ e{2} = ea
    /\ m{2} = ja -1 /\ m{2} <= e{2} ==> _) .
conseq whp_split_prop.
progress.
progress.
progress.
smt. auto.
qed.


require import Real.

lemma whp_cap_fin &m pa q ia (ea : int) r ja (p1 : real) (p2 : int -> real) :
  2  <= ja     =>
  ja <= ea + 1 =>
  pa r = false =>

  (* prob. of success *)
  (phoare[ A.main : arg = ia /\ (glob A) = (glob A){m}  ==> pa res /\  q res ] = p1) =>

  (* prob. of failure  *)
  (forall ea, 0 <= ea => phoare[ WW(A).whp : arg = (pa,ia, 1,ea,r) /\ (glob A) = (glob A){m}
                               ==> !pa res ] = (p2 ea)) =>
  (* module is rewinded or stateless  *)
  (hoare[ A.main :  (glob A) = (glob A){m}  ==> (glob A) = (glob A){m} ]) => 
   Pr[ WW(A).whp(pa,ia,1,ea,r) @ &m : WW.c = ja /\ pa res /\ q res ]  
     = p2 (ja - 2) * p1. 
proof.
progress.
rewrite  (whp_cap q &m pa ia 1 ea r ja ). smt. smt.
have ->: Pr[WW(A).whp(pa, ia, 1, ja-1, r) @ &m : WW.c = ja /\ pa res /\ q res]
 = Pr[WW(A).whp_if(pa, ia, 1, ja-1, r) @ &m : WW.c = ja /\ pa res /\ q res].
byequiv. conseq whp_if_prop. progress. admit.
progress. auto. auto.
 byphoare (_: arg = (pa, ia, 1, ja - 1, r) /\ (glob A) = (glob A){m} ==> _).
proc. sp.
seq 1 : (! p ri) (p2 (ja - 2))  p1 1%r 0%r (e = ja - 1 /\ WW.c <= e  /\ i = ia /\ p = pa 
 /\ (!p ri => WW.c = e)  /\  (glob A) = (glob A){m} ).
inline*. sp.
wp.
while (WW.c <= e0 + 1 /\  (glob A) = (glob A){m} ). wp. 
call H4.   skip. progress. smt. skip. progress.   smt. smt.  
  call (H3 (ja - 2)  ).  smt. skip. progress.  
rcondt 1. skip. progress. 
wp. call H2. skip. progress. 
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
    r <@ WW(A).whp(a);
    return r;
  }

}.


lemma whp_cap_fin_int_sum &m ia pa M (ea : int) ra :
   Pr[ WW(A).whp(pa,ia,1,ea,ra) @ &m : 1 < WW.c <= ea + 1  /\ M res ] = 
    big predT
      (fun i => Pr[ WW(A).whp(pa,ia,1,ea,ra) @ &m : WW.c = i /\ M res ])
      (range 2 (ea + 2)).
progress.
pose f := fun (x : glob CA) => x.`1.
have ->: Pr[ WW(A).whp(pa,ia,1,ea,ra) @ &m : 1 < WW.c <= ea + 1  /\ M res ]
 = Pr[ CA.run(pa,ia,1,ea,ra) @ &m : 2 <= f (glob CA) <= ea + 1  /\ M res ].
byequiv (_: ={arg, glob CA} ==> ={res, glob CA}). proc.
inline*. sp.  wp. 
conseq (_: ={glob CA} /\ ={e, p, i} /\ r{1} = r0{2} ==> ={glob CA} /\ r{1} = r0{2}). smt. smt.
sim. auto. smt. 
rewrite (pr_interval_to_sum_lemma CA &m (pa, ia, 1, ea, ra) f (fun _ x _ => M x)).
simplify.
have <-: 
 (fun (i : int) => Pr[WW(A).whp(pa, ia, 1, ea, ra) @ &m : WW.c = i /\ M res])
 = (fun (i : int) =>
     Pr[CA.run(pa, ia, 1, ea, ra) @ &m : f (WW.c, (glob A)) = i /\ M res]).
apply fun_ext. move => x.
byequiv (_: ={arg, glob CA} ==> ={res, glob CA}). proc.
inline*.  wp.  sp.
conseq (_: ={glob CA} /\ ={e, p, i} /\ r{1} = r0{2} ==> ={glob CA} /\ r{1} = r0{2}). smt. smt.
sim. auto. smt. 
auto.
qed.

   
lemma whp_cap_fin_int &m pa ia (ea : int) ra :
  pa ra = false => 1 <= ea =>
   Pr[ WW(A).whp(pa,ia,1,ea,ra) @ &m : 1 < WW.c <= ea + 1 ] = 1%r.
progress.
byphoare (_: arg = (pa, ia, 1, ea, ra) ==> _).
proc. sp.
unroll 1.
rcondt 1. skip. smt.
seq 2 : (WW.c = 2 /\ (p, i, s, e) = (pa, ia, 1, ea)).
wp. call (_: true ==> true). auto.
skip. auto.
wp. call (_: true ==> true). apply A_ll.
skip. progress.
while (1 < WW.c && WW.c <= e + 1) (e + 1 - WW.c).
progress. 
wp. call (_: true ==> true). apply A_ll.
skip. progress. smt. smt. smt. skip. progress.
smt.  smt.
hoare. simplify.
wp. call (_: true ==> true). auto. skip. auto. auto. auto.
auto.
qed.


lemma whp_cap_fin_sum &m pa q ia (ea : int) r ja 
  (p1 : real) 
  (p2 : int -> real) :
  2  <= ja     =>
  ja <= ea + 1 =>
  pa r = false =>

  (* prob. of success *)
  (phoare[ A.main : arg = ia /\ (glob A) = (glob A){m}  
           ==> pa res /\ q res ] = p1) =>

  (* prob. of failure  *)
  (forall ea, 0 <= ea => phoare[ WW(A).whp : arg = (pa,ia, 1,ea,r) 
                                 /\ (glob A) = (glob A){m}
                                   ==> !pa res ] = (p2 ea)) =>
  (* module is rewinded or stateless  *)
  (hoare[ A.main :  (glob A) = (glob A){m} 
           ==> (glob A) = (glob A){m} ]) => 
   Pr[ WW(A).whp(pa,ia,1,ea,r) @ &m : pa res /\ q res ]  
     = big predT
        (fun i => p2 (i - 2) * p1)
        (range 2 (ea + 2)). 
proof. progress.
have ->: Pr[ WW(A).whp(pa,ia,1,ea,r) @ &m : pa res /\ q res ]  
 = Pr[ WW(A).whp(pa,ia,1,ea,r) @ &m : (1 < WW.c <= ea + 1) 
        /\ pa res /\ q res ].
rewrite Pr[mu_split (1 < WW.c && WW.c <= ea + 1)].
  have ->: Pr[WW(A).whp(pa, ia, 1, ea, r) @ &m :
   (pa res /\ q res) /\ ! (1 < WW.c && WW.c <= ea + 1)] = 0%r.
   have : Pr[WW(A).whp(pa, ia, 1, ea, r) @ &m : ! (1 < WW.c && WW.c <= ea + 1)] = 0%r.
    have f3 : Pr[WW(A).whp(pa, ia, 1, ea, r) @ &m : (1 < WW.c && WW.c <= ea + 1)] = 1%r. rewrite (whp_cap_fin_int &m);smt.
    have f2 : 1%r = Pr[WW(A).whp(pa, ia, 1, ea, r) @ &m : ! (1 < WW.c && WW.c <= ea + 1)] + Pr[WW(A).whp(pa, ia, 1, ea, r) @ &m : (1 < WW.c && WW.c <= ea + 1)]. 
    have  <- : Pr[WW(A).whp(pa, ia, 1, ea, r) @ &m : true ] = 1%r.
    smt.
   rewrite Pr[mu_split (1 < WW.c && WW.c <= ea + 1)]. simplify.
   smt. smt. smt. simplify. smt.  
rewrite big_int_cond.
rewrite (whp_cap_fin_int_sum &m ia pa (fun x => pa x /\ q x) ea r).
simplify.
rewrite big_int_cond.
apply eq_big. auto.
progress.
apply (whp_cap_fin &m).  auto. smt.
auto.
auto.
auto.
auto.
qed.


end section.
  
