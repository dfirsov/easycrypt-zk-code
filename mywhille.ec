pragma Goals:printall.
require import Int.

type rrt, irt.


module type Run = {
  proc run(i:irt) : rrt
}.                                  

module W(A : Run) = {
  var c : int
  proc whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    while(c <= e /\ !p r){
     r <- A.run(i);
     c <- c + 1;
    }
    return r;
  }

  proc if_whp(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    if(c <= e /\ !p r){
     r <- A.run(i);
     c <- c + 1;
    }
    r <- whp(p,i,W.c,e,r);
    return r;
  }

  proc whp_if(p : rrt -> bool, i : irt, s : int, e : int, r : rrt) = {
    var ri;
    c <- s;
    ri <- whp(p,i,s,e-1,r);
    if(c <= e /\ !p ri){
     ri <- A.run(i);
     c <- c + 1;
    }
    return ri;
  }

  proc whp_split(p : rrt -> bool, i : irt, s : int, m : int, e : int, r : rrt) = {
    c <- s;
    r <- whp(p,i,s,m,r);
    r <- whp(p,i,W.c,e,r);
    return r;
  }
  
}.



section.

declare module A : Run {W}.

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
  equiv [ W(A).whp ~ W(A).whp_if : s{2} <= e{2} /\ ={glob W, glob A, arg} ==>  ={glob W, glob A, res} ].
proc.
inline*. sp. 
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





local lemma whp_premat_1 q &m pa ia sa ea ra ja : sa <= ja => ja <= ea =>
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


lemma whp_cap q &m p i s ea r ja :  s <= ja => ja <= ea =>
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

(* 
W.c = N := make exactly N iterations

*)
require import Real.
lemma whp_cap_fin &m pa q ia (s ea : int) r ja (p1 : real) (p2 : int -> real) :
  s <= ja - 1 => ja  <= ea =>
  pa r = false => 0 <= ea =>
  (phoare[ A.run : arg = ia ==> pa res /\  q res ] = p1) =>
  (forall ea, phoare[ W(A).whp : e = ea ==>  !pa res ] = (p2 ea)) =>
   Pr[ W(A).whp(pa,ia,s,ea,r) @ &m : W.c = ja /\ pa res /\ q res ] 
    = p2 (ja - 2) * p1. 
progress.
rewrite  (whp_cap q &m pa ia s ea r ja ). smt. smt.

have ->: Pr[W(A).whp(pa, ia, s, ja-1, r) @ &m : W.c = ja /\ pa res /\ q res]
 = Pr[W(A).whp_if(pa, ia, s, ja -1, r) @ &m : W.c = ja /\ pa res /\ q res].
byequiv. conseq whp_if_prop. progress. admit. admit.
progress. auto. auto.
    
byphoare (_: arg = (pa, ia, s, ja - 1, r) ==> _).
proc. sp.

seq 1 : (! p ri) (p2 (ja - 2))  p1 1%r 0%r (e = ja - 1 /\ W.c <= e  /\ i = ia /\ p = pa 
 /\ (!p ri => W.c = e) ).
inline*. sp.
wp.
while (W.c <= e0 + 1 ). wp. 
call (_:true ==> true). auto. skip. progress. smt. skip. progress.   smt.

 
call (H4 (ja - 2)). skip. progress.  
rcondt 1. skip. progress. 
wp. call H3. skip. progress. 
smt.
hoare.
simplify.
if. wp. call (_:true ==> true). auto.
skip. smt.
skip. smt.  auto. auto. auto.
qed.
 end section.
  
