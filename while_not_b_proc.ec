pragma Goals:printall.
require import AllCore DBool.
require import Int.

type rt, iat.

module type Run = {
  proc run(i:iat) : rt
}.

module M(A : Run) = {
  var c : int
  proc whp(i : iat, MyP : rt -> bool, s : int, e : int, r : rt) = {
    c <- s;
    while(c <= e /\ !MyP r){
     r <@ A.run(i);
     c <- c + 1;
    }
    return r;
  }

  proc whp_if_end(i : iat, MyP : rt -> bool,s : int, e : int, r : rt) = {
    var ri : rt;
    ri <- whp(i,MyP, s,e,r);     
    if(c <= e + 1 /\ !MyP ri){
      ri <@ A.run(i);
      c <- c + 1;
    }
    return ri;
  }
}.

section.
declare module A : Run{M}.

axiom A_run_ll : islossless A.run.

lemma whp_split_if_end :  
  equiv[ M(A).whp ~ M(A).whp_if_end : ={glob A, i, MyP, s,r} /\ e{1} - 1 = e{2}
        ==> ={res,M.c} ].
proof. proc.
inline*. sp. 
splitwhile{1} 1 : M.c  <= (e - 1) .
seq  1 1 : (={M.c, glob A} /\ r{1} = r0{2} /\ e0{2} = e{2} /\ i{1} = i0{2} /\ i{2} = i0{2}
   /\ MyP0{2} = MyP{1} /\ MyP0{2} = MyP{2} 
   /\ e{1} - 1 = e0{2} /\ (!MyP{1} r{1} => (e{1} - 1) < M.c{1} )).
while (={M.c,MyP, glob A} /\ r{1} = r0{2} /\ e0{2} = e{2} /\ i{1} = i0{2} /\ i{2} = i0{2}
   /\ MyP{1} = MyP0{2} /\ MyP{2} = MyP0{2}
   /\ e{1} - 1 = e0{2} ).
wp. call (_:true).   skip. progress. smt.  skip. progress. smt. smt.
sp. simplify.
case (MyP{1} r{1}).
rcondf {1} 1. progress. skip. smt.
rcondf {2} 1. progress. skip. progress. smt.
skip. progress.
unroll {1} 1.
if. progress.  
rcondf {1} 3. progress.
wp. call (_:true). skip. progress. smt.
wp. call (_:true). skip. progress. 
rcondf {1} 1. progress. skip. progress.
qed.



lemma whp_split_if_end' MyP  i s e r p P :  
  (phoare [ M(A).whp_if_end : arg = (i,MyP,s,e,r) ==> P res ] = p)
   => phoare [ M(A).whp : arg = (i, MyP,s,e+1,r) ==> P res ] = p.
proof. progress. bypr.
progress.
have <-: Pr[M(A).whp_if_end(i{m}, MyP{m}, s{m}, e{m}, r{m}) @ &m : P res] = p.
byphoare (_: arg = (i{m}, MyP{m}, s{m}, e{m}, r{m}) ==> _).
conseq H. auto. auto. byequiv.
conseq whp_split_if_end. smt. auto. auto. auto.
qed.


lemma lll (b a c : real) : a <= b => b <= c => a <= c.
smt. qed.

    
lemma whp_split_if_end_le MyP i s e r p P :  
  (phoare [ M(A).whp_if_end : arg = (i,MyP,s,e,r) ==> P res ] <= p)
   => phoare [ M(A).whp : arg = (i,MyP,s,e+1,r) ==> P res ] <= p.
proof. progress. bypr.
progress.
have zz : Pr[M(A).whp_if_end(i{m},MyP{m}, s{m}, e{m}, r{m}) @ &m : P res] <= p.
byphoare (_: arg = (i{m},MyP{m},s{m}, e{m}, r{m}) ==> _).
conseq H. auto. auto. 
apply (lll Pr[M(A).whp_if_end(i, MyP,s, e, r) @ &m : P res] ).
byequiv.
 conseq whp_split_if_end. smt. auto. auto. auto. apply zz.
qed.



lemma asdsad (p : real) ia r MyPa: 
   (phoare[ A.run : arg = ia ==> !MyPa res ] = p) =>
  MyPa r = false => forall e, 0 <= e => 
  phoare[ M(A).whp_if_end : arg = (ia, MyPa, 1,e,r) ==> !MyPa res ] = (p ^ (e+1)).
proof. move => iipr ipr. apply ge0ind. smt.
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt.
sp. 
rcondt 1. skip. progress. smt.
swap 1 1.  
have f : phoare[ A.run : arg = ia ==> ! MyPa res] = (p^1). admit.
call f. sp. skip. auto.
  simplify.
progress. proc.
  have phf: phoare[ M(A).whp : arg = (ia, MyPa, 1, n+1, r) ==> !MyPa res] = (p ^(n+1)).
 apply (whp_split_if_end'  MyPa ia 1 n r  (p^(n+1)) (fun x => !MyPa x) (H0 H) ).
seq 1 : (!MyPa ri) (p ^(n+1)) p 1%r 0%r (i =  ia /\ MyP = MyPa /\ (!MyPa ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (i =  ia /\ MyP = MyPa /\ (!MyPa r0 => M.c <= e + 1)).
 while (i = ia /\ i = i0 /\ MyP = MyP0 /\ MyP = MyPa /\ e = e0 /\ (!MyPa r0 => M.c <= e0 + 1)).
wp. 
call (_:true).  skip. progress. smt. skip. progress. smt. sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt.  
wp. simplify.  call iipr.  simplify.
skip. progress. 
hoare. 
rcondf 1. skip.  progress.  smt.
simplify. skip. auto. smt.
qed.

lemma asdsad_le (p : real) ia r MyPa: 
   (phoare[ A.run : arg = ia ==> !MyPa res ] <= p) =>
  MyPa r = false => forall e, 0 <= e => 
  phoare[ M(A).whp_if_end : arg = (ia, MyPa, 1,e,r) ==> !MyPa res ] <= (p ^ (e+1)).
proof. move => iipr ipr. apply ge0ind. smt.
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt.
sp. 
rcondt 1. skip. progress. smt.
swap 1 1.  
have f : phoare[ A.run : arg = ia ==> ! MyPa res] <= (p^1). admit.
call f. sp. skip. auto.
  simplify.
progress. proc.
  have phf: phoare[ M(A).whp : arg = (ia, MyPa, 1, n+1, r) ==> !MyPa res] <= (p ^(n+1)).
 apply (whp_split_if_end_le MyPa  ia 1 n r (p^(n+1))  (fun x => !MyPa x) (H0 H)  ).
seq 1 : (!MyPa ri) (p ^(n+1)) p 1%r 0%r (i = ia /\ MyP = MyPa /\ (!MyPa ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (i = ia /\ MyP = MyPa /\ (!MyPa r0 => M.c <= e + 1)).
 while (i = ia /\ i = i0 /\ MyP = MyP0 /\ MyP = MyPa /\ e = e0 /\ (!MyPa r0 => M.c <= e0 + 1)).
wp. 
call (_:true).  skip. progress. smt. skip. progress. smt. sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt.  
wp. simplify.  call iipr.  simplify.
skip. progress. 
hoare. 
rcondf 1. skip.  progress.  smt.
simplify. skip. auto. smt.
qed.



lemma asdsadq (p : real) ia MyP r :  
   (phoare[ A.run : arg = ia ==> !MyP res ] = p) =>
  MyP r = false => forall e, 0 <= e =>
  phoare[ M(A).whp : arg = (ia,MyP,1,e+1,r) ==> !MyP res ] = (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M(A).whp_if_end : arg = (ia,MyP,1,e,r) ==> !MyP res ] = (p ^ (e+1)).
apply (asdsad  p ia r  MyP H1 H e ep). auto.
conseq (whp_split_if_end' MyP ia 1 e r (p^(e+1)) (fun x => !MyP x) fact1).
qed.



lemma asdsadq_le (p : real) ia MyP r:  
   (phoare[ A.run : arg = ia ==> !MyP res ] <= p) =>
  MyP r = false => forall e, 0 <= e =>
  phoare[ M(A).whp : arg = (ia, MyP,1,e+1,r) ==> !MyP res ] <= (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M(A).whp_if_end : arg = (ia,MyP,1,e,r) ==> !MyP res ] <= (p ^ (e+1)).
apply (asdsad_le   p  ia r MyP H1 H e ep). auto.
conseq (whp_split_if_end_le MyP ia 1 e r (p^(e+1))  (fun x => !MyP x) fact1).
qed.

end section.
