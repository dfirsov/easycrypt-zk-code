pragma Goals:printall.
require import AllCore DBool.
require import Int.

type rt.


module M = {
  var c : int
  proc whp(MyP : rt -> bool,myd : rt distr, s : int, e : int, r : rt) = {
    c <- s;
    while(c <= e /\ !MyP r){
     r <$ myd;
     c <- c + 1;
    }
    return r;
  }

  proc whp_if_end(MyP : rt -> bool,myd : rt distr, s : int, e : int, r : rt) = {
    var ri : rt;
    ri <@ whp(MyP,myd, s,e,r);     
    if(c <= e + 1 /\ !MyP ri){
      ri <$ myd;
      c <- c + 1;
    }
    return ri;
  }
}.


lemma whp_split_if_end :  
  equiv[ M.whp ~ M.whp_if_end : ={MyP,myd, s,r} /\ e{1} - 1 = e{2}
        ==> ={res,M.c} ].
proof. proc.
inline*. sp. 
splitwhile{1} 1 : M.c  <= (e - 1) .
seq  1 1 : (={M.c} /\ r{1} = r0{2} /\ myd{1} = myd0{2} /\ e0{2} = e{2} /\ myd0{2} = myd{2}
   /\ MyP0{2} = MyP{1} /\ MyP0{2} = MyP{2} 
   /\ e{1} - 1 = e0{2} /\ (!MyP{1} r{1} => (e{1} - 1) < M.c{1} )).
while (={M.c,myd,MyP} /\ r{1} = r0{2} /\ myd{1} = myd0{2} /\ e0{2} = e{2} 
   /\ MyP{1} = MyP0{2} /\ MyP{2} = MyP0{2}
   /\ e{1} - 1 = e0{2} ).
wp. rnd. skip. progress. smt.  skip. progress. smt. smt.
sp. simplify.
case (MyP{1} r{1}).
rcondf {1} 1. progress. skip. smt.
rcondf {2} 1. progress. skip. progress. smt.
skip. progress.
unroll {1} 1.
if. progress.  
rcondf {1} 3. progress.
wp. rnd. skip. progress. smt.
wp. rnd. skip. progress. 
rcondf {1} 1. progress. skip. progress.
qed.


lemma whp_split_if_end' MyP s e r p P d :  
  (phoare [ M.whp_if_end : arg = (MyP,d,s,e,r) ==> P res ] = p)
   => phoare [ M.whp : arg = (MyP,d,s,e+1,r) ==> P res ] = p.
proof. progress. bypr.
progress.
have <-: Pr[M.whp_if_end(MyP{m},d{m}, s{m}, e{m}, r{m}) @ &m : P res] = p.
byphoare (_: arg = (MyP{m},d{m}, s{m}, e{m}, r{m}) ==> _).
conseq H. auto. auto. byequiv.
conseq whp_split_if_end. smt. auto. auto. auto.
qed.


lemma lll (b a c : real) : a <= b => b <= c => a <= c.
smt. qed.

    
lemma whp_split_if_end_le MyP s e r p myd P :  
  (phoare [ M.whp_if_end : arg = (MyP,myd,s,e,r) ==> P res ] <= p)
   => phoare [ M.whp : arg = (MyP,myd,s,e+1,r) ==> P res ] <= p.
proof. progress. bypr.
progress.
have zz : Pr[M.whp_if_end(MyP{m}, myd{m},s{m}, e{m}, r{m}) @ &m : P res] <= p.
byphoare (_: arg = (MyP{m},myd{m},s{m}, e{m}, r{m}) ==> _).
conseq H. auto. auto. 
apply (lll Pr[M.whp_if_end(MyP,myd,s, e, r) @ &m : P res] ).
byequiv.
 conseq whp_split_if_end. smt. auto. auto. auto. apply zz.
qed.



lemma asdsad (p : real) r myda MyPa: 
  (mu myda (fun (x : rt) => ! MyPa x) = p) =>
  MyPa r = false => forall e, 0 <= e => 
  phoare[ M.whp_if_end : arg = (MyPa,myda, 1,e,r) ==> !MyPa res ] = (p ^ (e+1)).
proof. move => iipr ipr. apply ge0ind. smt.
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt.
sp. 
rcondt 1. skip. progress. smt.
swap 1 1.  rnd.  simplify.
wp.  skip.  progress. smt.
progress. proc.
  have phf: phoare[ M.whp : arg = (MyPa,myda, 1, n+1, r) ==> !MyPa res] = (p ^(n+1)).
 apply (whp_split_if_end'  MyPa 1 n r  (p^(n+1)) (fun x => !MyPa x) myda (H0 H) ).
seq 1 : (!MyPa ri) (p ^(n+1)) p 1%r 0%r (myd = myda /\ MyP = MyPa /\ (!MyPa ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (MyP = MyPa /\ myd = myda  /\ (!MyPa r0 => M.c <= e + 1)).
 while (MyP = MyP0 /\ MyP = MyPa /\ myd = myda /\ e = e0 /\ (!MyPa r0 => M.c <= e0 + 1)).
wp. 
rnd.  skip. progress. smt. skip. progress. smt. sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt.  
wp. simplify.  rnd.  simplify.
skip. progress. 
hoare. 
rcondf 1. skip.  progress.  smt.
simplify. skip. auto. smt.
qed.


lemma asdsad_le (p : real) MyPa r d:
  (mu d (fun (x : rt) => ! MyPa x) <= p) =>
    MyPa r = false => forall e, 0 <= e => 
  phoare[ M.whp_if_end : arg = (MyPa, d,1,e,r) ==> !MyPa res ]
     <= (p ^ (e+1)).
proof. move => dpr ipr. apply ge0ind. smt.
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt.
sp. 
rcondt 1. skip. progress. smt.
swap 1 1.  rnd.  simplify.
wp.  skip.  progress. smt. 
progress. proc.
  have phf: phoare[ M.whp : arg = (MyPa,d,1, n+1, r) ==> !MyPa res] <= (p ^(n+1)).
 apply (whp_split_if_end_le MyPa 1 n r (p^(n+1)) d (fun x => !MyPa x) (H0 H) ).
seq 1 : (!MyP ri) (p ^(n+1)) p 1%r 0%r (d = myd /\ MyP = MyPa /\ (!MyP ri => M.c <= e + 1)).
inline*. sp.
seq 1 :  (d = myd /\ MyP = MyPa /\ myd = myd0 /\ (!MyP r0 => M.c <= e + 1)).
 while (d = myd /\ myd = myd0 /\ MyP = MyP0 /\ e = e0 /\ (!MyP r0 => M.c <= e0 + 1)).
wp. 
rnd.  skip. progress. smt. skip. progress. smt. sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt. 
wp. simplify.  rnd.  simplify.
skip. progress.
hoare. 
rcondf 1. skip.  progress.  smt.
simplify. skip. auto. smt.
qed.


lemma asdsadq (p : real) MyP r d:  
   (mu d (fun (x : rt) => ! MyP x) = p) =>
  MyP r = false => forall e, 0 <= e =>
  phoare[ M.whp : arg = (MyP,d,1,e+1,r) ==> !MyP res ] = (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M.whp_if_end : arg = (MyP,d,1,e,r) ==> !MyP res ] = (p ^ (e+1)).
apply (asdsad  p r d MyP H1 H e ep). auto.
conseq (whp_split_if_end' MyP 1 e r (p^(e+1)) (fun x => !MyP x) d fact1).
qed.



lemma asdsadq_le (p : real) MyP r d:  
   (mu d (fun (x : rt) => ! MyP x) <= p) =>
   MyP r = false => forall e, 0 <= e =>
    phoare[ M.whp : arg = (MyP,d,1,e+1,r) ==> !MyP res ] <= (p ^ (e+1)).
move => H1 H e ep.
have fact1  : phoare[ M.whp_if_end : arg = (MyP,d,1,e,r) ==> !MyP res ] <= (p ^ (e+1)).
apply (asdsad_le  p MyP r d H1 H e ep). auto.
conseq (whp_split_if_end_le MyP 1 e r (p^(e+1))  d (fun x => !MyP x) fact1).
qed.
