pragma Goals:printall.
require import AllCore DBool.
require import Int.

type rt.

op MyP : rt -> bool.



module M = {
  var c : int
  proc whp(myd : rt distr, s : int, e : int, r : rt) = {
    c <- s;
    while(c <= e /\ !MyP r){
     r <$ myd;
     c <- c + 1;
    }
    return r;
  }

  proc whp_if_end(myd : rt distr, s : int, e : int, r : rt) = {
    var ri : rt;
    ri <- whp(myd, s,e,r);     
    if(c <= e + 1 /\ !MyP ri){
      ri <$ myd;
      c <- c + 1;
    }
    return ri;
  }
}.


lemma whp_split_if_end :  
  equiv[ M.whp ~ M.whp_if_end : ={myd, s,r} /\ e{1} - 1 = e{2}
        ==> ={res,M.c} ].
proof. proc.
inline*. sp. 
splitwhile{1} 1 : M.c  <= (e - 1) .
seq  1 1 : (={M.c} /\ r{1} = r0{2} /\ myd{1} = myd0{2} /\ e0{2} = e{2} /\ myd0{2} = myd{2}
   /\ e{1} - 1 = e0{2} /\ (!MyP r{1} => (e{1} - 1) < M.c{1} )).
while (={M.c,myd} /\ r{1} = r0{2} /\ myd{1} = myd0{2} /\ e0{2} = e{2}
   /\ e{1} - 1 = e0{2} ).
wp. rnd. skip. progress. smt.  skip. progress. smt. smt.
sp. simplify.
case (MyP r{1}).
rcondf {1} 1. progress. skip. smt.
rcondf {2} 1. progress. skip. smt.
skip. progress.
unroll {1} 1.
if. progress.  
rcondf {1} 3. progress.
wp. rnd. skip. progress. smt.
wp. rnd. skip. progress. 
rcondf {1} 1. progress. skip. progress.
qed.


lemma whp_split_if_end' s e r p P d :  
  (phoare [ M.whp_if_end : arg = (d,s,e,r) ==> P res ] = p)
   => phoare [ M.whp : arg = (d,s,e+1,r) ==> P res ] = p.
proof. progress. bypr.
progress.
have <-: Pr[M.whp_if_end(d{m}, s{m}, e{m}, r{m}) @ &m : P res] = p.
byphoare (_: arg = (d{m}, s{m}, e{m}, r{m}) ==> _).
conseq H. auto. auto. byequiv.
conseq whp_split_if_end. smt. auto. auto. auto.
qed.


lemma lll (b a c : real) : a <= b => b <= c => a <= c.
smt. qed.

    
lemma whp_split_if_end_le s e r p myd P :  
  (phoare [ M.whp_if_end : arg = (myd,s,e,r) ==> P res ] <= p)
   => phoare [ M.whp : arg = (myd,s,e+1,r) ==> P res ] <= p.
proof. progress. bypr.
progress.
have zz : Pr[M.whp_if_end(myd{m},s{m}, e{m}, r{m}) @ &m : P res] <= p.
byphoare (_: arg = (myd{m},s{m}, e{m}, r{m}) ==> _).
conseq H. auto. auto. 
apply (lll Pr[M.whp_if_end(myd,s, e, r) @ &m : P res] ).
byequiv.
 conseq whp_split_if_end. smt. auto. auto. auto. apply zz.
qed.



lemma asdsad r myd:  MyP r = false => forall e, 0 <= e => 
  phoare[ M.whp_if_end : arg = (myd, 1,e,r) ==> !MyP res ] = ((1%r/2%r) ^ (e+1)).
proof. move => ipr. apply ge0ind. smt.
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt.
sp. 
rcondt 1. skip. progress. smt.
swap 1 1.  rnd.  simplify.
wp.  skip.  progress. admit.
progress. proc.
  have phf: phoare[ M.whp : arg = (myd, 1, n+1, r) ==> !MyP res] = (inv 2%r ^(n+1)).
 apply (whp_split_if_end'  1 n r  ((inv 2%r)^(n+1)) (fun x => !MyP x) myd (H0 H) ).
seq 1 : (!MyP ri) (inv 2%r ^(n+1)) (1%r/2%r) 1%r 0%r (!MyP ri => M.c <= e + 1).
inline*. sp.
seq 1 :  (!MyP r0 => M.c <= e + 1).
 while (e = e0 /\ (!MyP r0 => M.c <= e0 + 1)).
wp. 
rnd.  skip. progress. smt. skip. progress. smt. sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt.
wp. simplify.  rnd.  simplify.
skip. progress.
admit.
hoare. 
rcondf 1. skip.  progress.  smt.
simplify. skip. auto. smt.
qed.


lemma asdsad_le r d:  MyP r = false => forall e, 0 <= e => 
  phoare[ M.whp_if_end : arg = (d,1,e,r) ==> !MyP res ]
     <= ((1%r/2%r) ^ (e+1)).
proof. move => ipr. apply ge0ind. smt.
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt.
sp. 
rcondt 1. skip. progress. smt.
swap 1 1.  rnd.  simplify.
wp.  skip.  progress. admit.
progress. proc.
  have phf: phoare[ M.whp : arg = (d,1, n+1, r) ==> !MyP res] <= (inv 2%r ^(n+1)).
 apply (whp_split_if_end_le 1 n r ((inv 2%r)^(n+1)) d (fun x => !MyP x) (H0 H) ).
seq 1 : (!MyP ri) (inv 2%r ^(n+1)) (1%r/2%r) 1%r 0%r (!MyP ri => M.c <= e + 1).
inline*. sp.
seq 1 :  (!MyP r0 => M.c <= e + 1).
 while (e = e0 /\ (!MyP r0 => M.c <= e0 + 1)).
wp. 
rnd.  skip. progress. smt. skip. progress. smt. sp.  skip. progress. 
 call phf. skip.  auto.
rcondt 1. skip. progress. smt.
wp. simplify.  rnd.  simplify.
skip. progress.
admit.
hoare. 
rcondf 1. skip.  progress.  smt.
simplify. skip. auto. smt.
qed.


lemma asdsadq r d:  MyP r = false => forall e, 0 <= e =>
  phoare[ M.whp : arg = (d,1,e+1,r) ==> !MyP res ] = ((1%r/2%r) ^ (e+1)).
progress.
have fact1  : phoare[ M.whp_if_end : arg = (d,1,e,r) ==> !MyP res ] = ((1%r/2%r) ^ (e+1)).
apply (asdsad r d H e H0). auto.
conseq (whp_split_if_end' 1 e r ((inv 2%r)^(e+1)) (fun x => !MyP x) d fact1).
qed.
