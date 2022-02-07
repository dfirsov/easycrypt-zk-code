pragma Goals:printall.

require import AllCore DBool.

require import Int.
op myd : int distr.

module M = {
  var c : int
  proc whp(s : int, e : int, b : bool, r : int) = {
    c <- s;
    while(c <= e /\ !b ){
     r <$ myd;
     b <$ {0,1};
     c <- c + 1;
    }
    return (r,b);
  }

  proc whp_if_end(s : int, e : int, b : bool, r : int) = {
    (r,b) <- whp(s,e,b,r);     
    if(c <= e + 1 /\ !b){
      r <$ myd;
      b <$ {0,1};
      c <- c + 1;
    }
    return (r,b);
  }
}.


lemma whp_split_if_end :  
  equiv[ M.whp ~ M.whp_if_end : ={s,b,r} /\ e{1} - 1 = e{2}
        ==> ={res,M.c} ].
proof. proc.
inline*. sp. 
splitwhile{1} 1 : M.c  <= (e - 1) .
seq  1 1 : (={M.c} /\ b{1} = b0{2} /\ r{1} = r0{2} /\ e0{2} = e{2}
   /\ e{1} - 1 = e0{2} /\ (!b{1} => (e{1} - 1) < M.c{1} )).
while (={M.c} /\ b{1} = b0{2} /\ r{1} = r0{2} /\ e0{2} = e{2}
   /\ e{1} - 1 = e0{2} ).
wp. rnd. rnd. skip. progress. smt.  skip. progress. smt. smt.
sp. simplify.
case (b{1}).
rcondf {1} 1. progress. skip. smt.
rcondf {2} 1. progress. skip. smt.
skip. progress.
unroll {1} 1.
if. progress.  
rcondf {1} 4. progress.
wp. rnd. rnd. skip. progress. smt.
wp. rnd. rnd. skip. progress. 
rcondf {1} 1. progress. skip. progress.
qed.


lemma whp_split_if_end' s e b r p P :  
  (phoare [ M.whp_if_end : arg = (s,e,b,r) ==> P res ] = p)
   => phoare [ M.whp : arg = (s,e+1,b,r) ==> P res ] = p.
proof. progress. bypr.
progress.
have <-: Pr[M.whp_if_end(s{m}, e{m}, b{m}, r{m}) @ &m : P res] = p.
byphoare (_: arg = (s{m}, e{m}, b{m}, r{m}) ==> _).
conseq H. auto. auto. byequiv.
conseq whp_split_if_end. smt. auto. auto. auto.
qed.

lemma lll (b a c : real) : a <= b => b <= c => a <= c.
smt. qed.

    
lemma whp_split_if_end_le s e b r p P :  
  (phoare [ M.whp_if_end : arg = (s,e,b,r) ==> P res ] <= p)
   => phoare [ M.whp : arg = (s,e+1,b,r) ==> P res ] <= p.
proof. progress. bypr.
progress.
have zz : Pr[M.whp_if_end(s{m}, e{m}, b{m}, r{m}) @ &m : P res] <= p.
byphoare (_: arg = (s{m}, e{m}, b{m}, r{m}) ==> _).
conseq H. auto. auto. 
apply (lll Pr[M.whp_if_end(s, e, b, r) @ &m : P res] ).
byequiv.
 conseq whp_split_if_end. smt. auto. auto. auto. apply zz.
qed.



lemma asdsad r:  forall e, 0 <= e =>
  phoare[ M.whp_if_end : arg = (1,e,false,r) ==> !res.`2 ] = ((1%r/2%r) ^ (e+1)).
proof. apply ge0ind. smt.
progress. simplify.
  progress. proc.
inline*. sp.
rcondf 1. skip. smt.
sp. 
rcondt 1. skip. progress. wp.
conseq (_: true ==> !b). 
swap 1 1.  rnd. 
conseq (_: true ==> !b). admit.
rnd. skip. smt.
progress. proc.
  have phf: phoare[ M.whp : arg = (1, n+1, false, r) ==> ! res.`2] = (inv 2%r ^(n+1)).
 apply (whp_split_if_end' 1 n false r ((inv 2%r)^(n+1)) (fun (x : int * bool) => !x.`2) (H0 H) ).
seq 1 : (!b) (inv 2%r ^(n+1)) (1%r/2%r) 1%r 0%r (!b => M.c <= e + 1).
inline*. sp.  wp. while (e = e0 /\ (!b0 => M.c <= e + 1)).
wp. rnd. rnd. skip. progress. smt. skip. progress. smt.
call phf. skip.  auto.
rcondt 1. skip. progress. smt.
wp. simplify.  swap 1 1.  rnd. 
conseq (_: _ ==> !b). progress. admit.
rnd. skip. progress.
smt.
hoare. 
rcondf 1. skip.  progress.  smt.
simplify. skip. auto. smt.
qed.


lemma asdsadq r:  forall e, 0 <= e =>
  phoare[ M.whp : arg = (1,e+1,false,r) ==> !res.`2 ] = ((1%r/2%r) ^ (e+1)).
progress.
have fact1  : phoare[ M.whp_if_end : arg = (1,e,false,r) ==> !res.`2 ] = ((1%r/2%r) ^ (e+1)). apply asdsad. auto.
 apply (whp_split_if_end' 1 (e) false r ((inv 2%r)^(e+1)) (fun (x : int * bool) => !x.`2)  fact1 ).
qed.
