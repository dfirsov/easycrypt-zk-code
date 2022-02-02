pragma Goals:printall.

require import AllCore DBool.

require import Int.
print Int.
op myd : int distr.

module M = {

  proc whp(c : int, n : int, b : bool, r : int) = {
    while(c <= n /\ !b ){
     r <$ myd;
     b <$ {0,1};
     c <- c + 1;
    }
    return (r,b);
  }

  proc main'_split(na : int) = {
    var result,ba,ca;
    result <- witness;
    ba <- false;
    ca <- 1;
    if(ca <= na /\ !ba ){
     result <$ myd;
     ba <$ {0,1};
     ca <- ca + 1;
    }
    (result,ba) <- whp(2,na,ba,result);
    return result;
  }


  
  proc main'(na : int) = {
    var result,br;
    result <- witness;
    br <- false;
    (result,br) <- whp(1,na,false,result);
    return result;
  }
  
  proc main(n : int) = {
    var r,c : int;
    var b : bool;
    r <- witness;
    c <- 1;
    b <- false;
    while(c <= n /\ !b ){
     r <$ myd;
     b <$ {0,1};      
     c <- c + 1;
    }
    return r;
  }  
}.

lemma kk : equiv [M.main ~ M.main' : ={arg} ==> ={res}].
proof. proc. 
inline*.
sp. wp.
while (={c,b,r,n}).
wp. 
rnd. rnd. skip.  progress. skip. progress.
qed.


lemma qq : equiv [M.main' ~ M.main'_split : ={arg} ==> ={res}].
proof. proc.
sp. inline*. sp.
unroll {1} 1.
if. progress.
wp.
seq 3 7 : (={r,c,b,n}).
wp.  rnd. rnd. skip. progress. sim.
sp.
rcondf {1} 1. progress. 
rcondf {2} 1. progress.  skip. progress. smt. wp.  skip. smt.
qed.



lemma zqq o (P : _ -> bool) : 0 <= o
    => equiv [M.whp ~ M.whp : c{1} = c{2} + o /\ n{1} = n{2} + o /\ ={b,r}  ==> (P res{1}) = P res{2}].
proof. move => oass. proc. 
inline*.
sp. wp.
while (c{1} = c{2} + o /\ n{1} = n{2} + o /\ ={b,r}).
wp. rnd. rnd. skip. progress. smt. smt.  smt.
skip. progress. smt. smt.
qed.


lemma zzt &m P : forall np r, 0 < np =>
    Pr[ M.main'_split(np) @ &m : P res ] = Pr[ M.whp(1,np,false,r) @ &m : P res.`1 ].
proof. progress.
byequiv. proc. 
inline*. sp.
unroll {2} 1.
wp.  if. smt. 
while (={c,b,r,n}). wp. rnd. rnd. skip. progress. wp. 
rnd. rnd. skip. progress. sp. 
while (={c,b,r,n}). wp. rnd. rnd. skip.  progress. skip. progress.
smt. auto. auto.
qed.


lemma okk &m ca na ba ra P : 
 phoare[ M.whp : arg = (ca,na,ba,ra) ==> P res] =  Pr[M.whp(ca,na,ba,ra) @ &m : P res].
proof. bypr.
progress.
byequiv (_: ={arg} ==> _).
proc.  while (={c,n,b,r}). wp. rnd. rnd. skip. progress. skip. progress. 
smt.
auto.
qed.

lemma zz &m P : forall np, 0 < np => Pr[ M.main'_split(np) @ &m : P res ] = mu myd P.
proof.  apply ge0ind.
simplify. smt.
simplify. auto.
simplify. move => np. progress.
case (np = 0).
move => np0. rewrite np0. simplify.
byphoare (_: na = 1 ==> _).
  proc. sp.
rcondt 1.
skip.  auto. inline*.
rcondf 8.
wp.  rnd. rnd. skip. progress. 
wp. rnd. rnd. skip. smt.
  auto. auto.
move => p1.
have : 0 < np. smt.
clear p1. clear H1.
move => npe.
have : Pr[M.main'_split(np) @ &m : P res] = mu myd P.
apply H0. auto.
clear H0 H.
move => ih.
byphoare (_: na = np+1 ==> _). 
proc.  sp.
rcondt 1. skip.  smt.
swap 2 -1.
seq 1 : (ca = 1  /\ na = np + 1) (1%r) (mu myd P) (0%r) (1%r).
rnd. skip. smt.
rnd. skip. progress. smt.
case (ba = true).
inline*.
rcondf 7. wp.  rnd. skip. progress. wp.
rnd. skip. smt.
seq 2 : (na = np + 1 /\ ba = false) (1%r) (mu myd P) (0%r) (1%r).
wp. rnd. skip. auto.
wp. rnd. skip. progress.  smt. admit.
rewrite (zzt &m P np witness) in ih.
  auto.
exists* result. elim*. move => r.
have : Pr[M.whp(2, np + 1, false, witness) @ &m : P res.`1] = Pr[M.whp(1, np, false, witness) @ &m : P res.`1]. 
byequiv. proc*.
 call (zqq 1 (fun (x : int * bool) => P x.`1)).
skip. progress. smt. smt.  auto. auto.
have ->: Pr[M.whp(2, np + 1, false, witness) @ &m : P res.`1] =  Pr[M.whp(2, np + 1, false, r) @ &m : P res.`1].
byequiv. proc. unroll {1} 1. unroll {2} 1.
seq 1 1 : (={c,n,b,r}). 
rcondt {1} 1. auto. smt.
rcondt {2} 1. auto. smt.
wp. rnd. rnd. skip. progress.
conseq (_: _ ==> ={c,n,b,r}). auto. sim. auto. auto.
auto.
have : Pr[M.whp(2, np + 1, false, r) @ &m : P res.`1] = mu myd P.
rewrite - ih. apply H. progress.
clear H ih.
have : phoare[ M.whp : arg = (2, np+1, false, r) ==> P res.`1] = (mu myd P).
rewrite -  H0.
apply (okk &m 2 (np + 1) false r (fun (x : int * bool) => P x.`1)). auto.
call H. skip.  progress. 
hoare. wp. rnd. skip. progress. smt. auto.
hoare. simplify.
rnd. skip.  progress. auto. auto. auto.
qed.


lemma kl : Pr[ M.main'_split(np) @ &m : b = false ] <= ?
lemma kl : Pr[ M.main'_split(np) @ &m : b = false /\ P res ] <= ?
          

lemma kl : Pr[ M.main'_split(np) @ &m : P res /\ b = false ]
 = (int 2%r) ^ n * Pr[ M.main'_split(np) @ &m : P res ]
