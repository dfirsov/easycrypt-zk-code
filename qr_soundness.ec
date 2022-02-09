pragma Goals:printall.
require import AllCore Distr.


type sbits, iat, rrt, irt.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.

require RewBasics.
clone import RewBasics as RW with type sbits <- sbits,
                                  type iat   <- iat,
                                  type iat2  <- irt,
                                  type rrt   <- rrt,
                                  type irt   <- irt,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.

                                  


require Reflection.
clone import Reflection.Refl as Re with
                                  type at  <- irt,
                                  type rt  <- rrt.

                                  
                                  
section.


op MyP : rrt -> bool.  


module W(A : RewRun) = {
  module GRS = GetRunSet(A)
  module PA = PP(GRS)
  var c : int
  proc whp_A(i : irt, s : int, e : int, r : rrt) = {
    c <- s;
    while(c <= e /\ !MyP r){
     r <- GRS.main(i);
     c <- c + 1;
    }
    return r;
  }

  proc whp_d(d : rrt distr, s : int, e : int, r : rrt) = { 
    c <- s;
    while(c <= e /\ !MyP r){
     r <- PA.sampleFrom(d);
     c <- c + 1;
    }
    return r;
  }
}.


declare module A : RewRun {W}.



axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.


lemma asdistr_rew : forall (D : (glob A) -> irt -> rrt distr),
  (forall &m M a, mu (D (glob A){m} a) M = Pr[ GetRunSet(A).main(a) @ &m :  M res ])
  => forall &m a, equiv [PP(GetRunSet(A)).sampleFrom ~ GetRunSet(A).main : ={glob A} /\ arg{1} = (D (glob A){m} a) 
                         /\ (glob A){2} = (glob A){m} /\ arg{2} = a 
                         ==>  res{1} =  res{2} /\ (glob A){2} = (glob A){m} ].
progress.
bypr (res{1}, true) (res{2}, (glob A){2} = (glob A){m}). progress. smt.
progress. 
have ->: Pr[PP(GetRunSet(A)).sampleFrom(d{1}) @ &1 : (res, true) = a0]
 = Pr[PP(GetRunSet(A)).sampleFrom(d{1}) @ &1 : res = a0.`1 /\ a0.`2 = true].
rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[GetRunSet(A).main(z{2}) @ &2 : (res, (glob A) = (glob A){m}) = a0]
 = Pr[GetRunSet(A).main(z{2}) @ &2 : res  = a0.`1 /\ ((glob A) = (glob A){m})  = a0.`2].
rewrite Pr[mu_eq]. smt. auto.

case (a0.`2 = true). 
progress. rewrite H3. simplify.

have -> : Pr[GetRunSet(A).main(z{2}) @ &2 :
   res = a0.`1 /\ ((glob A) = (glob A){m}) = true]
 = Pr[GetRunSet(A).main(z{2}) @ &2 :
   res = a0.`1]. admit.

byequiv (_: ={glob A} /\ arg{2} = z{2} /\ (glob A){2} = (glob A){m} /\ arg{1} = D (glob A){m} z{2} ==> _). 
exists* z{2}. elim*. progress.
proc*.
call  (asdistr (GetRunSet(A)) D H &m arg_R ).
auto. progress. auto. 
admitted.

  
lemma zz  (da : (glob A) -> irt -> rrt distr) :  
 (forall &m (M : rrt -> bool) (a : irt),
       mu (da (glob A){m} a) M = Pr[GetRunSet(A).main(a) @ &m : M res])

 => forall &m P e (s : int) r ia,  0 <= s =>  
  Pr[ W(A).whp_d(da (glob A){m} ia,s,e,r) @ &m : P res ]
   = Pr[ W(A).whp_A(ia, s,e,r) @ &m : P res ].
progress. 
byequiv (_: ={s,e,r, glob A} /\ d{1} = (da (glob A){m} ia) /\ i{2} = ia
     /\ (glob A){2} = (glob A){m} ==> _). proc.
sp. 
exists* (glob A){2} . elim*. progress.
while (={W.c,r,e,glob A} /\ d{1} = da (glob A){m} ia /\ i{2} = ia /\ (glob A){m} = (glob A){2}).
wp.
call (asdistr' (GetRunSet(A)) da H &m ia).
skip. progress.    progress.
progress. auto.
qed.

