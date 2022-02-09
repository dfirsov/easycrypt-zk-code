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

axiom A_ll : islossless A.run.


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
   res = a0.`1]. 

  have kj: Pr[GetRunSet(A).main(z{2}) @ &2 : res = a0.`1 /\ ((glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[GetRunSet(A).main(z{2}) @ &2 : ((glob A) <> (glob A){m})] = 0%r.      
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ GetRunSet(A).main : (glob A) = ga ==> (glob A) = ga] = 1%r. 
    print dbl1. move => ga.
    apply (dbl1 A RewProp (fun x => true) ). conseq A_ll. 
    conseq (f (glob A){2}).       auto. auto.
     smt.
smt.  
byequiv (_: ={glob A} /\ arg{2} = z{2} /\ (glob A){2} = (glob A){m} /\ arg{1} = D (glob A){m} z{2} ==> _). 
exists* z{2}. elim*. progress.
proc*.
call  (asdistr (GetRunSet(A)) D H &m arg_R ).
auto. progress. auto. 
move => hp.
have hpp : a0.`2 = false. smt.
clear hp.
rewrite hpp.
  have ->: Pr[PP(GetRunSet(A)).sampleFrom(d{1}) @ &1 : res = a0.`1 /\ false] = 0%r.
  smt.
  have ->: Pr[GetRunSet(A).main(z{2}) @ &2 : res = a0.`1 /\ ((glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[GetRunSet(A).main(z{2}) @ &2 : ((glob A) <> (glob A){m})] = 0%r.      
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ GetRunSet(A).main : (glob A) = ga ==> (glob A) = ga] = 1%r. 
    print dbl1. move => ga.
    apply (dbl1 A RewProp (fun x => true) ). simplify. conseq A_ll.
    conseq (f (glob A){2}).       auto. auto.
     smt.
auto.
qed.


  
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
call (asdistr_rew  da H &m ia).
skip. progress.    progress.
progress. auto.
qed.


lemma final_zz &m i e r : 
   Pr[ A.run(i) @ &m : MyP res ]  = 1%r/2%r
  => Pr[ W(A).whp_A(i, 1,e+1,r) @ &m : MyP res ] = ((1%r/2%r) ^ (e+1)).
admitted.
