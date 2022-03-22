pragma Goals:printall.
require import AllCore Distr.


type sbits, iat, rrt, irt.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.

require IterModule.
clone import IterModule as IM with type sbits <- sbits,
                                   type iat <- iat,
                                   type rrt <- rrt,
                                   type irt <- irt.

require RewBasics.
clone import RewBasics as RW with type sbits <- sbits,
                                  type iat   <- iat,
                                  type iat2  <- irt,
                                  type rrt   <- rrt,
                                  type irt   <- irt,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.

                                  


require ReflectionTemp.
clone import ReflectionTemp.Refl as Re with
                                  type at  <- irt,
                                  type rt  <- rrt.


                                  
require While_not_b.                                  
clone import While_not_b as WNB with type rt <- rrt.


section.



module DW = {
  var c : int
  proc whp_d(p : rrt -> bool,d : rrt distr, s : int, e : int, r : rrt) = { 
    c <- s;
    while(c <= e /\ !p r){
     r <- SF.sampleFrom(d);
     c <- c + 1;
    }
    return r;
  }
}.

module W1 = {
 

}.





declare module A : HasRun {W, DW}.

axiom A_ll : islossless A.run.


  
lemma asdistr_rew : forall (D : (glob A) -> irt -> rrt distr),
  (forall &m M a, mu (D (glob A){m} a) M = Pr[ A.run(a) @ &m :  M res ])
  => forall &m a, equiv [SF.sampleFrom ~ A.run : ={glob A} /\ arg{1} = (D (glob A){m} a) 
                         /\ (glob A){2} = (glob A){m} /\ arg{2} = a 
                         ==>  res{1} =  res{2} /\ (glob A){2} = (glob A){m} ].
progress.
bypr (res{1}, true) (res{2}, (glob A){2} = (glob A){m}). progress. smt.
progress. 
have ->: Pr[SF.sampleFrom(d{1}) @ &1 : (res, true) = a0]
 = Pr[SF.sampleFrom(d{1}) @ &1 : res = a0.`1 /\ a0.`2 = true].
rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[A.run(z{2}) @ &2 : (res, (glob A) = (glob A){m}) = a0]
 = Pr[A.run(z{2}) @ &2 : res  = a0.`1 /\ ((glob A) = (glob A){m})  = a0.`2].
rewrite Pr[mu_eq]. smt. auto.
case (a0.`2 = true). 
progress. rewrite H3. simplify.
have -> : Pr[A.run(z{2}) @ &2 :
   res = a0.`1 /\ ((glob A) = (glob A){m}) = true]
 = Pr[A.run(z{2}) @ &2 :
   res = a0.`1]. 

  have kj: Pr[A.run(z{2}) @ &2 : res = a0.`1 /\ ((glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[A.run(z{2}) @ &2 : ((glob A) <> (glob A){m})] = 0%r.      
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ A.run : (glob A) = ga ==> (glob A) = ga] = 1%r. 
    move => ga. admit.  admit.
    auto. auto.
     smt.
smt.  
byequiv (_: ={glob A} /\ arg{2} = z{2} /\ (glob A){2} = (glob A){m} /\ arg{1} = D (glob A){m} z{2} ==> _). 
exists* z{2}. elim*. progress.
proc*.

call  (asdistr A D H &m arg_R ).
auto. progress. auto. 
move => hp.
have hpp : a0.`2 = false. smt.
clear hp.
rewrite hpp.
  have ->: Pr[SF.sampleFrom(d{1}) @ &1 : res = a0.`1 /\ false] = 0%r.
  smt.
  have ->: Pr[A.run(z{2}) @ &2 : res = a0.`1 /\ ((glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[A.run(z{2}) @ &2 : ((glob A) <> (glob A){m})] = 0%r.      
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ A.run : (glob A) = ga ==> (glob A) = ga] = 1%r. 
    move => ga. admit. admit. auto. auto.
     smt.
auto.
qed.


  
lemma zz MyPa  (da : (glob A) -> irt -> rrt distr) :  
 (forall &m (M : rrt -> bool) (a : irt),
       mu (da (glob A){m} a) M = Pr[A.run(a) @ &m : M res])
 => forall &m P e (s : int) r ia,  
  Pr[ DW.whp_d(MyPa,da (glob A){m} ia,s,e,r) @ &m : P res ]
   = Pr[ W(A).whp(MyPa,ia, s,e,r) @ &m : P res ].
progress. 
byequiv (_: ={p,s,e,r, glob A} /\ d{1} = (da (glob A){m} ia) /\ i{2} = ia
     /\ (glob A){2} = (glob A){m} ==> _). proc.
sp. 
exists* (glob A){2} . elim*. progress.
while (={p,r,e,glob A} /\ DW.c{1} = W.c{2} /\ d{1} = da (glob A){m} ia /\ i{2} = ia /\ (glob A){m} = (glob A){2}).
wp.
call (asdistr_rew  da H &m ia).
skip. progress.    progress.
progress. auto.
qed.



lemma final_zz &m (p : real) MyPa i e ra :  MyPa ra = false => 0 <= e =>
   Pr[ A.run(i) @ &m : !MyPa res ]  = p
  => Pr[ W(A).whp(MyPa,i, 1,e,ra) @ &m : !MyPa res ] = (p ^ (e)).
case (e = 0).
progress.
have ->: Pr[A.run(i) @ &m : ! MyPa res] ^ 0 = 1%r. smt.
byphoare (_: e = 0 /\ s = 1 /\ MyPa ra = false /\ r = ra ==> _).
simplify. proc. 
sp.
rcondf 1. skip. progress. skip. smt. smt. auto.  auto. 
move => ez sf ep.
have :  exists e', e' + 1 = e /\ 0 <= e'. smt.
elim. progress.
have exD :  exists (D : (glob A) -> irt -> rrt distr),
      forall &m (M : rrt -> bool) (a : irt),
        mu (D (glob A){m} a) M = Pr[A.run(a) @ &m : M res].
apply (reflection_simple_res A).
elim exD. progress. 
rewrite - (zz MyPa D H0 &m (fun x => !MyPa x)).
have ->: Pr[DW.whp_d(MyPa, D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPa res]
 = Pr[M.whp(MyPa, D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPa res].
byequiv. proc. simplify.  sp. 
conseq (_: ={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}  ==> _). auto.
while (={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}). wp. inline*. wp.  rnd. wp. 
skip. progress. 
skip. progress. auto. auto.
byphoare(_: arg = (MyPa,D (glob A){m} i, 1, e' + 1 , ra ) ==> _).

have lf :   mu (D (glob A){m} i) (fun (x : rrt) => ! MyPa x) =
  Pr[A.run(i) @ &m : ! MyPa res].
rewrite H0. auto.

conseq (asdsadq (Pr[A.run(i) @ &m : ! MyPa res]) MyPa  ra (D (glob A){m} i) lf sf e' H ). auto.
auto.
qed.



lemma final_zz_le &m pr MyPa i e ra :  MyPa ra = false => 0 <= e =>
   Pr[ A.run(i) @ &m : !MyPa res ]  <= pr
  => Pr[ W(A).whp(MyPa,i, 1,e,ra) @ &m : !MyPa res ] <= (pr ^ (e)).
case (e = 0).
progress.
byphoare (_: e = 0 /\ s = 1 /\ p ra = false /\ r = ra ==> _).
simplify. proc.
sp.
rcondf 1. skip. progress. skip. smt. smt. auto.  auto. 
move => ez sf ep.
have :  exists e', e' + 1 = e /\ 0 <= e'. smt.
elim. progress.
have exD :  exists (D : (glob A) -> irt -> rrt distr),
      forall &m (M : rrt -> bool) (a : irt),
        mu (D (glob A){m} a) M = Pr[A.run(a) @ &m : M res].
apply (reflection_simple_res A).
elim exD. progress. 
rewrite - (zz MyPa D H1 &m (fun x => !MyPa x)).
have ->: Pr[DW.whp_d(MyPa,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPa res]
 = Pr[M.whp(MyPa,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPa res].
byequiv. proc.  sp. 
conseq (_: ={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}  ==> _). auto.
while (={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}). wp. inline*. wp.  rnd. wp. 
skip. progress. 
skip. progress. auto. auto.
byphoare(_: arg = (MyPa,D (glob A){m} i, 1, e' + 1 , ra ) ==> _).

have lf :   mu (D (glob A){m} i) (fun (x : rrt) => ! MyPa x) <= pr. rewrite H1. auto.
conseq (asdsadq_le pr MyPa ra (D (glob A){m} i) lf sf e' H ). auto.
auto.
qed.



lemma final_zz_ph_le &m p MyPa i e r :  MyPa r = false => 0 <= e =>
   phoare[ A.run : arg = i ==> !MyPa res ] <= p =>
   phoare [ W(A).whp : arg = (MyPa, i, 1,e,r) ==> !MyPa res ] <= (p ^ (e)).
move => sf ep ph1.
bypr. progress.
have ff : Pr[A.run(i) @ &m0 : ! MyPa res] <= p. 
byphoare (_: arg = i ==> _). apply ph1. auto. auto.
rewrite H. simplify.
apply (final_zz_le &m0 p MyPa i e r sf ep ff).
qed.



lemma final_zz_ph &m p MyPa i e r :  MyPa r = false => 0 <= e =>
   phoare[ A.run : arg = i ==> !MyPa res ] = p =>
   phoare [ W(A).whp : arg = (MyPa,i, 1,e,r) ==> !MyPa res ] = (p ^ (e)).
move => sf ep ph1.
bypr. progress.
rewrite -  (final_zz &m0 p MyPa i e r sf ep).
byphoare (_: arg = i ==> _). conseq ph1. auto. auto.
rewrite H. auto.
qed.



lemma final_zz_ph_m &m p MyPa i e r :  MyPa r = false => 0 <= e =>
   phoare[ A.run : arg = i /\ (glob A){m} = (glob A) ==> !MyPa res ] = p =>
   phoare [ W(A).whp : arg = (MyPa,i, 1,e,r) /\ (glob A){m} = (glob A) ==> !MyPa res ] = (p ^ (e)).
move => sf ep ph1.
bypr. progress. rewrite H. simplify.
rewrite -  (final_zz &m0 p MyPa i e r sf ep). 
byphoare (_: arg = i /\ (glob A) = (glob A){m0} ==> _). conseq ph1. auto. auto.
auto. auto.
qed.


end section.
