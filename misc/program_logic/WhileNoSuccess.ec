pragma Goals:printall.
require import AllCore Distr.


type sbits, iat, rrt, irt.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.

require WhileSplit.
clone import WhileSplit as IM with type sbits <- sbits,
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


                                  
require WhileNotB.                                  
clone import WhileNotB as WNB with type rt <- rrt.


section.



module DW = {
  var c : int
  proc whp_d(p : rrt -> bool,d : rrt distr, s : int, e : int, r : rrt) = { 
    c <- s;
    while(c <= e /\ !p r){
     r <@ SF.sampleFrom(d);
     c <- c + 1;
    }
    return r;
  }
}.



op MyPred : rrt -> bool.

declare module A <: HasRun {-W, -DW}.

declare axiom A_ll : islossless A.run.

declare axiom A_rew_ph x : phoare[ A.run : (glob A) = x ==> !MyPred res => (glob A) = x ] = 1%r.



lemma A_rew_h x : hoare[ A.run : (glob A) = x ==> !MyPred res => (glob A) = x ] .
bypr. progress. 
have <- : Pr[A.run(z{m}) @ &m : false ] = 0%r. smt.
have : 1%r = Pr[A.run(z{m}) @ &m : !(!MyPred res => (glob A) = (glob A){m}) ]
  + Pr[A.run(z{m}) @ &m : !MyPred res => (glob A) = (glob A){m} ].
   have <- :  Pr[A.run(z{m}) @ &m : true ] = 1%r. byphoare. apply  A_ll. auto. auto.
rewrite Pr[mu_split (!MyPred res => (glob A) = (glob A){m}) ]. smt.
have ->: Pr[A.run(z{m}) @ &m : (!MyPred res => (glob A) = (glob A){m}) ] = 1%r. byphoare (_: (glob A) = (glob A){m} ==> _). apply (A_rew_ph). auto. auto.
smt.
qed.




lemma asdistr_rew2 : forall (D : (glob A) -> irt -> rrt distr) ,
  (forall &m M a, mu (D (glob A){m} a) M = Pr[ A.run(a) @ &m :  M res ])
  => forall &m a, equiv [SF.sampleFrom ~ A.run : ={glob A} /\ arg{1} = (D (glob A){m} a) 
                         /\ (glob A){2} = (glob A){m} /\ arg{2} = a 
                         ==>  res{1} =  res{2} /\ (!MyPred res{2}  =>(glob A){2} = (glob A){m}) ].
progress.
bypr (res{1}, true) (res{2}, !MyPred res{2} => (glob A){2} = (glob A){m}). progress.  smt.
progress. 

have ->: Pr[SF.sampleFrom(d{1}) @ &1 : (res, true) = a0]
 = Pr[SF.sampleFrom(d{1}) @ &1 : res = a0.`1 /\ a0.`2 = true].
rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[A.run(z{2}) @ &2 : (res, (!MyPred res => (glob A) = (glob A){m})) = a0]
 = Pr[A.run(z{2}) @ &2 : res  = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m})  = a0.`2].
rewrite Pr[mu_eq]. smt. auto.
case (a0.`2 = true).
progress. rewrite H3. simplify.
have -> : Pr[A.run(z{2}) @ &2 :
   res = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m}) = true]
 = Pr[A.run(z{2}) @ &2 :
   res = a0.`1].

  have kj: Pr[A.run(z{2}) @ &2 : res = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[A.run(z{2}) @ &2 : !(!MyPred res => (glob A) = (glob A){m})] = 0%r.
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ A.run : (glob A) = ga ==>  (!MyPred res => (glob A) = ga) ] = 1%r.
    move => ga. apply A_rew_ph.  apply A_rew_h. auto. auto.
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
  have ->: Pr[A.run(z{2}) @ &2 : res = a0.`1 /\ (!MyPred res => (glob A) = (glob A){m}) = false] = 0%r.
   have : Pr[A.run(z{2}) @ &2 : !(!MyPred res => (glob A) = (glob A){m}) ] = 0%r.
   rewrite - H2.
   byphoare (_: (glob A) = (glob A){2} ==> _ ). hoare.  simplify.
    have f : forall ga, phoare[ A.run : (glob A) = ga ==> (!MyPred res => (glob A) = ga) ] = 1%r.
    move => ga. apply A_rew_ph. apply A_rew_h.  auto. auto.
     smt.
auto.
qed.




  
lemma zz  (da : (glob A) -> irt -> rrt distr) :  
 (forall &m (M : rrt -> bool) (a : irt),
       mu (da (glob A){m} a) M = Pr[A.run(a) @ &m : M res])
 => forall &m P e (s : int) rr ia,  
  Pr[ DW.whp_d(MyPred,da (glob A){m} ia,s,e,rr) @ &m : P res ]
   = Pr[ W(A).whp(MyPred,ia, s,e,rr) @ &m : P res ].
progress. 
byequiv (_: ={p,s,e,r, glob A} /\ d{1} = (da (glob A){m} ia) /\ i{2} = ia /\ p{1} = MyPred
     /\ (glob A){2} = (glob A){m} ==> _). proc.
sp. 
exists* (glob A){2} . elim*. progress.
while (={p,r,e} /\ DW.c{1} = W.c{2} /\ d{1} = da (glob A){m} ia /\ i{2} = ia /\   p{1} = MyPred /\ (!p{1} r{2} => ={glob A} /\ (glob A){2} = (glob A){m}) ).
wp.

call (asdistr_rew2  da H &m ia).
skip. progress.    smt.  smt.  smt. smt. skip. progress. smt.
progress. 
qed.



lemma final_zz &m (p : real)  i e ra :  MyPred ra = false => 0 <= e =>
   Pr[ A.run(i) @ &m : !MyPred res ]  = p
  => Pr[ W(A).whp(MyPred,i, 1,e,ra) @ &m : !MyPred res ] = (p ^ (e)).
case (e = 0).
progress.
have ->: Pr[A.run(i) @ &m : ! MyPred res] ^ 0 = 1%r. smt.
byphoare (_: e = 0 /\ s = 1 /\ MyPred ra = false /\ r = ra ==> _).
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
rewrite - (zz  D H0 &m (fun x => !MyPred x)).
have ->: Pr[DW.whp_d(MyPred, D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res]
 = Pr[M.whp(MyPred, D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res].
byequiv. proc. simplify.  sp. 
conseq (_: ={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}  ==> _). auto.
while (={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}). wp. inline*. wp.  rnd. wp. 
skip. progress. 
skip. progress. auto. auto.
byphoare(_: arg = (MyPred,D (glob A){m} i, 1, e' + 1 , ra ) ==> _).

have lf :   mu (D (glob A){m} i) (fun (x : rrt) => ! MyPred x) =
  Pr[A.run(i) @ &m : ! MyPred res].
rewrite H0. auto.

conseq (asdsadq (Pr[A.run(i) @ &m : ! MyPred res]) MyPred  ra (D (glob A){m} i) lf sf e' H ). auto.
auto.
qed.



lemma final_zz_le &m pr  i e ra :  MyPred ra = false => 0 <= e =>
   Pr[ A.run(i) @ &m : !MyPred res ]  <= pr
  => Pr[ W(A).whp(MyPred,i, 1,e,ra) @ &m : !MyPred res ] <= (pr ^ (e)).
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
rewrite - (zz  D H1 &m (fun x => !MyPred x)).
have ->: Pr[DW.whp_d(MyPred,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res]
 = Pr[M.whp(MyPred,D (glob A){m} i, 1, e' + 1 , ra) @ &m : !MyPred res].
byequiv. proc.  sp. 
conseq (_: ={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}  ==> _). auto.
while (={e,r} /\ p{1} = MyP{2} /\ DW.c{1} = M.c{2} /\ d{1} = myd{2}). wp. inline*. wp.  rnd. wp. 
skip. progress. 
skip. progress. auto. auto.
byphoare(_: arg = (MyPred,D (glob A){m} i, 1, e' + 1 , ra ) ==> _).

have lf :   mu (D (glob A){m} i) (fun (x : rrt) => ! MyPred x) <= pr. rewrite H1. auto.
conseq (asdsadq_le pr MyPred ra (D (glob A){m} i) lf sf e' H ). auto.
auto.
qed.




lemma final_zz_ph_le p  i e r :  MyPred r = false => 0 <= e =>
   phoare[ A.run : arg = i ==> !MyPred res ] <= p =>
   phoare [ W(A).whp : arg = (MyPred, i, 1,e,r) ==> !MyPred res ] <= (p ^ (e)).
move => sf ep ph1.
bypr. progress.
have ff : Pr[A.run(i) @ &m : ! MyPred res] <= p. 
byphoare (_: arg = i ==> _). apply ph1. auto. auto.
rewrite H. simplify.
apply (final_zz_le &m p  i e r sf ep ff).
qed.



(* lemma final_zz_lei &m (pr : real) MyPa i e ra :  MyPa ra = false => 0 <= e => *)
(*    (forall &m, Pr[ A.run(i) @ &m : !MyPa res ]  <= pr) => *)
(*    Pr[ W(A).whpi(MyPa,i, 1,e,ra) @ &m : !MyPa res ] <= (pr ^ e). *)
(* progress. *)
(* byphoare (_: arg = (MyPa, i, 1, e, ra) ==> _). *)
(* proc.  *)
(* call (final_zz_ph_le pr MyPa i e ra _ _ _).  *)
(* bypr. smt. *)
(* call (_:true). skip. auto. auto. auto. *)
(* qed. *)


lemma final_zz_ph &m p i e r :  MyPred r = false => 0 <= e =>
   phoare[ A.run : arg = i ==> !MyPred res ] = p =>
   phoare [ W(A).whp : arg = (MyPred,i, 1,e,r) ==> !MyPred res ] = (p ^ (e)).
move => sf ep ph1.
bypr. progress.
rewrite -  (final_zz &m0 p  i e r sf ep).
byphoare (_: arg = i ==> _). conseq ph1. auto. auto.
rewrite H. auto.
qed.



lemma final_zz_ph_m &m p i e r :  MyPred r = false => 0 <= e =>
   phoare[ A.run : arg = i /\ (glob A){m} = (glob A) ==> !MyPred res ] = p =>
   phoare [ W(A).whp : arg = (MyPred,i, 1,e,r) /\ (glob A){m} = (glob A) ==> !MyPred res ] = (p ^ e).
move => sf ep ph1.
bypr. progress. rewrite H. simplify.
rewrite -  (final_zz &m0 p  i e r sf ep). 
byphoare (_: arg = i /\ (glob A) = (glob A){m0} ==> _). conseq ph1. auto. auto.
auto. auto.
qed.


end section.
