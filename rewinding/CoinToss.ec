pragma Goals:printall.
require import Distr DBool Real Bool List RealSeries.
require RewSumBindingCommitment Averaging.

type sbits, irt, rrt,iat.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.


clone import RewSumBindingCommitment.SumBinding as SB
  with type sbits <- sbits,
       type irt <- irt,
       type rrt <- rrt,
       type iat <- iat,
       type message <- bool,
       op m1 <- false,
       op m2 <- true,
       op pair_sbits <- pair_sbits,
       op unpair <- unpair.

import CommitmentProtocol.

clone import Averaging.Avg as Av
  with type at <- bool,
       type rt <- value * bool * commitment * openingkey * bool,
       type at1 <- unit,
       type at2 <- unit.

       

module type CoinTossAlice = {
  proc commit(param : value) : commitment
  proc toss(r2 : bool)  : bool * openingkey
  proc getState() : sbits
  proc * setState(b : sbits) : unit   
}.


module B_t(A : CoinTossAlice) : RewindableSumBinder = {
  proc commit(p : value) = {
    var r;
    r <@ A.commit(p);
    return r;
  }
  proc open(x : bool) = {
    var d, r1 ;
    (r1 , d) <@ A.toss(!x);
    return d;
  }
  proc getState() : sbits = {
    var s;
    s <@ A.getState();
    return s;
  }  
  proc setState(b : sbits) : unit = {
    A.setState(b);
  }
}.


module B_f(A : CoinTossAlice) : RewindableSumBinder = {
  proc commit(p : value) = {
    var r;
    r <@ A.commit(p);
    return r;
  }
  proc open(x : bool) = {
    var d, r1 ;
    (r1 , d) <@ A.toss(x);
    return d;
  }
  proc getState() : sbits = {
    var s;
    s <@ A.getState();
    return s;
  }  
  proc setState(b : sbits) : unit = {
    A.setState(b);
  }
}.


module CTA(S : CommitmentScheme, A : CoinTossAlice) = {
  proc main() = {
     var p, r2, c, r1, d;
     p <@ S.gen();
     r2 <$ {0,1};
     c <@ A.commit(p);
     (r1, d) <@ A.toss(r2);
     return (p,r1,c,d,r2);
  }
}.


module CTAP(S : CommitmentScheme, A : CoinTossAlice) = {
  proc main(b:bool,u:unit) = {
     var p, c, r1, d;
     p <@ S.gen();
     c <@ A.commit(p);
     (r1, d) <@ A.toss(b);
     return (p,r1,c,d,b);
  }
}.


section.

declare module S <: CommitmentScheme.
declare module A <: CoinTossAlice{-S}.

axiom Aol : islossless A.toss.
axiom Acl : islossless A.commit.
axiom Sgl : islossless S.gen.

axiom RewPropA :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m}) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

axiom verify_det : forall a,
  phoare [ S.verify : arg = a ==> res = Ver a ] = 1%r.


local lemma RewPropB_t : exists (f : (glob B_t(A)) -> sbits),
  injective f /\
  (forall &m0,
     Pr[B_t(A).getState() @ &m0 :
        (glob B_t(A)) = (glob B_t(A)){m0} /\ res = f (glob B_t(A)){m0}] =
     1%r) /\
  (forall &m0 (b : sbits) (x : (glob B_t(A))),
     b = f x => Pr[B_t(A).setState(b) @ &m0 : (glob B_t(A)) = x] = 1%r) /\
  islossless B_t(A).setState.
proof. simplify. elim RewPropA.
progress. exists f. split. apply H.
split. progress. rewrite - (H0 &m0). 
byequiv. proc*. inline*. wp. call(_:true). skip. auto. auto. auto.
progress. rewrite - (H1 &m0 (f x) x). auto.
byequiv. proc*. inline*. sp.  call(_:true). skip. auto. auto. auto.
proc. call H2. skip. auto.
qed.

local lemma RewPropB_f : exists (f : (glob B_f(A)) -> sbits),
  injective f /\
  (forall &m0,
     Pr[B_f(A).getState() @ &m0 :
        (glob B_f(A)) = (glob B_f(A)){m0} /\ res = f (glob B_f(A)){m0}] =
     1%r) /\
  (forall &m0 (b : sbits) (x : (glob B_f(A))),
     b = f x => Pr[B_f(A).setState(b) @ &m0 : (glob B_f(A)) = x] = 1%r) /\
  islossless B_f(A).setState.
proof. simplify. elim RewPropA.
progress. exists f. split. apply H.
split. progress. rewrite - (H0 &m0). 
byequiv. proc*. inline*. wp. call(_:true). skip. auto. auto. auto.
progress. rewrite - (H1 &m0 (f x) x). auto.
byequiv. proc*. inline*. sp.  call(_:true). skip. auto. auto. auto.
proc. call H2. skip. auto.
qed.


local lemma ccc &m M :
      Pr[ CTA(S,A).main() @ &m : M res ] = Pr[WorkAvg(CTAP(S,A)).main({0,1}, tt) 
        @ &m : M res.`1].
proof. byequiv.       proc. inline*. sp.
swap {1} 2 -1. wp.
call (_:true). call (_:true). call(_:true).
wp.  rnd. skip. smt. auto. auto.
qed.


local lemma sumsum &m M :
 Pr[ CTA(S,A).main() @ &m : M res ] 
 = (sum (fun (x : bool) => mu1 {0,1} x 
                         * Pr[CTAP(S,A).main(x, tt) @ &m : M res])).
proof. rewrite ccc.
apply (averaging (CTAP(S,A)) &m ).
qed.


local lemma sumb g : sum g = g false + g true.
proof.
rewrite (sumE_fin g (false :: true :: [])).
smt. smt.
rewrite /big /filter.
have ->: (filter predT [false; true]) = [false; true].
smt. smt.
qed.


local lemma coin_toss_alice_true &m : 
    Pr[ CTA(S,A).main() @ &m : Ver (res.`1, res.`2, res.`3, res.`4)
      /\ (res.`2 ^^ res.`5) = true ] 
     <= 1%r / 2%r + Pr[ BindingExperiment(S,R(B_t(A))).main() @ &m : res ].
proof. 
have ->: Pr[ CTA(S,A).main() @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                 /\ (res.`2 ^^ res.`5) = true ] 
      = 1%r / 2%r * 
         (Pr[ CTAP(S,A).main(false,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                           /\ (res.`2 ^^ false) = true]
        + Pr[ CTAP(S,A).main(true,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                           /\ (res.`2 ^^  true) = true]).
rewrite (sumsum &m (fun (r : value * bool * commitment * openingkey * bool) 
                          => Ver (r.`1, r.`2, r.`3, r.`4) /\ r.`2 ^^ r.`5 = true)).
rewrite sumb.  simplify.
         have ->: mu1 {0,1} false = 1%r/2%r. smt.
         have ->: mu1 {0,1} true = 1%r/2%r. smt.         
have zz : forall q, Pr[CTAP(S, A).main(q, tt) 
                      @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                          /\ res.`2 ^^ res.`5 = true]
 = Pr[CTAP(S, A).main(q, tt) @ &m :
   Ver (res.`1, res.`2, res.`3, res.`4) /\ res.`2 ^^ q = true].
move => q. byequiv. proc. call (_:true). call (_:true). call(_:true). skip. 
smt. auto. auto.  rewrite (zz false). rewrite (zz true). smt.
have ->: Pr[ CTAP(S,A).main(false,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                          /\ (res.`2 ^^ false) = true]
       = Pr[ CTAP(S,A).main(false,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) /\ res.`2 = true]. 
       rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[ CTAP(S,A).main(true,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                         /\ (res.`2 ^^  true) = true]
       = Pr[ CTAP(S,A).main(true,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                         /\ res.`2 = false]. 
       rewrite Pr[mu_eq]. smt. auto.
have ineq1 : Pr[ CTAP(S,A).main(false,tt) 
               @ &m : Ver (res.`1, res.`2, res.`3, res.`4) /\ res.`2 = true]
    <= Pr[SumBindingExperiment(S, B_t(A)).main(true) @ &m : res].
byequiv. proc. inline*.
seq 3 7 : (p{1} = param{2} /\ c{1} = c{2} /\ r1{1} = r1{2} 
        /\ d{1} = d{2} /\ x{2} = true /\ m{2} = true).
wp. call (_:true). wp.  call (_:true). wp. call (_:true).
skip. progress.
conseq (_: exists a, a = (param,m,c,d){2} /\ p{1} = param{2} 
                       /\ ={c, r1, d} /\ m{2} = true ==> _).
smt.
elim*. progress.
call {2} (verify_det a). skip. progress.
auto. auto.
have ineq2 : Pr[ CTAP(S,A).main(true,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) /\ res.`2 = false]
    <= Pr[SumBindingExperiment(S, B_t(A)).main(false) @ &m : res].
byequiv. proc. inline*.
seq 3 7 : (p{1} = param{2} /\ c{1} = c{2} /\ r1{1} = r1{2} 
         /\ d{1} = d{2} /\ x{2} = false /\ m{2} = false).
wp. call (_:true). wp.  call (_:true). wp. call (_:true).
skip. progress.
conseq (_: exists a, a = (param,m,c,d){2} /\ p{1} = param{2} 
           /\ ={c, r1, d} /\ m{2} = false ==> _).
smt.
elim*. progress.
call {2} (verify_det a). skip. progress.
auto. auto.       
have ineq3 : Pr[SumBindingExperiment(S, B_t(A)).main(false) @ &m : res] +
      Pr[SumBindingExperiment(S, B_t(A)).main(true) @ &m : res] <=
      1%r + 2%r * Pr[BindingExperiment(S, R(B_t(A))).main() @ &m : res].      
apply (commitment_sum_binding S (B_t(A))).
(* apply RewPropB_t. *)
(* apply verify_det. *)
(* proc. call Aol. skip. auto. *)
(* proc. call Acl. skip. auto. *)
(* apply Sgl.       *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
smt. 
qed.


local lemma coin_toss_alice_false &m : 
    Pr[ CTA(S,A).main() @ &m : Ver (res.`1, res.`2, res.`3, res.`4)
      /\ (res.`2 ^^ res.`5) = false ] 
     <= 1%r / 2%r + Pr[ BindingExperiment(S,R(B_f(A))).main() @ &m : res ].
proof. 
have ->: Pr[ CTA(S,A).main() @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                 /\ (res.`2 ^^ res.`5) = false ] 
      = 1%r / 2%r * 
          (Pr[ CTAP(S,A).main(false,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                           /\ (res.`2 ^^ false) = false]
        +  Pr[ CTAP(S,A).main(true,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
            /\ (res.`2 ^^  true) = false]).
rewrite (sumsum &m (fun (r : value * bool * commitment * openingkey * bool) 
                        => Ver (r.`1, r.`2, r.`3, r.`4) /\ r.`2 ^^ r.`5 = false)).
rewrite sumb. simplify.
         have ->: mu1 {0,1} false = 1%r/2%r. smt.
         have ->: mu1 {0,1} true  = 1%r/2%r. smt.         
have zz : forall q, Pr[CTAP(S, A).main(q, tt) @ &m :
   Ver (res.`1, res.`2, res.`3, res.`4) /\ res.`2 ^^ res.`5 = false]
 = Pr[CTAP(S, A).main(q, tt) @ &m :
   Ver (res.`1, res.`2, res.`3, res.`4) /\ res.`2 ^^ q = false].
move => q. byequiv. proc. call (_:true). call (_:true). call(_:true). skip. smt. 
auto. auto. 
rewrite (zz false). rewrite (zz true). smt.
have ->: Pr[ CTAP(S,A).main(false,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                          /\ (res.`2 ^^ false) = false]
       = Pr[ CTAP(S,A).main(false,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                          /\ res.`2 = false]. 
       rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[ CTAP(S,A).main(true,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                          /\ (res.`2 ^^  true) = false]
       = Pr[ CTAP(S,A).main(true,tt) @ &m : Ver (res.`1, res.`2, res.`3, res.`4) 
                                          /\ res.`2 = true]. 
         rewrite Pr[mu_eq]. smt. auto.
have ineq1 : Pr[ CTAP(S,A).main(false,tt) 
               @ &m : Ver (res.`1, res.`2, res.`3, res.`4) /\ res.`2 = false]
    <= Pr[SumBindingExperiment(S, B_f(A)).main(false) @ &m : res].
byequiv. proc. inline*.
seq 3 7 : (p{1} = param{2} /\ c{1} = c{2} /\ r1{1} = r1{2} 
        /\ d{1} = d{2} /\ x{2} = false /\ m{2} = false).
wp. call (_:true). wp.  call (_:true). wp. call (_:true). skip. progress.
conseq (_: exists a, a = (param,m,c,d){2} /\ p{1} = param{2} /\ ={c, r1, d} 
           /\ m{2} = false ==> _). smt.
elim*. progress.
call {2} (verify_det a). skip. progress.
auto. auto.      
have ineq2 : Pr[ CTAP(S,A).main(true,tt) 
               @ &m : Ver (res.`1, res.`2, res.`3, res.`4)  /\ res.`2 = true]
    <= Pr[SumBindingExperiment(S, B_f(A)).main(true) @ &m : res].
byequiv. proc. inline*.
seq 3 7 : (p{1} = param{2} /\ c{1} = c{2} /\ r1{1} = r1{2} 
        /\ d{1} = d{2} /\ x{2} = true /\ m{2} = true).
wp. call (_:true). wp.  call (_:true). wp. call (_:true).
skip. progress.
conseq (_: exists a, a = (param,m,c,d){2} /\ p{1} = param{2} 
      /\ ={c, r1, d} /\ m{2} = true ==> _). smt.
elim*. progress.
call {2} (verify_det a). skip. progress.
auto. auto.      
have ineq3 : Pr[SumBindingExperiment(S, B_f(A)).main(false) @ &m : res] +
      Pr[SumBindingExperiment(S, B_f(A)).main(true) @ &m : res] <=
      1%r + 2%r * Pr[BindingExperiment(S, R(B_f(A))).main() @ &m : res].      
apply (commitment_sum_binding S (B_f(A))).
(* apply RewPropB_f. *)
(* apply verify_det. *)
(* proc. call Aol. skip. auto. *)
(* proc. call Acl. skip. auto. *)
(* apply Sgl. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair.       *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. apply ips. apply unpair_pair. *)
smt. 
qed.


op max (a b : real) = if a <= b then b else a.

lemma coin_toss_alice &m b: 
    Pr[ CTA(S,A).main() @ &m : Ver (res.`1, res.`2, res.`3, res.`4)
      /\ (res.`2 ^^ res.`5) = b ] 
     <= 1%r / 2%r + 
        max Pr[ BindingExperiment(S,R(B_t(A))).main() @ &m : res ]
            Pr[ BindingExperiment(S,R(B_f(A))).main() @ &m : res ].
proof. elim b.
smt (coin_toss_alice_true). smt (coin_toss_alice_false).
qed.

end section.


