pragma Goals:printall.
require import AllCore Distr List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require (*--*) FinType.
require import DProd.




(*

Note: we use following lemmas:
  sumE_fin
  sum_pair_dep
  big_allpairs
  bigEM
*)

type ct,rt,pt.

op d : ct distr.


clone import ProdSampling with type t1 <- ct,
                               type t2 <- ct.



op allcs : ct list.
axiom allcs_uniq : uniq allcs.
axiom allcs_all x : mu1 d x <> 0%r => x \in  allcs.

module type Comp = {
  proc rest (p : pt, c1c2 : ct * ct) : rt
}.


module type Run = {
  proc run (p : pt, c : ct) : rt
}.

module X(C : Comp) = {
  proc run(p : pt) = {
    var c1c2, r;
    c1c2 <$ d `*` d;
    r <@ C.rest(p,c1c2);
    return (c1c2,r);
  }
}.


module Xseq(C : Comp) = {
  proc run(p : pt) = {
    var c1,c2, r;
    c1 <$ d;
    c2 <$ d;
    r <@ C.rest(p,(c1,c2));
    return ((c1,c2),r);
  }
}.


require import Averaging.
section.


local clone import Avg as A with type at <- ct * ct,
                      type at2 <- pt,
                      type rt <- (ct * ct) * rt.


module C'(C : Comp) = {
  proc main(c1c2:ct*ct,i2 : pt) = {
    var r;
    r <@ C.rest(i2,c1c2);
    return (c1c2,r);
  }
}.


lemma avr &m M  p:  forall (C <: Comp),
  Pr[ X(C).run(p) @ &m  : M res ] 
     = sum (fun c1c2 => 
      (mu1 (d `*` d) c1c2) * Pr[ C.rest(p,c1c2) @ &m : M (c1c2,res) ]).
progress.
have ->: Pr[X(C).run(p) @ &m : M res] = Pr[WorkAvg(C'(C)).main(d `*` d, p) @ &m : M res.`1].
byequiv. proc. inline*. wp. call (_:true).
wp. rnd. wp.  skip.  progress. auto. auto. 
rewrite (averaging (C'(C))).
have ->: (fun (x : ct * ct) => mu1 (d `*` d) x * Pr[C'(C).main(x, p) @ &m : M res])
 = (fun (c1c2 : ct * ct) =>
     mu1 (d `*` d) c1c2 * Pr[C.rest(p, c1c2) @ &m : M (c1c2, res)]).
apply fun_ext. move => x.
have ->: Pr[C'(C).main(x, p) @ &m : M res] = Pr[C.rest(p, x) @ &m : M (x, res)].
byequiv. proc*. inline*. wp.  sp. call (_:true). skip. progress. auto. auto.
auto. auto.
qed.



local module X'(C : Comp) = {
  proc run(p : pt) = {
    var c1c2, r;
    c1c2 <@ S.sample(d,d);
    r <@ C.rest(p,c1c2);
    return (c1c2,r);
  }
}.


local module Xseq'(C : Comp) = {
  proc run(p : pt) = {
    var c1,c2, r;
    (c1,c2) <@ S.sample2(d,d);
    r <@ C.rest(p,(c1,c2));
    return ((c1,c2),r);
  }
}.



declare module C <: Comp.


lemma x_xseq &m M p: 
   Pr[X(C).run(p) @ &m : M p res] = Pr[Xseq(C).run(p) @ &m : M p res].
have ->: Pr[X(C).run(p) @ &m : M p res] 
    = Pr[X'(C).run(p) @ &m : M p res]. byequiv. proc.  inline*.
sp.  call (_:true). wp.  rnd.  skip. progress. auto. auto. 
have ->: Pr[Xseq(C).run(p) @ &m : M p res] 
    = Pr[Xseq'(C).run(p) @ &m : M p res]. byequiv. proc.  inline*.
sp.  call (_:true). wp.  rnd.  rnd. skip. progress. auto. auto. 
byequiv. proc. 
seq 1 1 : (={glob C,p} /\ (c1c2{1} = (c1,c2){2})). 
call sample_sample2. skip.  progress. smt().
call (_:true). skip. progress. auto.  auto.
qed.
  

local lemma avr_lemma_1 &m M p : 
  Pr[ X(C).run(p) @ &m  : M res ] 
     = big predT (fun c1c2 => 
        (mu1 (d `*` d) c1c2) * Pr[ C.rest(p,c1c2) @ &m : M (c1c2,res) ]) (allpairs (fun c1 c2 => (c1,c2))  allcs allcs) .
proof. rewrite -  sumE_fin. apply allpairs_uniq. apply allcs_uniq. apply allcs_uniq. smt().
progress. 
apply allpairsP. exists x. progress.

have : mu1 d x.`1 <> 0%r.  smt(@Distr).
apply allcs_all. 
apply allcs_all.  smt(@Distr).
smt().
apply (avr _ _ _ C).
qed.


lemma avr_lemma_2 &m M p : 
     big predT (fun c1c2 => 
        (mu1 (d `*` d) c1c2) * Pr[ C.rest(p,c1c2) @ &m : M (c1c2,res) ]) (allpairs (fun c1 c2 => (c1,c2))  allcs allcs)
   = big predT (fun (c1c2 : ct * ct) => 
        ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * Pr[ C.rest(p,c1c2) @ &m : M (c1c2,res) ]) (allpairs (fun c1 c2 => (c1,c2))  allcs allcs).
apply eq_big. auto.
progress.
rewrite - dprod1E. smt().
qed.


local lemma avr_lemma_3 &m M N p f l : 
  big predT (fun (c1c2 : ct * ct) => 
        (f c1c2) * Pr[ C.rest(p,c1c2) @ &m : N c1c2 /\ M (c1c2,res) ]) l
  = big N (fun (c1c2 : ct * ct) => 
        (f c1c2) * Pr[ C.rest(p,c1c2) @ &m : M (c1c2,res) ]) l.
rewrite  (big_mkcond N).
apply eq_big.
auto. simplify. progress.
case (N i). auto.
simplify. rewrite Pr[mu_false]. simplify. auto.
qed.

op cartprod2 (l : 'a list)  = (allpairs (fun c1 c2 => (c1,c2)) l l).


local lemma avr_lemma_4 &m M p : 
  Pr[ X(C).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M res ] 
     = big (fun (r : ct * ct) => r.`1 <> r.`2) 
           (fun (c1c2 : ct * ct) => 
             ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                Pr[ C.rest(p,c1c2) @ &m :  M (c1c2,res) ]) 
                  (cartprod2 allcs).
rewrite  (avr_lemma_1 &m (fun r => (fst (fst r)) <> (snd (fst r)) /\ M r ) ). 
simplify.
rewrite (avr_lemma_2 &m (fun r => (fst (fst r)) <> (snd (fst r)) /\ M r )).
simplify.
rewrite - avr_lemma_3.
simplify. auto.
qed.


local lemma avr_lemma_5 &m M p : 
  Pr[ X(C).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M res ] 
     = big predT  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C.rest(p,c1c2) @ &m :  M (c1c2,res) ]) 
                   (cartprod2 allcs)
     - big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C.rest(p,c1c2) @ &m :  M (c1c2,res) ]) 
                   (cartprod2 allcs).
rewrite (bigEM (fun (r : ct * ct) => r.`1 = r.`2)).
rewrite /predC.  rewrite avr_lemma_4. 
have f : forall (a b : real), a = b + a - b. smt().
apply f.
qed.


lemma avr_lemma_6 &m M p : 
  Pr[ X(C).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M res ] 
     = Pr[ X(C).run(p) @ &m  : M res ] 
     - big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C.rest(p,c1c2) @ &m :  M (c1c2,res) ]) 
                   (cartprod2 allcs).
rewrite avr_lemma_1.
rewrite avr_lemma_2. 
apply avr_lemma_5.
qed.
end section.



