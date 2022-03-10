pragma Goals:printall.
require import AllCore Distr List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require (*--*) FinType.



type ct,pt,rt, irt.

op d : ct distr.
axiom duni : is_uniform d.

search is_uniform.

op umc : real.
axiom ss c : mu1 d c = umc.

op allcs : ct list.
axiom allcs_uniq : uniq allcs.


require BigPr.
clone import BigPr as BP with type ct <- ct,
                              type pt <- pt,
                              type rt <- rt * rt,
                              op d <- d,
                              op allcs <- allcs.

module type Adv = {
  proc init(p : pt) : irt
  proc run(i : irt, c : ct)  : rt
}.


lemma kiki2 ['a] : forall (l : 'a list), 
  unzip1 (map (fun (x : 'a) => (x, x)) l) = l.
elim. smt. smt.
qed.

lemma kiki3 ['a] x :  forall (l : 'a list), uniq l => !(x \in l) =>
 filter (fun x => fst x = snd x)  (map ((fun (c1 c2 : 'a) => (c1, c2)) x) l)  = [].
elim. smt.
progress. 
smt.
qed.


lemma kiki4 ['a] x :  forall (l : 'a list), uniq l => x \in l =>
 filter (fun x => fst x = snd x)  (map ((fun (c1 c2 : 'a) => (c1, c2)) x) l)  = (x, x) :: [].
elim. smt.
move => y H2 H3 H4 H5. 
case (x = y).
move => H6. rewrite H6. simplify.
 have f : !(x \in H2). smt.
apply  (kiki3 y). smt. smt.
move => q. rewrite q. simplify. apply H3. smt. smt.
qed.


lemma kiki0 ['a] : forall (l1 l2 : 'a list), size l1 <= size l2 => uniq l1 => uniq l2 => (forall x, x \in l1 => x \in l2) =>
  (filter (fun x => fst x = snd x) (allpairs (fun (c1 c2 : 'a) => (c1, c2)) l1 l2)) = map (fun x => (x , x)) l1 .
proof. elim. smt.
progress. rewrite /cartprod2.
rewrite allpairs_consl. simplify.
rewrite filter_cat. 
rewrite  (kiki4 x). auto. smt. simplify.
smt (filter_cat kiki4).
qed.


lemma kiki ['a] (l : 'a list) : uniq l =>
  unzip1 (filter (fun x => fst x = snd x) (cartprod2 l)) = l.
move => q.
rewrite /cartprod2.  rewrite kiki0;auto.
rewrite kiki2. auto. 
qed.


section.
declare module A : Adv.

axiom A_ll : islossless A.run.

local module C2 : Comp = {
  proc rest(p : pt, c1c2 : ct * ct) : rt * rt = {
    var r1, r2,i;
    i  <@ A.init(p);
    r1 <@ A.run(i,c1c2.`1);
    r2 <@ A.run(i,c1c2.`2);
    return (r1,r2);
  }
}.


local module C1 = {
  proc rest(p : pt, c1 : ct) : rt = {
    var r1,i;
    i  <@ A.init(p);
    r1 <@ A.run(i,c1);
    return r1;
  }
}.

local module X1 = {
  proc run(p : pt) = {
    var c,r;
    c <$ d;
    r <- C1.rest(p,c);
    return (c,r);
  }
}.



local lemma x0 &m M p : 
  big predT (fun (c : ct) => mu1 d c * Pr[C1.rest(p, c) @ &m : M c res]) allcs =
     Pr[X1.run(p) @ &m : M res.`1 res.`2].
admitted.


local lemma x1 &m M p: 
   Pr[X(C2).run(p) @ &m : M res] = Pr[Xseq(C2).run(p) @ &m : M res].
admitted.

   
local lemma x2 &m M p:
  Pr[X1.run(p) @ &m : M res.`1 res.`2] ^ 2 <=
  Pr[Xseq(C2).run(p) @ &m : M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2].
admitted.
   

local lemma avr_lemma_6_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M res ] 
     = Pr[ Xseq(C2).run(p) @ &m  : M res ] 
     - big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C2.rest(p,c1c2) @ &m :  M (c1c2,res) ]) 
                   (cartprod2 allcs).
rewrite -  (x1 &m (fun (r :  (ct * ct) * (rt * rt)) => r.`1.`1 <> r.`1.`2 /\ M r)).
rewrite (avr_lemma_6 C2 &m M p).
rewrite - x1. auto.
qed.


local lemma avr_lemma_7_app &m M p c: 
 Pr[ C2.rest(p,(c,c)) @ &m :  M c res.`1 /\ M c res.`2 ]
  <= Pr[ C1.rest(p,c) @ &m :  M c res ].
byequiv.
proc.
seq 2 2 : (={glob A,i,r1}).
call (_:true). call (_:true). skip. progress.
call {1} (_: true ==> true). apply A_ll. skip. progress. auto.
auto.
qed.


local lemma avr_lemma_8_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2 ] 
     >= Pr[ Xseq(C2).run(p) @ &m  : M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2  ] 
     - big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C1.rest(p,c1c2.`1) @ &m :  M c1c2.`1 res ]) 
                   (cartprod2 allcs).
rewrite (avr_lemma_6_app &m (fun (r :  (ct * ct) * (rt * rt)) =>   M r.`1.`1 r.`2.`1 /\ M r.`1.`2 r.`2.`2)).
simplify.
have f2 :  big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * mu1 d c1c2.`2 *
     Pr[C2.rest(p, c1c2) @ &m : M c1c2.`1 res.`1 /\ M c1c2.`2 res.`2])
  (cartprod2 allcs) <= 
  big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * mu1 d c1c2.`2 *
     Pr[C1.rest(p, c1c2.`1) @ &m : M c1c2.`1 res]) (cartprod2 allcs).
apply ler_sum. progress. 
   have : Pr[C2.rest(p, a) @ &m : M a.`1 res.`1 /\ M a.`2 res.`2] <=
            Pr[C1.rest(p, a.`1) @ &m : M a.`1 res].
    rewrite H.
      have ->: a = (a.`1,a.`1).  smt. simplify.
      apply (avr_lemma_7_app &m M p ). 
     smt.
have f3  : forall (a b c : real), b <= c => a - b >= a - c.
smt.
apply f3.
apply f2.
qed.


local lemma avr_lemma_9_app &m M p : 
     big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C1.rest(p,c1c2.`1) @ &m :  M c1c2.`1 res ]) 
                   (cartprod2 allcs)
     =   umc * Pr[ X1.run(p) @ &m :  M res.`1 res.`2 ].
have ->: 
       big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C1.rest(p,c1c2.`1) @ &m :  M c1c2.`1 res ]) 
                   (cartprod2 allcs)
      = big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  umc * ((mu1 d c1c2.`1) * 
                   Pr[ C1.rest(p,c1c2.`1) @ &m :  M c1c2.`1 res ])) 
                   (cartprod2 allcs).
apply eq_big. auto.
progress.
rewrite ss. rewrite ss. auto. smt.
have ->: big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     umc * (mu1 d c1c2.`1 * Pr[C1.rest(p, c1c2.`1) @ &m : M c1c2.`1 res]))
  (cartprod2 allcs)
 = umc * big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
      (mu1 d c1c2.`1 * Pr[C1.rest(p, c1c2.`1) @ &m : M c1c2.`1 res]))
  (cartprod2 allcs).
rewrite mulr_sumr. auto.
auto.
have ->: big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * Pr[C1.rest(p, c1c2.`1) @ &m : M c1c2.`1 res])
  (cartprod2 allcs)
   = big predT
      (fun (c : ct) =>
         mu1 d c * Pr[C1.rest(p, c) @ &m : M c res])
          allcs.
have ->: big predT (fun (c : ct) => mu1 d c * Pr[C1.rest(p, c) @ &m : M c res]) allcs = big predT (fun (c : ct) => mu1 d c * Pr[C1.rest(p, c) @ &m : M c res]) 
    (map fst (filter (fun x => fst x = snd x) (cartprod2 allcs))). rewrite kiki. smt. auto.
rewrite big_mapT. 
rewrite - big_filter. rewrite  /(\o). auto.
 rewrite x0. auto.
qed.


local lemma avr_lemma_10_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2 ] >= 
  Pr[ Xseq(C2).run(p) @ &m  : M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2  ] 
   - umc * Pr[ X1.run(p) @ &m :  M res.`1 res.`2 ].
rewrite - avr_lemma_9_app.
apply avr_lemma_8_app.
qed.


local lemma avr_lemma_11_app &m M p : 
   Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2  ] 
       >= Pr[ X1.run(p) @ &m :  M res.`1 res.`2 ] ^2
          - umc * Pr[ X1.run(p) @ &m :  M res.`1 res.`2 ].
apply (ler_trans (Pr[ Xseq(C2).run(p) @ &m  : M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2  ] 
   - umc * Pr[ X1.run(p) @ &m :  M res.`1 res.`2 ])). 
   have ff : Pr[X1.run(p) @ &m : M res.`1 res.`2] ^ 2
     <= Pr[Xseq(C2).run(p) @ &m : M res.`1.`1 res.`2.`1 /\ M res.`1.`2 res.`2.`2].
   apply x2.
smt. 
apply (avr_lemma_10_app &m M p).
qed.
