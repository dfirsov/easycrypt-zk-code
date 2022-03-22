pragma Goals:printall.
require import AllCore Distr List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require (*--*) FinType.

require import AllpairsProp.


type ct, pt, rt, irt.

op d : ct distr.
axiom duni : is_uniform d.

op allcs : ct list.
axiom allcs_uniq : uniq allcs.

axiom ss c : mu1 d c = 1%r/(size allcs)%r.

require BigPr.
clone import BigPr as BP with type ct  <- ct,
                              type pt  <- pt,
                              type rt  <- rt * rt,
                              op    d  <- d,
                              op allcs <- allcs.

module type Adv = {
  proc init(p : pt) : irt
  proc run(i : irt, c : ct)  : rt
}.



module InitRun2(A : Adv) = {
  proc run(a : pt) = {
    var i, c1, c2, r1, r2;
    i <- A.init(a);
    
    c1 <$ d;
    r1 <- A.run(i,c1);

    c2 <$ d;
    r2 <- A.run(i,c2);

    return ((c1,r1),(c2,r2));
  }
}.


module InitRun1(A : Adv) = {
  proc run(a : pt) = {
    var i, c1, r1;
    i <- A.init(a);
    
    c1 <$ d;
    r1 <- A.run(i,c1);

    return (c1,r1);
  }
}.


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


(* averging  *)
local lemma x0 &m M p : 
  big predT (fun (c : ct) => mu1 d c * Pr[C1.rest(p, c) @ &m : M (c, res)]) allcs =
     Pr[X1.run(p) @ &m : M (res.`1, res.`2)].
admitted.


(* c1c2 <$ d * d ~ c1 <$ d ; c2 <$ d  *)
local lemma x1 &m M p: 
   Pr[X(C2).run(p) @ &m : M res] = Pr[Xseq(C2).run(p) @ &m : M res].
admitted.
   
(* sum binding  *)
local lemma x2 &m M p:
  Pr[X1.run(p) @ &m : M (res.`1, res.`2)] ^ 2 <=
  Pr[Xseq(C2).run(p) @ &m : M (res.`1.`1, res.`2.`1) /\ M (res.`1.`2, res.`2.`2)].
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
 Pr[ C2.rest(p,(c,c)) @ &m :  M (c, res.`1) /\ M (c, res.`2) ]
  <= Pr[ C1.rest(p,c) @ &m :  M (c, res) ].
byequiv.
proc.
seq 2 2 : (={glob A,i,r1}).
call (_:true). call (_:true). skip. progress.
call {1} (_: true ==> true). apply A_ll. skip. progress. auto.
auto.
qed.


local lemma avr_lemma_8_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M (res.`1.`1, res.`2.`1) /\ M (res.`1.`2, res.`2.`2) ] 

     >= Pr[ Xseq(C2).run(p) @ &m  : M (res.`1.`1, res.`2.`1) /\ M (res.`1.`2, res.`2.`2)  ] 
     - big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C1.rest(p,c1c2.`1) @ &m :  M (c1c2.`1, res) ]) 
                   (cartprod2 allcs).
rewrite (avr_lemma_6_app &m (fun (r :  (ct * ct) * (rt * rt)) =>   M (r.`1.`1, r.`2.`1) /\ M (r.`1.`2, r.`2.`2))).
simplify.
have f2 :  big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * mu1 d c1c2.`2 *
     Pr[C2.rest(p, c1c2) @ &m : M (c1c2.`1, res.`1) /\ M (c1c2.`2, res.`2)])
  (cartprod2 allcs) <= 
  big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * mu1 d c1c2.`2 *
     Pr[C1.rest(p, c1c2.`1) @ &m : M (c1c2.`1, res)]) (cartprod2 allcs).
apply ler_sum. progress. 
   have : Pr[C2.rest(p, a) @ &m : M (a.`1, res.`1) /\ M (a.`2, res.`2)] <=
            Pr[C1.rest(p, a.`1) @ &m : M (a.`1, res)].
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
                    Pr[ C1.rest(p,c1c2.`1) @ &m :  M (c1c2.`1, res) ]) 
                    (cartprod2 allcs)
     = (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M (res.`1, res.`2) ].
have ->: big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C1.rest(p,c1c2.`1) @ &m :  M (c1c2.`1, res) ]) 
                   (cartprod2 allcs)
      = big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  (1%r/(size allcs)%r) * ((mu1 d c1c2.`1) * 
                   Pr[ C1.rest(p,c1c2.`1) @ &m :  M (c1c2.`1, res) ])) 
                   (cartprod2 allcs).
apply eq_big. auto. 
progress.
rewrite ss. rewrite ss. simplify. auto. simplify. 
have ->: big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     (1%r/(size allcs)%r) * (mu1 d c1c2.`1 * Pr[C1.rest(p, c1c2.`1) @ &m : M (c1c2.`1, res)]))
  (cartprod2 allcs)
 = (1%r/(size allcs)%r) * big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
      (mu1 d c1c2.`1 * Pr[C1.rest(p, c1c2.`1) @ &m : M (c1c2.`1, res)]))
  (cartprod2 allcs).
rewrite mulr_sumr. auto.
auto.
have ->: big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * Pr[C1.rest(p, c1c2.`1) @ &m : M (c1c2.`1, res)])
  (cartprod2 allcs)
   = big predT
      (fun (c : ct) =>
         mu1 d c * Pr[C1.rest(p, c) @ &m : M (c, res)])
          allcs.
have ->: big predT (fun (c : ct) => mu1 d c * Pr[C1.rest(p, c) @ &m : M (c, res)]) allcs = big predT (fun (c : ct) => mu1 d c * Pr[C1.rest(p, c) @ &m : M (c, res)]) 
    (map fst (filter (fun x => fst x = snd x) (cartprod2 allcs))). rewrite cart2_diag_unzip1. smt. auto.
rewrite big_mapT. 
rewrite - big_filter. rewrite  /(\o). auto.
 rewrite x0. auto.
qed.


local lemma avr_lemma_10_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M (res.`1.`1, res.`2.`1) /\ M (res.`1.`2, res.`2.`2) ] >= 
  Pr[ Xseq(C2).run(p) @ &m  : M (res.`1.`1, res.`2.`1) /\ M (res.`1.`2, res.`2.`2)  ] 
   - (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M (res.`1, res.`2) ].
rewrite - avr_lemma_9_app.
apply avr_lemma_8_app.
qed.


local lemma avr_lemma_11_app &m M p : 
   Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 
            /\ M (res.`1.`1, res.`2.`1) /\ M (res.`1.`2, res.`2.`2) ] 
       >= Pr[ X1.run(p) @ &m :  M (res.`1, res.`2) ] ^2
          - (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M (res.`1, res.`2) ].
apply (ler_trans (Pr[ Xseq(C2).run(p) @ &m  : M (res.`1.`1, res.`2.`1) 
                                             /\ M (res.`1.`2, res.`2.`2)  ] 
   - (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M (res.`1, res.`2) ])). 
have ff : Pr[X1.run(p) @ &m : M (res.`1, res.`2)] ^ 2
     <= Pr[Xseq(C2).run(p) @ &m : M (res.`1.`1, res.`2.`1) 
                                     /\ M (res.`1.`2, res.`2.`2)].
apply x2.
smt. 
apply (avr_lemma_10_app &m M p).
qed.


lemma final_eq &m M p : 
   Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ M res.`1 /\ M res.`2 ] 
  >= Pr[ InitRun1(A).run(p) @ &m  :  M res ]^2
          - (1%r/(size allcs)%r) * Pr[ InitRun1(A).run(p) @ &m  :  M res ].
proof.
 have <-: Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 
            /\ M (res.`1.`1, res.`2.`1) /\ M (res.`1.`2, res.`2.`2) ] 
    = Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ M res.`1 /\ M res.`2 ].
byequiv. proc.  simplify.
swap {2} 2 -1.
swap {2} 4 -2.
inline*. wp. 
call (_:true).
call (_:true).
call (_:true). wp.  simplify.
rnd. rnd.
skip. progress. auto.  auto.
 have <-: Pr[ X1.run(p) @ &m :  M (res.`1, res.`2) ] 
    = Pr[ InitRun1(A).run(p) @ &m : M res ].
byequiv. proc. inline*. swap {2} 2 -1. wp. 
simplify.   call (_:true).  call (_:true). wp. rnd. 
skip. progress. auto.  auto.
apply avr_lemma_11_app.
qed.


lemma final_eq_step1 &m AccRun SuccExtr p negl : 
   Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ AccRun res.`1 /\ AccRun res.`2
   /\ !SuccExtr res.`1 res.`2 ] <= negl
  => 
   Pr[ InitRun2(A).run(p) @ &m : res.`1.`1 <> res.`2.`1 
                                 /\ AccRun res.`1 /\ AccRun res.`2 /\ SuccExtr res.`1 res.`2 ] 
    >= (Pr[ InitRun1(A).run(p) @ &m  :  AccRun res ]^2
         - (1%r/(size allcs)%r) * Pr[ InitRun1(A).run(p) @ &m  :  AccRun res ])
    - negl.
progress.
have : Pr[InitRun1(A).run(p) @ &m : AccRun res] ^ 2 -
  Pr[InitRun1(A).run(p) @ &m : AccRun res] / (size allcs)%r <=
   Pr[InitRun2(A).run(p) @ &m : res.`1.`1 <> res.`2.`1 /\
       AccRun res.`1 /\ AccRun res.`2 /\ SuccExtr res.`1 res.`2] + negl.
  apply (ler_trans    Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ AccRun res.`1 /\ AccRun res.`2 ] ).
  apply final_eq.  
rewrite Pr[mu_split SuccExtr res.`1 res.`2]. 
have ->: Pr[InitRun2(A).run(p) @ &m :
   (res.`1.`1 <> res.`2.`1 /\ AccRun res.`1 /\ AccRun res.`2) /\
   SuccExtr res.`1 res.`2] = Pr[InitRun2(A).run(p) @ &m :
   res.`1.`1 <> res.`2.`1 /\ AccRun res.`1 /\ AccRun res.`2 /\
   SuccExtr res.`1 res.`2].
rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[InitRun2(A).run(p) @ &m :
   (res.`1.`1 <> res.`2.`1 /\ AccRun res.`1 /\ AccRun res.`2) /\
   !SuccExtr res.`1 res.`2] = Pr[InitRun2(A).run(p) @ &m :
   res.`1.`1 <> res.`2.`1 /\ AccRun res.`1 /\ AccRun res.`2 /\
   !SuccExtr res.`1 res.`2].
rewrite Pr[mu_eq]. smt. auto.
smt.
smt.
qed.


require import RealExp.


lemma qqq1  (a b : real) : a <= b  => sqrt a <= sqrt b.
smt. qed.


lemma qqq2  (a b : real) : a ^ 2 <= b  => a <= sqrt b.
smt. qed.


lemma final_eq_step2 &m AccRun SuccExtr p negl : 
   Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ AccRun res.`1 /\ AccRun res.`2
   /\ !SuccExtr res.`1 res.`2 ] <= negl
 => Pr[ InitRun2(A).run(p) @ &m 
          :  SuccExtr res.`1 res.`2 ] = 0%r   
 => Pr[ InitRun1(A).run(p) @ &m  :  AccRun res ]
   <=  sqrt (negl + 1%r/(size allcs)%r).
proof.  progress.
have f2 :     Pr[InitRun2(A).run(p) @ &m :
       res.`1.`1 <> res.`2.`1 /\
  AccRun res.`1 /\ AccRun res.`2 /\ SuccExtr res.`1 res.`2] = 0%r.
  have ff2: Pr[InitRun2(A).run(p) @ &m :
       res.`1.`1 <> res.`2.`1 /\
  AccRun res.`1 /\ AccRun res.`2 /\ SuccExtr res.`1 res.`2]
   <= 0%r. rewrite - H0.
   rewrite Pr[mu_sub]. smt. auto. 
  smt.
have f1 :    0%r 
    >= (Pr[ InitRun1(A).run(p) @ &m  :  AccRun res ]^2
         - (1%r/(size allcs)%r) * Pr[ InitRun1(A).run(p) @ &m  :  AccRun res ])
    - negl.
rewrite - f2.
apply (final_eq_step1 &m). assumption.
clear f2. clear H.
have f3 : Pr[InitRun1(A).run(p) @ &m : AccRun res] ^ 2 
     <= 1%r / (size allcs)%r * Pr[InitRun1(A).run(p) @ &m : AccRun res] + negl.
smt.
clear f1.
clear H0.
have : Pr[InitRun1(A).run(p) @ &m : AccRun res] <=
    sqrt (1%r / (size allcs)%r * Pr[InitRun1(A).run(p) @ &m : AccRun res] + negl).
apply qqq2. auto.
clear f3. simplify.
move => f4.
apply (ler_trans (sqrt (Pr[InitRun1(A).run(p) @ &m : AccRun res] / (size allcs)%r + negl))).
auto.
apply qqq1. smt.
qed.


end section.

