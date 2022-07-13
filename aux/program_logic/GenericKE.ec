pragma Goals:printall.
require import AllCore Distr List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require (*--*) FinType.

require import Averaging DProd RewWithInit.



require import RealExp.

require import AllpairsProp.


type ct, pt, rt, irt, auxt, sbits.

op d : ct distr.
axiom duni : is_uniform d.

op allcs : ct list.
axiom allcs_uniq : uniq allcs.
axiom allcs_all x : mu1 d x <> 0%r => x \in allcs.
axiom ss c : mu1 d c = 1%r/(size allcs)%r.

require BigPr.
clone import BigPr as BP with type ct  <- ct,
                              type pt  <- pt * auxt,
                              type rt  <- (rt * irt) * (rt * irt),
                              op    d  <- d,
                              op allcs <- allcs.


clone import RWI with type sbits <- sbits,
                      type iat <- pt * auxt,
                      type irt <- irt,
                      type rrt <- ct * rt .

module type Adv = {
  proc init(p : pt, aux : auxt) : irt
  proc run(i : irt, c : ct)  : rt
  proc getState() : sbits
  proc * setState(b : sbits) : unit
}.



module InitRun2(A : Adv) = {
  proc run(a : pt, aux : auxt) = {
    var i, c1, c2, r1, r2, pstate;
    i <@ A.init(a,aux);
    
    c1 <$ d;
    pstate <@ A.getState();
    r1 <@ A.run(i,c1);

    c2 <$ d;
    A.setState(pstate);
    r2 <@ A.run(i,c2);

    return ((c1,(r1,i)),(c2,(r2,i)));
  }
}.


module InitRun1(A : Adv) = {
  proc run(a : pt, aux : auxt) = {
    var i, c1, r1;
    i <@ A.init(a,aux);
    
    c1 <$ d;
    r1 <@ A.run(i,c1);

    return (c1,(r1,i));
  }
}.


section.
declare module A <: Adv.

declare axiom A_ll : islossless A.run.

declare axiom rewindable_A_plus : 
  exists (f : glob A -> sbits),
  injective f /\
  (forall (x : glob A),
    phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) /\
  (forall (x : glob A),
    hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) /\
  islossless A.getState /\
  (forall (x: glob A),
    phoare[A.setState: b = f x ==> glob A = x] = 1%r) /\
  (forall (x: glob A),
    hoare[A.setState: b = f x ==> glob A = x]) /\
  islossless A.setState.

local module C2 : Comp = {
  proc rest(p : pt * auxt, c1c2 : ct * ct) : (rt * irt) * (rt * irt) = {
    var r1, r2,i, pstate;
    i  <@ A.init(p);
    pstate <@ A.getState();
    r1 <@ A.run(i,c1c2.`1);
    A.setState(pstate);
    r2 <@ A.run(i,c1c2.`2);
    return ((r1,i),(r2,i));
  }
}.


local module C1 = {
  proc main(c1 : ct, p : pt * auxt) : rt * irt = {
    var r1,i;
    i  <@ A.init(p);
    r1 <@ A.run(i,c1);
    return (r1,i);
  }
}.

local module C1' = {
  proc main(c1 : ct, p : pt * auxt) : (ct * (rt * irt)) = {
    var r1,i;
    i  <@ A.init(p);
    r1 <@ A.run(i,c1);
    return (c1,(r1,i));
  }
}.


local module X1 = {
  proc run(p : pt * auxt) = {
    var c,r;
    c <$ d;
    r <@ C1.main(c,p);
    return (c,r);
  }
}.

local module A' = {
  proc run(i: irt) = {
     var c, r;
     c <$ d;
     r <@ A.run(i,c);   
     return (c,r);
  }
  proc init = A.init
  proc getState = A.getState
  proc setState = A.setState
}.

(* averaging  *)
clone import Avg as A with type at <- ct,
                      type at2 <- pt * auxt,
                      type rt <- ct * (rt * irt).

local lemma x0 &m M p : 
  big predT (fun (c : ct) => mu1 d c * Pr[C1.main(c,p) @ &m : M p (c, res)]) allcs =
     Pr[X1.run(p) @ &m : M p (res.`1, res.`2)].
have ->: Pr[X1.run(p) @ &m : M p (res.`1, res.`2)]
 = Pr[WorkAvg(C1').main(d,p) @ &m : M p res.`1].
byequiv. proc. sp. 
inline*. wp. 
call (_:true).  call (_:true). 
wp. 
rnd. skip. progress. auto. auto.
rewrite (averaging C1' &m (M p) p d).
rewrite - sumE_fin. smt. 
smt.
have ->: 
  (fun (c : ct) => mu1 d c * Pr[C1.main(c, p) @ &m : M p (c, res)]) =
  (fun (x : ct) => mu1 d x * Pr[C1'.main(x, p) @ &m : M p res]).
apply fun_ext. move => x.
have ->: Pr[C1.main(x, p) @ &m : M p (x, res)] = Pr[C1'.main(x, p) @ &m : M p res].
byequiv. proc. call (_:true). call (_:true). skip.
progress. auto. auto. auto. auto.
qed.


(* c1c2 <$ d * d ~ c1 <$ d ; c2 <$ d  *)
local lemma x1 &m M p: 
   Pr[X(C2).run(p) @ &m : M p res] = Pr[Xseq(C2).run(p) @ &m : M p res].
apply (x_xseq C2).
qed.


   
(* sum binding  *)
local lemma x2 &m M p:
  Pr[X1.run(p) @ &m : M p (res.`1, res.`2)] ^ 2 <=
  Pr[Xseq(C2).run(p) @ &m : M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2)].
have ->: Pr[X1.run(p) @ &m : M p (res.`1, res.`2)]
 = Pr[ QQ(A',A').main_run(p) @ &m : M p (res.`2.`1, (res.`2.`2, res.`1)) ].
byequiv. proc. inline*. swap {2} 3 -2. wp.
call (_:true). wp.  call (_:true). wp. rnd. skip. 
progress. auto. auto.
have ->: 
  Pr[Xseq(C2).run(p) @ &m :
   M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2)]
 =    Pr[ QQ(A',A').main(p) @ &m : M p (res.`1.`2.`1, (res.`1.`2.`2, res.`1.`1)) /\ M p  (res.`2.`2.`1, (res.`2.`2.`2, res.`2.`1)) ] .
byequiv. proc. inline*. swap {2} 4 -3. swap {2} 9 -7. wp.
call (_:true). wp.  call (_:true). wp.  call (_:true).
wp. call (_:true). call (_:true). wp. rnd. rnd. skip. progress.
auto. auto.
apply (rew_with_init A' A' &m (fun (r :  irt * (ct * rt)) => M p (r.`2.`1, (r.`2.`2, r.`1)) )).
qed.
   

local lemma avr_lemma_6_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M p res ] 
     = Pr[ Xseq(C2).run(p) @ &m  : M p res ] 
     - big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C2.rest(p,c1c2) @ &m :  M p (c1c2,res) ]) 
                   (cartprod2 allcs).
rewrite -  (x1 &m (fun p (r :  (ct * ct) * ((rt * irt) * (rt * irt))) => r.`1.`1 <> r.`1.`2 /\ M p r)).
rewrite (avr_lemma_6 C2 &m (M p) p).
rewrite - x1. auto.
qed.


local lemma avr_lemma_7_app &m M p c: 
 Pr[ C2.rest(p,(c,c)) @ &m :  M p (c, res.`1) /\ M p (c, res.`2) ]
  <= Pr[ C1.main(c,p) @ &m :  M p (c, res) ].
byequiv.
proc.
elim rewindable_A_plus.
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
seq 1 1 : ((c1{2}, p{2}) = (c, p) /\
  (p{1}, c1c2{1}) = (p, (c, c)) /\ (glob A){1} = (glob A){2} /\ ={i}).
call (_:true). skip. progress.
seq 2 1 : (={glob A,i,r1}).
exists* (glob A){2}. elim*. progress.
call (_:true). 
call {1} (s2 A_R). skip. progress.
call {1} (_: true ==> true). apply A_ll. call {1} s3ll.
auto. auto.  auto.
qed.


local lemma avr_lemma_8_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2) ] 

     >= Pr[ Xseq(C2).run(p) @ &m  : M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2)  ] 
     - big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C1.main(c1c2.`1,p) @ &m :  M p (c1c2.`1, res) ]) 
                   (cartprod2 allcs).
rewrite (avr_lemma_6_app &m (fun p (r :  (ct * ct) * ((rt * irt) * (rt * irt))) =>   M p (r.`1.`1, r.`2.`1) /\ M p (r.`1.`2, r.`2.`2))).
simplify.
have f2 :  big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * mu1 d c1c2.`2 *
     Pr[C2.rest(p, c1c2) @ &m : M p (c1c2.`1, res.`1) /\ M p (c1c2.`2, res.`2)])
  (cartprod2 allcs) <= 
  big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * mu1 d c1c2.`2 *
     Pr[C1.main(c1c2.`1,p) @ &m : M p (c1c2.`1, res)]) (cartprod2 allcs).
apply ler_sum. progress. 
   have : Pr[C2.rest(p, a) @ &m : M p (a.`1, res.`1) /\ M p (a.`2, res.`2)] <=
            Pr[C1.main(a.`1,p) @ &m : M p (a.`1, res)].
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
                    Pr[ C1.main(c1c2.`1,p) @ &m :  M p (c1c2.`1, res) ]) 
                    (cartprod2 allcs)
     = (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M p (res.`1, res.`2) ].
have ->: big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  ((mu1 d c1c2.`1) * (mu1 d c1c2.`2)) * 
                   Pr[ C1.main(c1c2.`1,p) @ &m :  M p (c1c2.`1, res) ]) 
                   (cartprod2 allcs)
      = big (fun r => fst r = snd r)  (fun (c1c2 : ct * ct) => 
                  (1%r/(size allcs)%r) * ((mu1 d c1c2.`1) * 
                   Pr[ C1.main(c1c2.`1,p) @ &m :  M p (c1c2.`1, res) ])) 
                   (cartprod2 allcs).
apply eq_big. auto. 
progress.
rewrite ss. rewrite ss. simplify. auto. simplify. 
have ->: big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     (1%r/(size allcs)%r) * (mu1 d c1c2.`1 * Pr[C1.main(c1c2.`1,p) @ &m : M p (c1c2.`1, res)]))
  (cartprod2 allcs)
 = (1%r/(size allcs)%r) * big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
      (mu1 d c1c2.`1 * Pr[C1.main(c1c2.`1,p) @ &m : M p (c1c2.`1, res)]))
  (cartprod2 allcs).
rewrite mulr_sumr. auto.
auto.
have ->: big (fun (r : ct * ct) => r.`1 = r.`2)
  (fun (c1c2 : ct * ct) =>
     mu1 d c1c2.`1 * Pr[C1.main(c1c2.`1,p) @ &m : M p (c1c2.`1, res)])
  (cartprod2 allcs)
   = big predT
      (fun (c : ct) =>
         mu1 d c * Pr[C1.main(c,p) @ &m : M p (c, res)])
          allcs.
have ->: big predT (fun (c : ct) => mu1 d c * Pr[C1.main(c,p) @ &m : M p (c, res)]) allcs = big predT (fun (c : ct) => mu1 d c * Pr[C1.main(c,p) @ &m : M p (c, res)]) 
    (map fst (filter (fun x => fst x = snd x) (cartprod2 allcs))). rewrite cart2_diag_unzip1. smt. auto.
rewrite big_mapT. 
rewrite - big_filter. rewrite  /(\o). auto.
 rewrite x0. auto.
qed.


local lemma avr_lemma_10_app &m M p : 
  Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 /\ M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2) ] >= 
  Pr[ Xseq(C2).run(p) @ &m  : M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2)  ] 
   - (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M p (res.`1, res.`2) ].
rewrite - avr_lemma_9_app.
apply avr_lemma_8_app.
qed.


local lemma avr_lemma_11_app &m M p : 
   Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 
            /\ M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2) ] 
       >= Pr[ X1.run(p) @ &m :  M p (res.`1, res.`2) ] ^2
          - (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M p (res.`1, res.`2) ].
apply (ler_trans (Pr[ Xseq(C2).run(p) @ &m  : M p (res.`1.`1, res.`2.`1) 
                                             /\ M p (res.`1.`2, res.`2.`2)  ] 
   - (1%r/(size allcs)%r) * Pr[ X1.run(p) @ &m :  M p (res.`1, res.`2) ])). 
have ff : Pr[X1.run(p) @ &m : M p (res.`1, res.`2)] ^ 2
     <= Pr[Xseq(C2).run(p) @ &m : M p (res.`1.`1, res.`2.`1) 
                                     /\ M p (res.`1.`2, res.`2.`2)].
apply x2.
smt. 
apply (avr_lemma_10_app &m M p).
qed.


lemma final_eq &m M p : 
   Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ M p res.`1 /\ M p res.`2 ] 
  >= Pr[ InitRun1(A).run(p) @ &m  :  M p res ]^2
          - (1%r/(size allcs)%r) * Pr[ InitRun1(A).run(p) @ &m  :  M p res ].
proof.
 have <-: Pr[ Xseq(C2).run(p) @ &m  : res.`1.`1 <> res.`1.`2 
            /\ M p (res.`1.`1, res.`2.`1) /\ M p (res.`1.`2, res.`2.`2) ] 
    = Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ M p res.`1 /\ M p res.`2 ].
byequiv. proc.  
simplify.
elim rewindable_A_plus.
move => fA [s1 [s2 [s2h [s2ll [s3 [s3h ]]]] ]] s3ll.
swap {2} 2 -1.
swap {2} 5 -3.
inline*. wp. 
call (_:true).
call (_:true).
call (_:true). 
call (_:true). 
call (_:true). 
wp.  
simplify.
rnd. rnd.
skip. progress. auto.  auto.
 have <-: Pr[ X1.run(p) @ &m :  M p (res.`1, res.`2) ]
    = Pr[ InitRun1(A).run(p) @ &m : M p res ].
byequiv. proc. inline*. swap {2} 2 -1. wp.
simplify.   call (_:true).  call (_:true). wp. rnd.
skip. progress. auto.  auto.
apply avr_lemma_11_app.
qed.


lemma final_eq_step1 &m AccRun SuccExtr p negl : 
   Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ AccRun p res.`1 /\ AccRun p res.`2
   /\ !SuccExtr p res.`1 res.`2 ] <= negl
  => 
   Pr[ InitRun2(A).run(p) @ &m : res.`1.`1 <> res.`2.`1 
            /\ AccRun p res.`1 /\ AccRun p res.`2 /\ SuccExtr p res.`1 res.`2 ] 
    >= (Pr[ InitRun1(A).run(p) @ &m  :  AccRun p res ]^2
         - (1%r/(size allcs)%r) * Pr[ InitRun1(A).run(p) @ &m  :  AccRun p res ])
        - negl.
progress.
have : Pr[InitRun1(A).run(p) @ &m : AccRun p res] ^ 2 -
  Pr[InitRun1(A).run(p) @ &m : AccRun p res] / (size allcs)%r <=
   Pr[InitRun2(A).run(p) @ &m : res.`1.`1 <> res.`2.`1 /\
       AccRun p res.`1 /\ AccRun p res.`2 /\ SuccExtr p res.`1 res.`2] + negl.
  apply (ler_trans    Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ AccRun p res.`1 /\ AccRun p res.`2 ] ).
  apply final_eq.  
rewrite Pr[mu_split SuccExtr p res.`1 res.`2]. 
have ->: Pr[InitRun2(A).run(p) @ &m :
   (res.`1.`1 <> res.`2.`1 /\ AccRun p res.`1 /\ AccRun p res.`2) /\
   SuccExtr p res.`1 res.`2] = Pr[InitRun2(A).run(p) @ &m :
   res.`1.`1 <> res.`2.`1 /\ AccRun p res.`1 /\ AccRun p res.`2 /\
   SuccExtr p res.`1 res.`2].
rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[InitRun2(A).run(p) @ &m :
   (res.`1.`1 <> res.`2.`1 /\ AccRun p res.`1 /\ AccRun p res.`2) /\
   !SuccExtr p res.`1 res.`2] = Pr[InitRun2(A).run(p) @ &m :
   res.`1.`1 <> res.`2.`1 /\ AccRun p res.`1 /\ AccRun p res.`2 /\
   !SuccExtr p res.`1 res.`2].
rewrite Pr[mu_eq]. smt. auto.
smt.
smt.
qed.





lemma qqq1  (a b : real) : a <= b  => sqrt a <= sqrt b.
smt. qed.


lemma qqq2  (a b : real) : a ^ 2 <= b  => a <= sqrt b.
smt. qed.


lemma final_eq_step2 &m AccRun SuccExtr p negl : 
   Pr[ InitRun2(A).run(p) @ &m 
          : res.`1.`1 <> res.`2.`1 /\ AccRun p res.`1 /\ AccRun p res.`2
   /\ !SuccExtr p res.`1 res.`2 ] <= negl
 => Pr[ InitRun2(A).run(p) @ &m 
          :  SuccExtr p res.`1 res.`2 ] = 0%r   
 => Pr[ InitRun1(A).run(p) @ &m  :  AccRun p res ]
   <=  sqrt (negl + 1%r/(size allcs)%r).
proof.  progress.
have f2 :     Pr[InitRun2(A).run(p) @ &m :
       res.`1.`1 <> res.`2.`1 /\
  AccRun p res.`1 /\ AccRun p res.`2 /\ SuccExtr p res.`1 res.`2] = 0%r.
  have ff2: Pr[InitRun2(A).run(p) @ &m :
       res.`1.`1 <> res.`2.`1 /\
  AccRun p res.`1 /\ AccRun p res.`2 /\ SuccExtr p res.`1 res.`2]
   <= 0%r. rewrite - H0.
   rewrite Pr[mu_sub]. smt. auto. 
  smt.
have f1 :    0%r 
    >= (Pr[ InitRun1(A).run(p) @ &m  :  AccRun p res ]^2
         - (1%r/(size allcs)%r) * Pr[ InitRun1(A).run(p) @ &m  :  AccRun p res ])
    - negl.
rewrite - f2.
apply (final_eq_step1 &m). assumption.
clear f2. clear H.
have f3 : Pr[InitRun1(A).run(p) @ &m : AccRun p res] ^ 2 
     <= 1%r / (size allcs)%r * Pr[InitRun1(A).run(p) @ &m : AccRun p res] + negl.
smt.
clear f1.
clear H0.
have : Pr[InitRun1(A).run(p) @ &m : AccRun p res] <=
    sqrt (1%r / (size allcs)%r * Pr[InitRun1(A).run(p) @ &m : AccRun p res] + negl).
apply qqq2. auto.
clear f3. simplify.
move => f4.
apply (ler_trans (sqrt (Pr[InitRun1(A).run(p) @ &m : AccRun p res] / (size allcs)%r + negl))).
auto.
apply qqq1. smt.
qed.


end section.

