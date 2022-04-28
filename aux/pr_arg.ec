pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux FSet DJoin.


require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.



lemma pr1 (a b c : real) :  0%r < c =>
    `|a - b| = c * `|a/c - b/c|.
smt.
qed.

lemma pr2 (x e : real) : 
    0%r <= x <= 1%r
 => 0%r <= e <= 1%r 
 => x = x/(1%r + e) + x * e/(e + 1%r).
smt.
qed.


lemma pr3 (x e : real) : 
    0%r <= x <= 1%r
 => 0%r <= e <= 1%r 
 => x/(1%r + e) = x - x * e/(e + 1%r).
smt (pr2).
qed.


lemma pr4 (a b c : real) : c >= 0%r =>
  `|a - b + c| <= `|a - b| + c.
smt.
qed.

lemma pr5 (a b c : real) : c >= 0%r =>
  `|a - c - b | <= `|a - b| + c.
smt.
qed.

lemma pr6 (a b c : real) : 
  0%r <= a <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= c <= 1%r =>
  b <= a =>
  a <= c =>
  `|a - c| <= `|b - c|.
smt.
qed.



lemma pr7 (a b c : real) : 
  0%r <= a <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= c <= 1%r =>
  b <= a =>
  c <= a =>
  `|a - c| <= `|b - c + (a - b)|.
smt.
qed.

lemma pr8 (a b c : real) : 
  0%r <= a <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= c <= 1%r =>
  b <= a =>
  `|a - c| <= `|b - c| +  (a - b).
smt.
qed.



lemma pr9 (a b e : real) : 
  0%r <= a <= 1%r =>
  0%r <= b <= 1%r =>
  a + b = 1%r =>
  `| a - b | <= e =>
  a <= 1%r/2%r + e.
smt.
qed.


lemma pr10 (a b e : real) : 
  0%r <= a <= 1%r =>
  0%r <= b <= 1%r =>
  a + b = 1%r =>
  `| a - b | <= e =>
  a >= 1%r/2%r - e.
smt.
qed.

lemma pr_e1 (a e : real) : 
  0%r <= a <= 1%r =>
  `| a - 1%r/2%r | <= e =>
  a <= 1%r/2%r + e.
smt.
qed.


lemma pr_e2 (a e : real) : 
  0%r <= a <= 1%r =>
  `| a - 1%r/2%r | <= e =>
  a >= 1%r/2%r - e.
smt.
qed.



lemma pr11 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e <= 1%r =>
  x <= p =>
  p <= (1%r/2%r + e) =>
  `| x / p - 2%r * b| <=
  `| x / (1%r/2%r + e) - 2%r * b| + (x / p - x / (1%r/2%r + e)).
smt.
qed.


lemma pr12 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e <= 1%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
  (x / p - x / (1%r/2%r + e)) =  x * ((1%r/2%r + e) - p) / (p * (1%r/2%r + e))   .
smt.
qed.


lemma kk (a b c : real) : 
  a <= b =>
  0%r <= c <= 1%r =>
  a / c <= b / c.
smt.
qed.

lemma pr13 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e <= 1%r/2%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
  x * ((1%r/2%r + e) - p) / (p * (1%r/2%r + e)) 
    <=   x * (2%r * e) / (p * (1%r/2%r + e)) .
progress.
apply kk. smt. progress.
smt.
smt.
qed.

lemma pr14 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/2%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
     x * (2%r * e) / (p * (1%r/2%r + e)) 
     <=  x * (2%r * e) / ((1%r/2%r - e) * (1%r/2%r + e)).
smt.
qed.


lemma pr15 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/2%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
     x * (2%r * e) / ((1%r/2%r - e) * (1%r/2%r + e))
     =  x * (2%r * e) / ((1%r/4%r - e*e)).
smt.
qed.



lemma pr16 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
    x * (2%r * e) / ((1%r/4%r - e*e))
     <=   8%r * x * (2%r * e).
smt.
qed.

lemma pr17 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e)  =>
  (1%r/2%r - e)  <= p =>
       (x / p - x / (1%r/2%r + e))
     <=   16%r * e .
progress.
rewrite (pr12 x p b e);auto. smt.
apply (ler_trans (x * (2%r * e) / (p * (1%r/2%r + e)))).
apply (pr13 x p b e);auto. smt.
apply (ler_trans (x * (2%r * e) / ((1%r / 2%r - e) * (1%r / 2%r + e)))). 
apply (pr14 x p b e);auto. smt.
rewrite  (pr15 x p b e);auto. smt. smt.
qed.



lemma step1 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e) =>
  (1%r/2%r - e) <= p =>
  `| x / p - 2%r * b| <=
  `| x / (1%r/2%r + e) - 2%r * b| + 16%r * e.
progress.
apply (ler_trans (`| x / (1%r/2%r + e) - 2%r * b| + (x / p - x / (1%r/2%r + e)))). smt. 

have fff : (x / p - x / (1%r / 2%r + e)) <= 16%r * e.
apply (pr17 x p b e);auto.
smt.
qed.

lemma rp1 x e b  : 
  0%r <= x <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  `| x / (1%r/2%r + e) - 2%r * b|
  = 2%r * (`|x - x*2%r*e / (1%r + 2%r*e) - b|).
smt (pr3).
qed.

lemma rp2 x e b  : 
  0%r <= x <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  2%r * (`|x - x*2%r*e / (1%r + 2%r*e) - b|)
  <= 2%r * ((`|x - b|) + 2%r*e).
smt (pr5).
qed.

lemma step2 (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e) =>
  (1%r/2%r - e) <= p =>
   `| x / (1%r/2%r + e) - 2%r * b| + 16%r * e <=
    2%r * (`|x - b|) + 20%r * e.
progress.
rewrite rp1;auto. smt.
qed.

lemma main_fin (x p b e : real) : 
  0%r <= x <= 1%r =>
  0%r <= p <= 1%r =>
  0%r <= b <= 1%r =>
  0%r <= e < 1%r/4%r =>
  x <= p =>
  p <= (1%r/2%r + e) =>
  (1%r/2%r - e) <= p =>
  `| x / p - 2%r * b|  <= 2%r * `|x - b| + 20%r * e.
progress. apply (ler_trans (`| x / (1%r/2%r + e) - 2%r * b| + 16%r*e)). 
smt.
apply (step2 x p b e);auto.
qed.


(*
1. x = x/(1 + z) + xz/(z+1)
2. x/(1 + z) = x - xz/(z+1)
3. xz/(z+1) <= z

   |x / (1/2 + eps) - 2*b| 
=  2 * (|x / (1/2 + eps)/2 - 2*b/2|)
=  2 * (|x / (1 + 2*eps) - b|)
=  2 * (|x - x2eps/(1 + 2*eps) - b|)
<= 2 * (|x - b|) + 2x2eps/(1 + 2*eps)
<= 2 * (|x - b|) + 2*eps
<= 2 * eps + 2 * eps
<= 4eps
*)
