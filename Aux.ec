require import AllCore.

lemma andI (a b : bool) : a => b => a /\ b.
auto.
qed.


lemma oip1 (a b c eps : real) :  (0%r <= eps) =>
  `|a / b - c| <= eps
 => exists (p : real), 0%r <= p <= eps  /\ `|a / b - c| = p.
smt.
qed.


lemma oip2 (a b c p : real) :  
  (0%r < b) =>
  `|a / b - c| = p =>
      a = b * c - b * p \/  a = b * c + b * p.
smt.
qed.



lemma oip2b (a b c p : real) :  
  (0%r < b) =>
  (0%r <= p) =>
      a = b * c - b * p \/  a = b * c + b * p
   =>   `|a / b - c| = p.
smt.
qed.



lemma oip3 (a b c eps : real) :  (0%r < b) => (0%r <= eps) =>
  `|a / b - c| <= eps => 
  exists (p : real),  0%r <= p <= eps  
  /\ `|a / b - c| = p 
  /\ (a = b * (c - p) \/  a = b * (c + p)).
smt (oip1 oip2).
qed.



lemma oip4 (a c p : real) :  
  (0%r <= p) =>
   a = c - p \/  a = c + p
   => `|a - c| = p.
smt.
qed.


require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
require import Int.


lemma big_formula_p p  : 0%r <= p <= 1%r => forall n, 0 <= n  =>
 bigi predT (fun (i : int) => p^i * (1%r-p) ) 0 n 
 = 1%r - p^ n.
move => pa.  apply ge0ind. 
progress. smt.
progress.
have ->: 1%r - p ^ 0 = 0%r. smt.
smt.
progress.
search big.
rewrite big_int_recr. auto. simplify.
rewrite H0. auto.  smt.
qed.

lemma big_formula_1mp p  : 0%r <= p <= 1%r => forall n, 0 <= n  =>
 bigi predT (fun (i : int) => (1%r-p)^i * p) 0 n = 1%r - (1%r-p)^ n.
smt (big_formula_p).
qed.


lemma multn p  : 0%r <= p <= 1%r => forall n, 0 <= n => 0%r <= p^n <= 1%r.
move => cs.  apply ge0ind. smt.
smt.
simplify. progress. smt.
smt.
qed.

lemma big_geq0 p  : 0%r <= p <= 1%r => forall n, 
 0%r <= bigi predT (fun (i : int) => (1%r-p) ^ i * p) 0 n.
move => cs n.
case (0 <= n). move=> ma.
rewrite  big_formula_1mp.  auto. auto. smt (multn).
move => q. 
have : n < 0. smt.
move => qq.
rewrite big_geq. smt. auto.
qed.


lemma big_leq1 p  : 0%r <= p <= 1%r => forall n, 
 bigi predT (fun (i : int) => (1%r-p) ^ i * p) 0 n <= 1%r.
move => cs n.
case (0 <= n). move=> ma.
rewrite  big_formula_1mp.  auto. auto. smt.
move => q. 
have : n < 0. smt.
move => qq.
rewrite big_geq. smt. auto.
qed.



lemma ots' (a c : real) : 
  (0%r <= a) =>
  (0%r <= c <= 1%r) =>
  a * c  <= a.
proof. smt.
qed.

lemma ots (a b c e : real) : 
  (0%r <= b <= 1%r) =>
  (0%r <= c <= 1%r) =>
  `|a - c * b| <= e
    => `|a - b| <= e + (1%r-c).
progress.
have f : b = c * b + (1%r-c)*b. smt.
    + case (a <= c * b). 
    move => H8.
    have f2: c * b - a <= e. smt.
    have f22 : c * b - a >= 0%r. smt.
    have f3: c * b - a + (1%r - c)*b <= e + (1%r - c)*b.
    smt.  
    have f33 : c * b - a + (1%r - c)*b >= 0%r. smt.
    have f4: b - a <= e + (1%r - c)*b.
    smt.
    have f5: b - a <= e + (1%r - c).
    smt.
    have f44: b - a >= 0%r.
    smt.
    smt.
 + move => H8.
have : c*b <= a. smt.
clear H8. move => H8.
have f1 : a - c * b <= e. smt.
have f2: c * b - a + (1%r - c)*b <= e + (1%r - c)*b. smt.
have f3: b - a  <= e + (1%r - c)*b. smt.
have f4: b - a  <= e + (1%r - c). smt(ots').
smt.
qed.
