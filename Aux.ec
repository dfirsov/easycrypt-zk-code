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


axiom big_geq0 p  : 0%r <= p <= 1%r => forall n, 
 0%r <= bigi predT (fun (i : int) => (1%r-p) ^ i * p) 0 n.
axiom big_leq1 p  : 0%r <= p <= 1%r => forall n, 
 bigi predT (fun (i : int) => (1%r-p) ^ i * p) 0 n <= 1%r.
