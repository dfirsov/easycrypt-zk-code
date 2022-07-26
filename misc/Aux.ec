require import AllCore List DJoin Distr.


lemma djoinmap_weight (d : 'a -> 'b distr) :  forall l,
  (forall x, is_lossless (d x)) =>
    weight (djoinmap d l) = 1%r.
elim. smt (weight_djoin_nil).
smt (weight_djoin_cons).
qed.


lemma kkk (a a' d zkp eps : real) :
   0%r <= a' <= a =>
   a - a' <= d =>
    `| a' - zkp | <= eps
    => `|a - zkp| <= eps + d.
smt().
qed.

lemma sub_all ['a]:
   forall (p1 p2 : 'a -> bool) (s : 'a list),
     (forall (x : 'a), p1 x => p2 x) => all p1 s => all p2 s.
move => p1 p2.  elim. smt().
smt().
qed.


lemma take_zip ['a 'b] : 
   forall  (n :  int) (l1 : 'a list)(l2 : 'b list),
   zip (take n l1) (take n l2) 
  = take n (zip l1 l2).
apply ge0ind. smt().
smt().
progress.
case (l1 = []).
smt().
progress.
have f1 : exists a1 l1', l1 = (a1 :: l1').
clear H0 H.  
exists (head witness l1) (behead l1).
smt().
elim f1.
progress. 
have -> : (n + 1 <= 0) = false.
smt(). simplify.
case (l2 = []).
smt().
progress. 
have f2 : exists a2 l2', l2 = (a2 :: l2').
exists (head witness l2) (behead l2).
smt().
elim f2.
progress. 
have -> : (n + 1 <= 0) = false.
smt(). simplify. smt().
qed.


lemma take_const ['a 'b] (c : 'b) f : forall (l : 'a list) ,
 all (fun x => f (c, x)) l =
   all f  (zip (nseq (size l) c) l).
proof. 
elim. smt().
progress. 
have ->: 1 + size l = size l + 1. smt().
rewrite nseqS. smt(@List).
simplify. smt().
qed.

lemma take_nseq ['a ] (c : 'a) : forall n ,
  (take n (nseq n c)) = nseq n c.
apply ge0ind. smt(@List).
smt(@List).
smt(@List).
qed.



type  ('a, 'b) sum = [Left of 'a | Right of 'b].

op is_right (s: ('a, 'b) sum) :  bool =
    with s = Left _ => false
    with s = Right _ => true.

op is_left (s: ('a, 'b) sum) :  bool =
    with s = Left _ => true
    with s = Right _ => false.

op proj_left (s: ('a, 'b) sum) : 'a =
    with s = Left x => x
    with s = Right _ => witness.

op proj_right (s: ('a, 'b) sum) : 'b =
    with s = Left _ => witness
    with s = Right x => x.


lemma andI (a b : bool) : a => b => a /\ b.
auto.
qed.


lemma oip1 (a b c eps : real) :  (0%r <= eps) =>
  `|a / b - c| <= eps
 => exists (p : real), 0%r <= p <= eps  /\ `|a / b - c| = p.
smt().
qed.


lemma oip2 (a b c p : real) :  
  (0%r < b) =>
  `|a / b - c| = p =>
      a = b * c - b * p \/  a = b * c + b * p.
smt().
qed.



lemma oip2b (a b c p : real) :  
  (0%r < b) =>
  (0%r <= p) =>
      a = b * c - b * p \/  a = b * c + b * p
   =>   `|a / b - c| = p.
smt(@Real).
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
smt().
qed.


require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
require import Int.


lemma big_formula_p p  : 0%r <= p <= 1%r => forall n, 0 <= n  =>
 bigi predT (fun (i : int) => p^i * (1%r-p) ) 0 n 
 = 1%r - p^ n.
move => pa.  apply ge0ind. 
progress. smt().
progress.
have ->: 1%r - p ^ 0 = 0%r. smt(@Real).
smt(@List).
progress.
rewrite big_int_recr. auto. simplify.
rewrite H0. auto.  smt(@Real).
qed.

lemma big_formula_1mp p  : 0%r <= p <= 1%r => forall n, 0 <= n  =>
 bigi predT (fun (i : int) => (1%r-p)^i * p) 0 n = 1%r - (1%r-p)^ n.
smt (big_formula_p).
qed.


lemma multn p  : 0%r <= p <= 1%r => forall n, 0 <= n => 0%r <= p^n <= 1%r.
move => cs.  apply ge0ind. smt().
smt(@Real).
simplify. progress. smt(@Real).
smt(@Real).
qed.

require import RealExp.
lemma multn2 (p q : real)  :  0%r <= p <= q => forall n, 0 <= n => p^n <= q^n.
move => cs.  apply ge0ind. smt().
smt(@Real).
simplify. progress. 
have ->: p ^ (n + 1) = p * p^n. smt(@Real).
have ->: q ^ (n + 1) = q * q^n. smt(@Real).
smt(@RealExp).
qed.


lemma big_split_min ['a]:
  forall (P0 : 'a -> bool) (F1 F2 : 'a -> real) (s : 'a list),
    big P0 (fun (i : 'a) => F1 i - F2 i) s = big P0 F1 s - big P0 F2 s.
proof.  progress.
have ->:  - big P0 F2 s
 =  (big P0 (fun x => - (F2 x) ) s).
apply (big_ind2 (fun (x : real) y => (- x) = y) ) .
smt(). smt().
progress.
apply big_split.
qed.


lemma big_geq0 p  : 0%r <= p <= 1%r => forall n, 
 0%r <= bigi predT (fun (i : int) => (1%r-p) ^ i * p) 0 n.
move => cs n.
case (0 <= n). move=> ma.
rewrite  big_formula_1mp.  auto. auto. smt (multn).
move => q. 
have : n < 0. smt().
move => qq.
rewrite big_geq. smt(). auto.
qed.


lemma big_leq1 p  : 0%r <= p <= 1%r => forall n, 
 bigi predT (fun (i : int) => (1%r-p) ^ i * p) 0 n <= 1%r.
move => cs n.
case (0 <= n). move=> ma.
rewrite  big_formula_1mp.  auto. auto. smt(@RealExp).
move => q. 
have : n < 0. smt().
move => qq.
rewrite big_geq. smt(). auto.
qed.



lemma ots' (a c : real) : 
  (0%r <= a) =>
  (0%r <= c <= 1%r) =>
  a * c  <= a.
proof. smt(). qed.


lemma ots (a b c e : real) : 
  (0%r <= b <= 1%r) =>
  (0%r <= c <= 1%r) =>
  `|a - c * b| <= e
    => `|a - b| <= e + (1%r-c).
progress.
have f : b = c * b + (1%r-c)*b. smt().
    + case (a <= c * b). 
    move => H8.
    have f2: c * b - a <= e. smt().
    have f22 : c * b - a >= 0%r. smt().
    have f3: c * b - a + (1%r - c)*b <= e + (1%r - c)*b.
    smt().  
    have f33 : c * b - a + (1%r - c)*b >= 0%r. smt().
    have f4: b - a <= e + (1%r - c)*b.
    smt().
    have f5: b - a <= e + (1%r - c).
    smt(@RealExp).
    have f44: b - a >= 0%r.
    smt().
    smt().
 + move => H8.
have : c*b <= a. smt().
clear H8. move => H8.
have f1 : a - c * b <= e. smt().
have f2: c * b - a + (1%r - c)*b <= e + (1%r - c)*b. smt().
have f3: b - a  <= e + (1%r - c)*b. smt().
have f4: b - a  <= e + (1%r - c). smt(ots').
smt().
qed.


lemma phase1_2 ['a] p (l : 'a list) n : 
 all p l
  =>  all p (take n l) .
smt(@List).
qed.

lemma aux_lem : forall l n,  
  size l = n =>
  nseq n true <> l  =>
  false \in l.
elim. smt(@List). smt(@List).
qed.

lemma phase1_3 ['a 'b] (l1 : 'a list) (l2 : 'b list) n : 
 take n (zip l1 l2) = zip (take n l1) (take n l2).
rewrite take_zip. auto.
qed.


section.
local lemma kiki2 ['a] : forall (l : 'a list), 
  unzip1 (map (fun (x : 'a) => (x, x)) l) = l.
elim. smt(). smt().
qed.


local lemma kiki3 ['a] x :  forall (l : 'a list), uniq l => !(x \in l) =>
 filter (fun x => fst x = snd x)  (map ((fun (c1 c2 : 'a) => (c1, c2)) x) l)  = [].
elim. smt().
progress. 
smt().
qed.


local lemma kiki4 ['a] x :  forall (l : 'a list), uniq l => x \in l =>
 filter (fun x => fst x = snd x)  (map ((fun (c1 c2 : 'a) => (c1, c2)) x) l)  = (x, x) :: [].
elim. smt().
move => y H2 H3 H4 H5. 
case (x = y).
move => H6. rewrite H6. simplify.
 have f : !(x \in H2). smt().
apply  (kiki3 y). smt(). smt().
move => q. rewrite q. simplify. apply H3. smt(). smt().
qed.


local lemma kiki0 ['a] : forall (l1 l2 : 'a list), size l1 <= size l2 => uniq l1 => uniq l2 => (forall x, x \in l1 => x \in l2) =>
  (filter (fun x => fst x = snd x) (allpairs (fun (c1 c2 : 'a) => (c1, c2)) l1 l2)) = map (fun x => (x , x)) l1 .
proof. elim. smt().
progress.
rewrite allpairs_consl. simplify.
rewrite filter_cat. 
rewrite  (kiki4 x). auto. smt(). simplify.
smt (filter_cat kiki4).
qed.


lemma cart2_diag_unzip1 ['a] (l : 'a list) : uniq l =>
  unzip1 (filter (fun x => fst x = snd x) ((allpairs (fun x y => (x,y))) l l)) = l.
move => q.
rewrite /cartprod2.  rewrite kiki0;auto.
rewrite kiki2. auto. 
qed.

end section.
