pragma Goals:printall.
require import AllCore.
require import Distr.
require import List.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.

require import SquareConvex.


lemma bs : forall a, a <= 1%r => 0%r  <= a => a * a <= a. smt.
qed.

lemma hzc : forall (a b : real), a >= 0%r => b >= 1%r => a * b >= a. smt.
qed.

lemma bss : forall (a b c : real),  c <= b => 0%r < c => b <= 1%r => a >= 0%r => a / b <= a / c.  smt. qed.

lemma bsss : forall (a b c : real),  0%r < a => a <= 1%r  => b / a <= c / a => b <= c.  smt. qed.


lemma bs2 : forall (a : real), (square a) = a * a. smt. 
qed.

lemma Jensen_fin_without_lossless ['a] :
  forall (d : 'a distr) (f : 'a -> real),
    is_finite (support d) =>
    square (E d f) <= E d (square \o f).
proof.  
move => d f pr.
case (weight d = 0%r).
smt.
case (0%r <= weight d <= 1%r).
elim. 
move => wp1 wp2. move => wb.
have :     square (E (dscale d) f) <= E (dscale d) (square \o f).
apply Jensen_fin. smt. apply dscale_ll. 
smt. apply square_convex.
have : forall f, E (dscale d) f = (E d f) / (weight d).
move => g.
simplify E.
have : (fun (x : 'a) => g x * mass (dscale d) x) = (fun (x : 'a) =>  1%r/(weight d) * (g x * mass d x)).
apply fun_ext. move => x. simplify.
rewrite massE. smt.
move =>  k. rewrite k.
rewrite sumZ. smt.
move => l.
rewrite (l f).
rewrite (l (square \o f)).
have : square (E d f / weight d) = square (E d f) / square (weight d).
timeout 20. smt.
move => j. rewrite j.  clear j. clear l. clear pr.
move => wp3. 
have wp4 : square (weight d) <=  (weight d). rewrite  bs2. smt.
have wp5 : square (E d f) /  (weight d) <= square (E d f) / square (weight d). apply bss.
auto. smt. auto. smt.
apply (bsss (weight d) ). smt. auto. smt.
smt.
qed.


lemma jen_big ['a] :
  forall (d : 'a distr) (f : 'a -> real) J,
  is_finite (support d) => uniq J =>
    (forall (x : 'a), (fun (x : 'a) => f x * mass d x) x <> 0%r => x \in J) 
  => (big predT (fun (x : 'a) => f x * mass d x) J) ^ 2
    <= (big predT (fun (x : 'a) => square (f x) * mass d x) J).
proof. simplify.
move => d f J fd uJ pJ1. 
  have pJ2 : forall (x : 'a), (fun (x0 : 'a) => square (f x0) * mass d x0) x <> 0%r => x \in J.
auto. move => x. simplify. move => pr. apply pJ1.
   have : mass d x <> 0%r.  smt.
   smt.
rewrite - (sumE_fin (fun (x : 'a) => f x * mass d x) J uJ pJ1). 
rewrite - (sumE_fin (fun (x : 'a) => square (f x) * mass d x) J uJ pJ2).  
apply Jensen_fin_without_lossless.
auto.
qed.


lemma jen_big_spec ['a] :
  forall (d : 'a distr) (f : 'a -> real) J,
  is_finite (support d) => uniq J =>
    (forall (x : 'a), (fun (x : 'a) => f x * mass d x) x <> 0%r => x \in J) 
  => (big predT (fun (x : 'a) => mass d x * f x) J) ^ 2
    <= (big predT (fun (x : 'a) => mass d x * (f x) * (f x)) J).
proof. progress.
have : (fun (x : 'a) => mass d x * f x) = (fun (x : 'a) => f x * mass d x).
apply fun_ext. move => x. smt.
have : (fun (x : 'a) => mass d x * f x * f x) = (fun (x : 'a) => square (f x) * mass d x).
apply fun_ext. move => x. smt.
move => e1 e2. rewrite e1 e2.
apply jen_big.
auto. auto. auto.
qed.


op rest ['a] (f : 'a -> real) (J : 'a list)  (x : 'a) : real 
 = if x \in J then f x else 0%r.


lemma big_rest_gen ['a] : forall (J Q : 'a list) (f : 'a -> real), 
  (forall a, a \in J => a \in Q) =>
  big predT f J = big predT (rest f Q) J.
proof. apply list_ind. progress.
simplify. move => a l ih Q f Qp. 
have : big predT f (a :: l) = (f a) + big predT f l. smt.
move => e1. rewrite e1. clear e1.
have : big predT (rest f Q) (a :: l) = (rest f Q) a + big predT (rest f Q) l.
smt. move => e1. rewrite e1. clear e1.
simplify rest.
have : a \in Q. smt.
move => aq. rewrite aq. simplify.
rewrite (ih Q ). smt.
auto.
qed.


lemma big_rest ['a] : forall (J : 'a list) (f : 'a -> real), 
  big predT f J = big predT (rest f J) J.
proof. move => J f. apply big_rest_gen. auto.
qed.


lemma big_rest_sm ['a] : forall (J Q : 'a list) (f : 'a -> real), 
  (forall a, 0%r <= f a) =>
  big predT (rest f Q) J <= big predT f J.
proof. apply list_ind. smt.
simplify. move => x l ih. move => Q f.
have : big predT f (x :: l) = (f x) + big predT f l. smt.
move => e1. rewrite e1. clear e1.
have : big predT (rest f Q) (x :: l) = (rest f Q) x + big predT (rest f Q) l.
smt. move => e1. rewrite e1. clear e1.
move => ap. 
have : rest f Q x <= f x.
smt.
move => apc. 
have ihc : big predT (rest f Q) l <= big predT f l.
apply ih. auto.  
clear ih.
clear ap.
smt.
qed.


lemma jen_big_spec2 ['a] :
  forall (d : 'a -> real) (f : 'a -> real) J,
   uniq J => isdistr d
  => (big predT (fun (x : 'a) => d x * f x) J) ^ 2
    <= (big predT (fun (x : 'a) => d x * (f x) * (f x)) J).
proof. move => d f J u idp. case idp.
move => idp1 idp2.
have e : big predT (fun (x : 'a) =>  d x * f x) J = big predT (rest (fun (x : 'a) => d x * f x) J) J.  rewrite big_rest. auto.
rewrite e. clear e.
have e : big predT (fun (x : 'a) =>  d x * f x * f x) J = big predT (rest (fun (x : 'a) => d x * f x * f x) J) J.  rewrite big_rest. auto.
rewrite e. clear e.
simplify rest.  
have isd : isdistr ((fun x => if x \in J then d x else 0%r)). split. 
move => x. simplify. smt.
move => s us.
have : big predT (fun (x : 'a) => if x \in J then d x else 0%r) s <=  big predT d s .
  apply big_rest_sm. auto. 
smt.
have e : (fun (x : 'a) => if x \in J then d x * f x else 0%r) = (fun (x : 'a) => mass (mk (fun x => if x \in J then d x else 0%r)) x * f x ). apply fun_ext.
move => x. simplify.  smt.
rewrite e. clear e.
have e : (fun (x : 'a) => if x \in J then d x * f x * f x else 0%r) 
 = (fun (x : 'a) => mass (mk (fun x => if x \in J then d x else 0%r)) x * f x  * f x).
apply fun_ext. move => x. smt. rewrite e. clear e.
apply (jen_big_spec (mk (rest d J)) f).
exists (filter (fun x => d x > 0%r) J). split.
smt.
move => x. split. 
move => xj. simplify rest. 
have : support (mk (rest d J)) x.
   have : 0%r < d x . smt. move => m0.
   have : mu (mk (rest d J)) (pred1 x)  = d x. rewrite - massE.
   rewrite muK. auto.  have : x \in J. smt. move => xj'. smt.
   move => m1.
 smt.
auto.
move => xmrd. 
have : (rest d J) x <> 0%r.
have : (mass (mk (rest d J))) x <> 0%r. smt. 
rewrite muK. auto. auto.
move => kll.
have : d x <> 0%r. smt.
move => dxo. smt.
auto.
simplify.
move => x. rewrite muK. auto. 
smt.
qed.
