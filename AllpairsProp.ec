pragma Goals:printall.
require import AllCore Distr List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries RealLub.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require (*--*) FinType.



section.
local lemma kiki2 ['a] : forall (l : 'a list), 
  unzip1 (map (fun (x : 'a) => (x, x)) l) = l.
elim. smt. smt.
qed.


local lemma kiki3 ['a] x :  forall (l : 'a list), uniq l => !(x \in l) =>
 filter (fun x => fst x = snd x)  (map ((fun (c1 c2 : 'a) => (c1, c2)) x) l)  = [].
elim. smt.
progress. 
smt.
qed.


local lemma kiki4 ['a] x :  forall (l : 'a list), uniq l => x \in l =>
 filter (fun x => fst x = snd x)  (map ((fun (c1 c2 : 'a) => (c1, c2)) x) l)  = (x, x) :: [].
elim. smt.
move => y H2 H3 H4 H5. 
case (x = y).
move => H6. rewrite H6. simplify.
 have f : !(x \in H2). smt.
apply  (kiki3 y). smt. smt.
move => q. rewrite q. simplify. apply H3. smt. smt.
qed.


local lemma kiki0 ['a] : forall (l1 l2 : 'a list), size l1 <= size l2 => uniq l1 => uniq l2 => (forall x, x \in l1 => x \in l2) =>
  (filter (fun x => fst x = snd x) (allpairs (fun (c1 c2 : 'a) => (c1, c2)) l1 l2)) = map (fun x => (x , x)) l1 .
proof. elim. smt.
progress.
rewrite allpairs_consl. simplify.
rewrite filter_cat. 
rewrite  (kiki4 x). auto. smt. simplify.
smt (filter_cat kiki4).
qed.


lemma cart2_diag_unzip1 ['a] (l : 'a list) : uniq l =>
  unzip1 (filter (fun x => fst x = snd x) ((allpairs (fun x y => (x,y))) l l)) = l.
move => q.
rewrite /cartprod2.  rewrite kiki0;auto.
rewrite kiki2. auto. 
qed.

end section.
