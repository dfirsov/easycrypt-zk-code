pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import Aux.


require import Permutation HC_Basics.
import ZK_defs.


lemma phase1_1 ['a 'b] p (l1 : 'a list) (l2 : 'b list) perm : 
 all p (zip l1 l2)
  =  all p (zip (ip perm l1) (ip perm l2)).
rewrite - zip_ip.
rewrite allP.
rewrite allP.
smt.
qed.


lemma phase1 ['a 'b] ver (l1 : 'a list) (l2 : 'b list) perm n : 
 all ver (zip l1 l2)
  =>  all ver (zip (take n (ip perm l1)) (take n (ip perm l2))).
progress.
rewrite - (phase1_3 (ip perm l1) (ip perm l2) n).
rewrite phase1_2.
rewrite - phase1_1.    
apply H.
qed.


    

lemma is_hc_perm_2 (n : int) (g : graph) (w : hc_wit) :
  !IsHC ((n,g),w) /\
     n = size w /\ 
     n * n = size g /\ 
     perm_eq w (range 0 n)
  => false \in (take n (hc_align w g)) .
progress.
  have : nseq (size w) true <> take (size w) (hc_align w g). smt.
progress.
have f : size (take (size w) (hc_align w g)) = size w.
  have ff : size (hc_align w g) = (size w) * (size w). smt.
  smt.
apply (aux_lem (take (size w) (hc_align w g)) (size w)).
auto. auto.
qed.

    
lemma phase2 (n : int) (g : graph) (w : hc_wit) :
  !IsHC ((n,g),w) /\
     n = size w /\ 
     n * n = size g /\ 
     perm_eq w (range 0 n) =>
   false \in (take n (hc_align w g)).
smt (is_hc_perm_2).
qed.


lemma phase3   (w : hc_wit) (g : graph) (n : int) c o1 p: 
   !HasHC (n,g) =>  
   hc_verify (n,g) c true  (Left (p,o1)) =>
   hc_verify (n,g) c false (Right (w,take n (hc_align w o1))) =>    
   all Ver (zip (nseq n true)  
                (take n (zip (hc_align w c)
                             (hc_align w o1)))) /\    
   all Ver (zip (take n (hc_align w (fap p g))) 
                (take n (zip (hc_align w c) 
                             (hc_align w o1)))) /\
   false \in (take n (hc_align w (fap p g))).  
proof. 
simplify.
progress.
rewrite - take_zip.
auto.
rewrite /hc_align.
rewrite - zip_ip.
apply (phase1 Ver (fap p g) (zip c o1) (prj w) (size w) H0).
have : ! HasHC (size w, fap p g). 
smt (fap_prop3).
have g1 :      perm_eq w (range 0 (size w)) /\
     (size w) * (size w) = size (fap p g).
split. auto. smt.
smt (phase2).
qed.


lemma quasi_fin ['a] (l' : bool list) n (l X : 'a list) ver : 
     false \in l'
  => all ver (zip (nseq n true) X)
  => all ver (zip l' l)
  => size l' = n
  => size l  = n
  => size X  = n
  => ver (true,  nth witness X (index false l')) /\
     ver (false, nth witness l (index false l')).
progress.
have f : (forall (i : int), 0 <= i && i < size (zip (nseq (size l') true) X) =>
            ver (nth witness (zip (nseq (size l') true) X) i)).
smt (all_nthP).

have : ver (nth witness (zip (nseq (size l') true) X) (index false l')). apply f. smt.
have ->:  (nth witness (zip (nseq (size l') true) X) (index false l')) = ((nth witness (nseq (size l') true) (index false l')), (nth witness X (index false l'))). timeout 20. smt.
smt.
have f : (forall (i : int), 0 <= i && i < size (zip l' l) =>
            ver (nth witness (zip l' l) i)).
smt (all_nthP).
have : ver (nth witness (zip l' l) (index false l')).
apply f. smt.
have ->: (nth witness (zip l' l) (index false l'))
  = ((nth witness l' (index false l')), (nth witness l (index false l'))). smt.
have ->: nth witness l' (index false l')
 = false. smt.
trivial.
qed.



lemma fin_bind_real   (w : hc_wit) (g : graph) (n : int) c o1 p X: 
   !HasHC (n,g) =>  
   hc_verify (n,g) c true  (Left (p,o1)) =>
   hc_verify (n,g) c false (Right (w,X)) 
  => Ver (true,  nth witness (take n (zip (hc_align w c)
                             X)) (index false (take n (hc_align w (fap p g))))) /\
     Ver (false, nth witness (take n (zip (hc_align w c)
                             (hc_align w o1))) (index false (take n (hc_align w (fap p g))))).
proof. 
move => p0 p1 p2 .
apply (quasi_fin ((take n (hc_align w (fap p g)))) n) .
apply is_hc_perm_2.   split.
smt. split. elim p2. smt.
split.  elim p1. smt. elim p1 p2. smt.
elim p1 p2. progress. smt.
elim p1 p2. progress. rewrite /hc_align. rewrite - zip_ip. apply phase1. auto.

elim p1 p2. progress.
  have : size (hc_align w (fap p g)) = (size w * size w). smt.
  smt.
elim p1 p2. progress.
  have : size (hc_align w c) = (size w) * (size w). 
  smt.
  have : size (hc_align w o1) = (size w) * (size w). 
  smt.
smt.
elim p2.
progress.
  have : size (hc_align w c) = (size w) * (size w). 
  smt.
smt.
qed.


