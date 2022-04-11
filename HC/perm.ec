require import AllCore FSet .

(* require Subtype. *)

(* type nat. *)
(* clone import Subtype as A with type T <- int, *)
(* type sT <- nat, *)
(* pred P <- (fun (x : int) => 0 <= x). *)

(* op n : {int | 0 <= n} as geo. *)


type perm = (int * int) fset.

pred is_good (p : perm) (n : int) = 
 (forall i j, (i,j) \in p => 0 <= i < n /\ 0 <= j < n) /\
 (forall i j k, (i,j) \in p  => (i,k) \in p => j = k)  /\
 (forall i j k, (i,k) \in p  => (j,k) \in p => i = j)  /\
 (forall i, 0 <= i < n  => exists j, (i, j) \in p /\ 0 <= j < n) /\
 (forall j, 0 <= j < n  => exists i, (i, j) \in p /\ 0 <= i < n).



op id (n : int) : perm.
op IdProp (n : int) (l  : perm) = forall i j, (i,j) \in l <=> i=j /\ 0 <= i < n.

axiom id_lemma1 n : IdProp n (id n). 
lemma id_lemma2 n l1 l2 : IdProp n l1 => IdProp n l2 => l1 = l2. 
proof.  progress.
apply fsetP.
progress. smt.
smt.
qed.

 
op inv (p : perm) : perm.
axiom inv_lemma p i j :  (i,j) \in p <=> (j,i) \in (inv p).



lemma invinv (p : perm) : p = inv (inv p). apply fsetP.
smt.
qed.


lemma inv_good p n : is_good p n => is_good (inv p) n.
rewrite /is_good. progress. smt. smt. smt.
smt.  smt.  smt. 
have : exists (j : int), ((j, i) \in p) /\ 0 <= j && j < n.
apply H3. smt. 
elim. progress. exists j. 
smt.
have : exists (i : int), ((j, i) \in p) /\ 0 <= i && i < n.
apply H2. smt. elim. progress.
exists i. smt.
qed.


op comp (p1 p2 : perm) : perm.
axiom comp_lemma_1 p1 p2 i j k :  
  (i,j) \in p1 => 
  (j,k) \in p2 => 
  (i,k) \in (comp p1 p2).

  
axiom comp_lemma_2 p1 p2 i k :  
  (i,k) \in (comp p1 p2)
  => exists j, (i,j) \in p1 /\ (j,k) \in p2.

  
lemma comp_inv p n : is_good p n => comp p (inv p) = id n.
proof. progress.
apply (id_lemma2 n _ (id n)).
rewrite /IdProp.
progress.
smt.
smt. 
smt. 
smt.
smt.
qed.

lemma inv_comp p n : is_good p n => comp (inv p) p = id n.
proof. progress.
apply (id_lemma2 n _ (id n)).
rewrite /IdProp.
progress.
smt.
smt. 
smt. 
smt.
smt.
qed.

  
op app (p : perm) (l : 'a list) : 'a list.


axiom app_lemma  p (l : 'a list):  
    is_good p (size l)
 => forall i j, (i,j) \in p 
 => nth witness l i = nth witness (app p l) j.
