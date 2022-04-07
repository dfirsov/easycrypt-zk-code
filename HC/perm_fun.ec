require import AllCore List.

type perm = int -> int.



pred is_good (p : perm) (n : int) = 
 (forall i j k, p i = k => p j = k => i = j)  /\
 (forall i, 0 <= i < n  <=> 0 <= p i < n) /\
 (forall j, 0 <= j < n  => exists i, p i = j /\ 0 <= i < n) /\
 (forall i,  n <= i => p i = i).

op id : perm = fun x => x.
op inv (p : perm) : perm.
axiom inv_lemma p i j n : is_good p n => (p i = j <=> (inv p) j = i).

lemma inv_lemma1 p   n : is_good p n => ((inv p) \o p = id).
smt. qed.

lemma inv_lemma2 p n : is_good p n => (p \o (inv p) = id).
smt. qed.

lemma inv_lemma_e p n i : is_good p n => ((inv p (p i) = i)).
smt. qed.

lemma inv_lemma2_e p n i : is_good p n => (p (inv p i) = i).
smt. qed.

op pi (p : perm) (l : 'a list) : 'a list.

axiom pi_lemma  p (l : 'a list):  
    is_good p (size l)
 => forall i, nth witness l i = nth witness (pi p l) (p i).

axiom pi_size  p (l : 'a list) : size (pi p l) = size l.

op ip (p : perm) (l : 'a list) : 'a list = pi (inv p) l.
 


lemma id_lemma n :  is_good id n.
proof. progress;smt.
qed.


lemma invinj (p : perm) n : is_good p n => injective (inv p).
progress. smt.
qed.

lemma inv_good p n : is_good p n => is_good (inv p) n.
move => H. elim H.
progress.
have f1 : injective p. smt.
have f2 : injective (inv p). apply (invinj p n). auto.  
smt.
have f3 : 0 <= p (inv p i) < n. 
rewrite (inv_lemma2_e p n i _).  auto. auto.
smt.
have f3 : 0 <= p (inv p i) < n. 
rewrite (inv_lemma2_e p n i _).  auto. auto.
smt. 
have f3: p (inv p i) = i. apply (inv_lemma2_e p n i). auto. 
smt.
have f3: p (inv p i) = i. apply (inv_lemma2_e p n i). auto. 
smt.
exists (p j). split.
apply (inv_lemma_e p n). auto. smt. 
have ->: i = p i. smt.
rewrite (inv_lemma_e p n). auto. rewrite H2. auto. auto.
qed.


lemma invinv (p : perm) n : is_good p n => p = inv (inv p).
progress.
have  f : injective p. smt.
have  g : injective (inv p). smt.

have : p \o (inv p) = (inv (inv p)) \o  (inv p).
  have ->: p \o (inv p) = id.  smt.
rewrite  (inv_lemma1 (inv p)  n). apply inv_good. auto. auto.
smt.
qed.


lemma comp_lemma_1 (p1 p2 : perm) i j k :  
  p1 i = j =>
  p2 j = k =>
  (p2 \o p1) i = k .
progress. 
qed.


  
lemma comp_inv_1 p n : is_good p n =>  p \o (inv p) = id.
proof. elim. progress.
apply fun_ext. move => x.
rewrite   (inv_lemma2 p n). auto.
smt.
qed.

lemma comp_inv_2 p n : is_good p n =>  (inv p) \o p = id.
proof. elim. progress.
apply fun_ext. move => x.
rewrite   (inv_lemma1 p n). auto.
smt.
qed.

lemma comp_good p1 p2 n : is_good p1 n => 
 is_good p2 n => is_good (p2 \o p1) n.
move => h1 h2. progress.
smt. smt. smt.
smt. smt.
exists (inv p1 (inv p2 j)). split.
rewrite /(\o). smt. smt.
smt.
qed.



lemma comp_inv2 p1 p2 n : is_good p1 n => is_good p2 n => (inv p1) \o (inv p2) = inv (p2 \o p1).
proof. progress.
apply fun_ext.
move => x. 
pose x1 := ((inv p1) \o (inv p2)) x.
pose x2 := inv (p2 \o p1) x.
have f1 : (p2 \o p1) x1 = x.
rewrite /x1. rewrite /(\o) /comp /(\o). 
smt.
have f2 : (p2 \o p1) x2 = x.
rewrite /x2. 
+ have f3 : is_good (p2 \o p1) n. smt.
  smt.
smt.
qed.




lemma inv_comp p n : is_good p n => (inv p) \o p = id.
proof. smt. qed.
  


lemma pi_lemma_inv  p (l : 'a list):  
    is_good p (size l)
 => forall i, nth witness l (inv p i) = nth witness (pi p l) i.
progress. rewrite (pi_lemma p l). auto. smt.
qed.


lemma qqq  x (l : 'a list) p :  is_good p (size l) =>
  x \in l => x \in (pi p l).
progress.
have f1 : nth witness l (index x l) = x. smt.
have f2 : 0 <= (index x l) < size l. smt.
have : nth witness (pi p l) (p (index x l)) = x.
rewrite - f1. smt.
smt.
qed.


lemma pi_index x (l : 'a list) p :  is_good p (size l) =>
  x \in l =>
  index x (pi p l) < size l.
smt.
qed.


lemma ext_list_eq' (l1 l2 : 'a list) : 
  size l1 = size l2 =>
  (forall i, 0 <= i < (size l1) 
     => nth witness l1 i = nth witness l2 i) 
=> l1 = l2.
proof.
progress.
apply (eq_from_nth witness). auto. smt.
qed.


lemma pi_lemma_id  (l : 'a list) : pi id l = l.
apply ext_list_eq'. smt.
progress. rewrite - (pi_lemma_inv). smt. 
smt.
qed.


  
lemma pi_comp (p1 p2 : perm) (l : 'a list) : 
  is_good p1 (size l) =>
  is_good p2 (size l) =>
  pi p2 (pi p1 l) = pi (p2 \o p1) l.
proof. progress.
apply ext_list_eq'.
progress. smt. progress.
have ->: nth witness (pi (p2 \o p1) l) i
 = nth witness l (inv (p2 \o p1) i).
rewrite pi_lemma_inv.
smt. auto.
have ->: nth witness (pi p2 (pi p1 l)) i
 = nth witness (pi p1 l) (inv p2 i).
rewrite pi_lemma_inv.
smt. auto.
have ->: nth witness (pi p1 l) (inv p2 i)
 = nth witness l (inv p1 (inv p2 i)).
rewrite pi_lemma_inv.
smt. auto.
smt.
smt (comp_inv2).
qed.


lemma ippi p (l : 'a list): 
  is_good p (size l) =>
  ip p (pi p l) = l.
move => g.
rewrite /ip. rewrite  (pi_comp  p (inv p) l). auto.
smt.
rewrite (comp_inv_2 p (size l)). auto. smt.
qed.


lemma ppp  x (l : 'a list) p :  is_good p (size l) =>
  x \in (pi p l) => x \in l.
progress.
have f1 : nth witness (pi p l) (index x (pi p l)) = x. smt.
have f2 : 0 <= (index x (pi p l)) < size l. smt.
have : nth witness l ((index x l)) = x.
rewrite - f1. smt.
progress.
have f3 : 0 <= (index x l) < size l. 
split. smt.
progress.  
have : index x (pi (inv p) (pi p l)) < size (pi p l).
smt.
have ->: (pi (inv p) (pi p l)) = l. 
smt. smt. smt.
qed.


lemma count_lemma_o x : forall (l : 'a list) i,
  x \in l =>
  nth witness l i = x =>
 (forall j, 0 <= j < size l => nth witness l j = x => i = j)
 => exists l1 l2, l = l1 ++ x :: l2 /\ !(x \in l1) /\ ! (x \in l2).
elim. smt.
move => x0 l ih i xin xeq z.
case (x = x0). 
progress.
exists [] l. split.  smt. split. smt.
case (x0 \in l).
move => ass. simplify.
have : 0 <= index x0 l < size l. smt.
move => [p1 p2].
have zz : i = 0.
apply z. smt. smt.
have f : nth witness (x0 :: l) (1 + index x0 l) = x0.
smt.
have : i = 1 + (index x0 l).
apply z. smt. auto. smt.
auto.
progress.
have q : exists (l1 l2 : 'a list),
        l = l1 ++ x :: l2 /\ ! (x \in l1) /\ ! (x \in l2).
apply (ih (i - 1)).  smt.
smt. progress. smt.
elim q.
progress. exists (x0 :: l1) (l2). split. smt.
smt.
qed.


lemma count_lemma i (l : 'a list) x : 
 0 <= i <= size l =>
 nth witness l i = x =>
  x \in l =>
 (forall j, 0 <= j < size l => nth witness l j = x => i = j)
 => count (pred1 x) l = 1.
move => p1 p2 p3 p4.
have f : exists l1 l2, l = l1 ++ x :: l2 /\ !(x \in l1) /\ ! (x \in l2).
smt(count_lemma_o).
elim f. progress.
smt.
qed.


lemma pi_uniq  p (l : 'a list):  
    is_good p (size l)
 => uniq l => uniq (pi p l).
proof. progress.
apply (count_mem_uniq (pi p l) _) .
progress.
have f : count (pred1 x) l = b2i (x \in l).
apply count_uniq_mem. auto.
have ->: b2i (x \in pi p l) = b2i (x \in l).
smt.
have <-: count (pred1 x) l = count (pred1 x) (pi p l).
case (x \in l).
progress.
have f2 : exists i, 0 <= i < (size l) /\ nth witness l i = x.
exists (index x l). smt.
elim f2. move => i [p1 p2].
have f3 : forall j, 0 <= j < (size l) => nth witness l j = x => j = i
. timeout 20. smt.
have : count (pred1 x) l = 1. smt.
progress. rewrite H2. clear H2.
have  z : nth witness (pi p l) (p i) = x. smt.
have f4 : forall j, 0 <= j < (size (pi p l)) => nth witness (pi p l) j = x => j = (p i).
progress. 
have f6 : (inv p j) = i.
apply f3. 
have f9 : j < size l. smt.
timeout 30. clear f H1 p2 f3. smt.
smt. clear  z f3 p2 H1 f  H3 H2 .  smt.
have f7 :  0 <= (p i) && (p i) < size l. smt.
have ->: count (pred1 x) (pi p l) = 1. 
apply (count_lemma (p i) (pi p l) x).  split.  smt. progress.   smt.
smt. smt.  auto. smt. auto.
progress.
have ->: count (pred1 x) l = 0. smt.
have ff : ! (x \in (pi p l)). 
smt. smt.
auto.
qed.

lemma piip p (l : 'a list) : is_good p (size l) => pi p (ip p l) = l.
move => g.
rewrite /ip.
rewrite /ip. rewrite  (pi_comp  (inv p) p l). smt.
auto.
smt.
qed.


lemma pi_perm_uniq ['a] p (l : 'a list) : is_good p (size l) =>
  uniq l =>
   perm_eq l (pi p l).
progress.
apply (uniq_perm_eq l (pi p l)). trivial. smt.
progress.
have  f: has (pred1 x) l. smt.
have  g : (exists (i : int), (0 <= i && i < size l) /\ (pred1 x) (nth witness l i)).
apply (has_nthP (pred1 x)).    auto.
elim g. progress.
rewrite /pred1  in H4.
rewrite - H4.
rewrite (pi_lemma p l H).
smt.
have  g : (exists (i : int), (0 <= i && i < size (pi p l)) /\ (pred1 x) (nth witness (pi p l) i)).
apply (has_nthP (pred1 x)).    smt.
elim g. progress.
rewrite /pred1  in H4.
rewrite - H4.
rewrite - (pi_lemma_inv p l H).
smt. 
qed.


lemma nthzip' i : forall (l1 : 'a list) (l2 : 'b list),
 size l1 = size l2 =>
 0 <= i < size l1 =>
  nth witness (zip l1 l2) i 
     = ((nth witness l1 i), (nth witness l2 i)).
elim. smt. 
move => x l h. elim.
smt.
progress.
smt.
qed.


lemma nthmap i (f : 'a -> 'b) : forall (l : 'a list),
 0 <= i < size l =>
  nth witness (map f l) i 
     =   f (nth witness l i) .
smt.
qed.

lemma nth_zip (l1 : 'a list)(l2 : 'b list)  i:  size l1 = size l2 =>
  0 <= i < size l1 =>
  fst (nth witness (zip l1 l2) i) = nth witness l1 i.
progress.
rewrite - (nthmap i fst (zip l1 l2)). smt. 
smt.
qed.

lemma pi_zip p (l : 'a list) : is_good p (size l) => 
   (unzip1 (pi p (zip l (range 0 (size l)))))
 = pi p l.
progress. apply ext_list_eq'.  smt.
progress.
have ->: nth witness (unzip1 (pi p (zip l (range 0 (size l))))) i =
 fst (nth witness ((pi p (zip l (range 0 (size l))))) i).
smt.
rewrite - (pi_lemma_inv p l _) . auto.
rewrite - (pi_lemma_inv p (zip l (range 0 (size l))) _) . smt.
apply (nth_zip l (range 0 (size l))).
smt.  smt.
qed.


lemma pi_perm ['a] p (l : 'a list) : is_good p (size l) =>
   perm_eq l (pi p l).
progress.
have f :  perm_eq (zip l (range 0 (size l))) (pi p (zip l (range 0 (size l)))).
apply pi_perm_uniq.
smt.
smt.
have f' : 
 perm_eq (unzip1 (zip l (range 0 (size l)))) (unzip1 (pi p (zip l (range 0 (size l))))).
smt.
have g : (unzip1 (zip l (range 0 (size l)))) = l.
rewrite unzip1_zip. smt. auto.
rewrite - g.
have ->: (pi p (unzip1 (zip l (range 0 (size l))))) = pi p l.
rewrite unzip1_zip. smt. auto.
have <- : (unzip1 (pi p (zip l (range 0 (size l)))))
 = pi p l.
rewrite pi_zip. auto. auto.
auto.
qed.


lemma ip_perm ['a] p (l : 'a list) : 
   is_good p (size l) => perm_eq l (ip p l).
smt.
qed.

lemma map_pi ['a, 'b] p (f : 'a -> 'b) (l : 'a list)  
   :  is_good p (size l) => 
   map f (pi p l) = pi p (map f l).
progress.
apply ext_list_eq'. smt.
progress.
rewrite -  (pi_lemma_inv p (map f l) _ i).  smt.
have ->: nth witness (map f (pi p l)) i
 = f (nth witness ((pi p l)) i).
apply nthmap. smt.
rewrite nthmap. smt. 
rewrite - (pi_lemma_inv p). smt.
auto.
qed.



lemma zip_pi ['a 'b] p (l1: 'a list) (l2 : 'b list)
   : is_good p (size l1) => size l1 = size l2 =>
   pi p (zip l1 l2) = zip (pi p l1) (pi p l2).
progress. apply ext_list_eq'.  smt.
progress.
rewrite nthzip'. smt. smt.
rewrite - pi_lemma_inv. smt. 
rewrite - pi_lemma_inv. smt.
rewrite - pi_lemma_inv. smt. 
apply nthzip'. smt. smt.
qed.

lemma zip_ip ['a 'b] p (l1: 'a list) (l2 : 'b list)
   : is_good p (size l1) => size l1 = size l2 =>
   ip p (zip l1 l2) = zip (ip p l1) (ip p l2).
smt.
qed.
    
