require import AllCore List Distr.

type permutation = int -> int.

op compose : permutation -> permutation -> permutation = (\o).

op inv : permutation -> permutation.
op mk_perm : int list -> permutation.
op perm_d : int -> permutation distr.

axiom perm_d_uni n : is_uniform (perm_d n).
axiom perm_d_lossless n : is_lossless (perm_d n).

axiom perm_d_in0 p n : p \in perm_d n => (inv p) \in perm_d n.
axiom perm_d_comp p q n : p \in perm_d n => q \in perm_d n =>  p \o q \in perm_d n.
axiom perm_d_in4 p n :  perm_eq p (range 0 n) => (mk_perm p) \in perm_d n.
axiom perm_d_in3 n p : p \in perm_d n => perm_eq (map p  (range 0 n)) (range 0 n).

axiom inv_prop1 p n :  p \in perm_d n => p \o (inv p) = (fun x => x).
axiom inv_prop2 p n :  p \in perm_d n => (inv p) \o p = (fun x => x). 
axiom inv_prop3 p : perm_eq p (range 0 (size p)) => map (inv (mk_perm p)) p = range 0 (size p).
