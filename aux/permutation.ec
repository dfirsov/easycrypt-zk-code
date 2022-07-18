pragma Goals:printall.
require import AllCore List Distr  .


type permutation = int -> int.

op compose : permutation -> permutation -> permutation 
  = (\o).
op inv : permutation -> permutation.


op perm_d : int -> permutation distr.

axiom inv_prop1 p n :  p \in perm_d n => p \o (inv p) = (fun x => x).
axiom inv_prop2 p n :  p \in perm_d n => (inv p) \o p = (fun x => x). 

op mk_perm_list_fun : int list -> permutation.


axiom perm_d_uni n : is_uniform (perm_d n).
axiom perm_d_in1 p n w : p \in perm_d n => p \o ((mk_perm_list_fun w)) \in perm_d n.
axiom perm_d_in2 p n w : p \in perm_d n => p \o (inv (mk_perm_list_fun w)) \in perm_d n.
axiom perm_d_in3 n p : p \in perm_d n => perm_eq (map p  (range 0 n)) (range 0 n).
axiom invop p : perm_eq p (range 0 (size p)) => map (inv (mk_perm_list_fun p)) p = range 0 (size p).

axiom perm_d_in4 p n :  perm_eq p (range 0 n) =>
  (mk_perm_list_fun p) \in perm_d n.

axiom perm_d_lossless : forall x, is_lossless (perm_d x).

