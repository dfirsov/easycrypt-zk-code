pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux FSet.

require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.

type permutation = int -> int.

op compose : permutation -> permutation -> permutation 
  = (\o).
op inv : permutation -> permutation.

axiom inv_prop1 p :  p \o (inv p) = (fun x => x).
axiom inv_prop2 p :  (inv p) \o p = (fun x => x).
axiom inv_prop3 p :  (inv (inv p)) = p.


op is_good : permutation -> bool.

op pi ['a] : permutation -> 'a list -> 'a list.
op ip ['a] : permutation -> 'a list -> 'a list.

axiom pi_perm ['a] p (l : 'a list) :  perm_eq l (pi p l).
axiom ip_perm ['a] p (l : 'a list) : perm_eq l (ip p l).

axiom ippi ['a] p : forall (l : 'a list), ip p (pi p l) = l.
axiom piip ['a] p : forall (l : 'a list), pi p (ip p l) = l.

axiom map_pi ['a, 'b] p (f : 'a -> 'b)  (l : 'a list)
   : map f (pi p l) = pi p (map f l).


axiom map_ip ['a, 'b] p (f : 'a -> 'b)  (l : 'a list)
   : map f (ip p l) = ip p (map f l).


axiom zip_pi ['a 'b] p (l1: 'a list) (l2 : 'b list)
   :  pi p (zip l1 l2) = zip (pi p l1) (pi p l2).

axiom zip_ip ['a 'b] p (l1: 'a list) (l2 : 'b list)
   : ip p (zip l1 l2) = zip (ip p l1) (ip p l2).

axiom size_pi ['a] p (l : 'a list) :  size (pi p l) = size l.
axiom size_ip ['a] p (l: 'a list) : size (ip p l) = size l.


op mk_perm ['a] : 'a list -> 'a list -> permutation.

op mk_perm_list_fun : int list -> permutation.


axiom mk_perm_good ['a] (l1 l2 : 'a list) : perm_eq l1 l2 
   => is_good (mk_perm l1 l2).

axiom mk_perm_pi ['a] (l1 l2 : 'a list) : perm_eq l1 l2
   => pi (mk_perm l1 l2) l1 = l2.

axiom mk_perm_ip ['a] (l1 l2 : 'a list) : perm_eq l1 l2 
   => ip (mk_perm l1 l2) l2 = l1.


op perm_d : int -> permutation distr.
axiom perm_d_uni n : is_uniform (perm_d n).
axiom perm_d_in1 p n w : p \in perm_d n => p \o ((mk_perm_list_fun w)) \in perm_d n.
axiom perm_d_in2 p n w : p \in perm_d n => p \o (inv (mk_perm_list_fun w)) \in perm_d n.
axiom perm_d_in3 n p : p \in perm_d n => perm_eq (map p  (range 0 n)) (range 0 n).


axiom invop p : map (mk_perm_list_fun p) p = range 0 (size p).
