pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux FSet.

require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.



type permutation.

op is_good : permutation -> bool.

op pi ['a] : permutation -> 'a list -> 'a list.
op ip ['a] : permutation -> 'a list -> 'a list.

op pn : permutation -> int -> int.
op np : permutation -> int -> int.

op compose : permutation -> permutation -> permutation.
op inv : permutation -> permutation.



axiom pi_perm ['a] p (l : 'a list) :  perm_eq l (pi p l).
axiom ip_perm ['a] p (l : 'a list) : perm_eq l (ip p l).
axiom ippi ['a] p : forall (l : 'a list), ip p (pi p l) = l.
axiom piip ['a] p : forall (l : 'a list), pi p (ip p l) = l.

axiom map_pi ['a, 'b] p (f : 'a -> 'b)  (l : 'a list)
   : map f (pi p l) = pi p (map f l).

axiom zip_pi ['a 'b] p (l1: 'a list) (l2 : 'b list)
   :  pi p (zip l1 l2) = zip (pi p l1) (pi p l2).

axiom zip_ip ['a 'b] p (l1: 'a list) (l2 : 'b list)
   : is_good p => ip p (zip l1 l2) = zip (ip p l1) (ip p l2).
axiom size_pi ['a] p (l : 'a list)
   : is_good p => size (pi p l) = size l.
axiom size_ip ['a] p (l: 'a list)
   : is_good p => size (ip p l) = size l.


op mk_perm ['a] : 'a list -> 'a list -> permutation.

op mk_perm_list_fun : int list -> int list -> permutation.

op mk_perm_fun : (int -> int) -> permutation.

axiom mk_perm_good ['a] (l1 l2 : 'a list) : perm_eq l1 l2 
   => is_good (mk_perm l1 l2).

axiom mk_perm_pi ['a] (l1 l2 : 'a list) : perm_eq l1 l2
   => pi (mk_perm l1 l2) l1 = l2.

axiom mk_perm_ip ['a] (l1 l2 : 'a list) : perm_eq l1 l2 
   => ip (mk_perm l1 l2) l2 = l1.
