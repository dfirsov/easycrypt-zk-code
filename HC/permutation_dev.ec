pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux FSet.

require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.

print perm_eq.

(* 
   Open : Commitment * Opening -> Maybe Edge   
   Com  : Edge -> Commitment * Opening

edge : int * int * bool

graph : edge fset
graph : bool list list

hc_com : edge commitment fset
hc_com : bit commitment list list


Prover(Dominique): 
- for i,j<-[n]: C[i,j],O[i,j] := Com(G[pi(i),pi(j)])
- Send C
- Wait for i
- If i=0: send pi, O
- If i=1: for each (i,j) <- pi(w): send (i,j), O[i,j]



Prover(Denis):
- C = {} :: fset
- O = {} :: fmap
- for (i,j,b)<-pi(G) where b=1: c,o := Com(i,j,b); C += c; O(c) := o
- Send C
- Wait for i
- If i=0: send pi, O
- If i=1: for each (i,j) <- pi(w): find corresponding c. Send O(c's).

Comments:
  - if hc_com = (bit commitment * int * int) fset, then everytingh works.




*)


  (* 


typedef permutation = "{(n,f) | n f. 
    bij_betw f {<n} {<n} /\ f = 0 on {>=n}}"

define len_perm = ...

define app_perm :: perm => nat=>nat  = ...


typedef permutation = (n,f::nat=>nat).

definition is_good (n,f) = bij_betw f ......

OR

inductive is_good     (nice: extensional)
  is_good (swap i j)
  is_good f ==> is_good (swap i j o f)


----

type permutation = f :: nat => nat

is_good :: nat => permutation => bool


 *)

(*
idea : 
 
1/ type swap = int * int

swap (i,j) means that we want to swap the element at position
i with element at position j.

2/ permutation = swap list

3/ is_good p := all indices in p are within 1 and (length p)

4/ apply_swap : swap -> 'a list

5/   apply_swap s (l1 ++ l2) = l3 ++ l4
  => apply_swap (adjust_indices s) (l1 ++ x :: l2) = l3 ++ x :: l4

6/ apply_perm p (l1 ++ l2) = l3 ++ l4
  => apply_perm (adjust_indices p) (l1 ++ x :: l2) = l3 ++ x :: l4

7/ implement and prove

   perm_rev : permutation -> permutation

   apply_perm p l1 = l2
   apply_perm (perm_rev p) l2 = l1

8/ implement and prove

   mk_perm : 'a list  -> 'a list -> permutation

   apply_perm (mk_perm l1 l2) l1 = l2


axiom map_pi ['a, 'b] p (f : 'a -> 'b)  (l : 'a list)
   : is_good p => map f (pi p l) = pi p (map f l).
  


*)

type Swap = int * int.
print List.

op app_swap ['a] (s : Swap) (l : 'a list) : 'a list.

lemma app_swap_p ['a] i j (l1 l2 : 'a list) l3 x y 
  :  size l1 = i => size (l1 ++ [x] ++ l2) = j 
      => app_swap (i,j) (l1 ++ [x] ++ l2 ++ [y] ++ l3)
         = (l1 ++ [y] ++ l2 ++ [x] ++ l3).
