pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux FSet.

require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.

require import Permutation.

type a, b.

op d : a -> b distr.

   
lemma zippi ['a, 'b] p (l1: 'a list) (l2 : 'b list)
   : is_good p => perm_eq (zip (pi p l1) l2) (zip l1 (ip p l2)).
proof. smt. qed.


op merge ['a] = (fun (xs : 'a list * 'a list) => xs.`1 ++ xs.`2).
op splitf ['a] (n : int) = (fun (l : 'a list) => (take n l, drop n l)).


module DJM = {

  proc main1(l1 : a list, l2 : a list) = {
    var x1, x2;
    x1 <$ djoinmap d l1;
    x2 <$ djoinmap d l2;
    return (x1, x2);
  }


  proc main2(l1 : a list, l2 : a list) = {
    var x;
    x <$ (djoinmap d l1 `*` djoinmap d l2);
    return x;
  }


  proc main3(l1 : a list, l2 : a list) = {
    var x;
    x <$ dmap (djoinmap d l1 `*` djoinmap d l2) merge;
    return x;
  }

  proc main4(l1 : a list, l2 : a list) = {
    var x;
    x <$ djoinmap d (l1 ++ l2) ;
    return x;
  }

  proc main5(l : a list) = {
    var x;
    x <$ djoinmap d l ;
    return x;
  }
  
}.


lemma main12 : equiv [ DJM.main1 ~ DJM.main2 : ={arg} ==> ={res} ].
admitted.


lemma main23 : equiv [ DJM.main3 ~ DJM.main2 : ={arg} ==> res{1} = merge res{2} ].
proc.
exists* l1{1}, l2{1}. 
elim*. progress.

rnd (fun l => (take (size l1_L) l, drop (size l1_L) l  )) merge.
skip. progress.
admit.
have ->: mu1 (dmap (djoinmap d l1{2} `*` djoinmap d l2{2}) merge) (merge xR)
 = mu1 ( (djoinmap d l1{2} `*` djoinmap d l2{2})) (splitf (size l1{1}) (merge xR)).
print    dmap1E_can.

rewrite - (dmap1E_can _ merge (splitf (size l1{1}))).
rewrite /cancel. admit.
admit.
auto. 
admit.
admit.
admit.
qed.


lemma main34 : equiv [ DJM.main4 ~ DJM.main3 : ={arg} ==> ={res} ].
proc.
rnd.  skip. progress.
rewrite - djoin_cat.
simplify.
smt.
rewrite - djoin_cat.
smt.
qed.



lemma djoin_pi ['a]  p (ds: 'a distr list) (xs : 'a list)
   : is_good p => size ds = size xs => mu1 (djoin (pi p ds)) xs  = mu1 (djoin ds) (ip p xs).
proof. rewrite djoin1E.
rewrite djoin1E.
progress. rewrite size_pi. rewrite H. simplify.
rewrite size_ip. auto. rewrite H0. simplify. 
apply eq_big_perm.
apply zippi. auto.
qed.

lemma djm_main14 : equiv [ DJM.main1 ~ DJM.main4 : ={arg} ==> merge res{1} = res{2} ].
proc.
admitted.


lemma main5perm  p : 
  equiv [ DJM.main5 ~ DJM.main5 : (pi p arg{1}) = (arg{2}) 
   ==> (res{1}) = (ip p res{2}) ]. progress.
admitted.

lemma djm_main51 p : equiv [ DJM.main5 ~ DJM.main1 : (pi p  (arg{1})) = (merge arg{2}) ==> res{1} = (ip p (merge res{2})) ].
proc.
admitted.


lemma djm_main511 p : equiv [ DJM.main5 ~ DJM.main1 : (ip p  (arg{1})) = (merge arg{2}) ==> res{1} = (pi p (merge res{2})) ].
proc.
admitted.


(* proc. *)
(* rnd (pi p) (ip p).  skip. progress. smt.  *)
(* rewrite map_pi. auto. rewrite  djoin_pi. smt. smt. reflexivity. *)
(* smt. *)
(* smt.    *)
(* qed. *)




    

 
