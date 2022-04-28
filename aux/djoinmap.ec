pragma Goals:printall.
require import AllCore DBool Bool List Distr Int IntDiv Aux FSet.

require import AllCore Distr FSet StdRing StdOrder StdBigop List.
(*---*) import RField RealOrder Bigreal BRA.
import BRM.

require import Permutation.

type a, b.

op d : a -> b distr.
   
lemma zippi ['a, 'b] p (l1: 'a list) (l2 : 'b list)
   :  perm_eq (zip (pi p l1) l2) (zip l1 (ip p l2)).
proof. smt. qed.

lemma zipip ['a, 'b] p (l1: 'a list) (l2 : 'b list)
   :  perm_eq (zip (ip p l1) l2) (zip l1 (pi p l2)).
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
    x <$ djoinmap d l1 `*` djoinmap d l2;
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

require import DProd.
clone import ProdSampling with type t1 <- b list,
                               type t2 <- b list.

lemma main12 : equiv [ DJM.main1 ~ DJM.main2 : ={arg} ==> ={res} ].
transitivity S.sample2 (arg{2} = (djoinmap d arg{1}.`1, djoinmap d arg{1}.`2) ==> ={res}) (arg{1} = (djoinmap d arg{2}.`1, djoinmap d arg{2}.`2) ==> ={res}).
progress. smt. auto.
proc. rnd. rnd. skip. progress.
symmetry.
transitivity S.sample (arg{2} = (djoinmap d arg{1}.`1, djoinmap d arg{1}.`2) ==> ={res}) (={arg} ==> ={res}).
progress. smt. auto.
proc. rnd. skip. progress.
conseq sample_sample2. auto.
qed.


lemma main23 : equiv [ DJM.main3 ~ DJM.main2 : ={arg} ==> res{1} = merge res{2} ].
proc.
exists* l1{1}, l2{1}. 
elim*. progress.
rnd (fun l => (take (size l1_L) l, drop (size l1_L) l)) merge.
skip. 
progress. 
have f1 : xR.`1 \in djoinmap d l1{2}. smt.
have f2 : xR.`2 \in djoinmap d l2{2}. smt.
have f3 : size xR.`1 = size l1{2}. smt.
have f4 : size xR.`2 = size l2{2}. smt.
rewrite /merge.
rewrite - f3. smt.
have ->: mu1 (dmap (djoinmap d l1{2} `*` djoinmap d l2{2}) merge) (merge xR)
 = mu1 ( (djoinmap d l1{2} `*` djoinmap d l2{2})) (splitf (size l1{2}) (merge xR)).
rewrite - (dmap1E_can _ merge (splitf (size l1{2}))).
rewrite /cancel.
rewrite /merge /splitf. smt.
rewrite /merge /splitf. 
progress.
have f1 : a.`1 \in djoinmap d l1{2}. smt.
have f2 : a.`2 \in djoinmap d l2{2}. smt.
have f3 : size a.`1 = size l1{2}. smt.
have f4 : size a.`2 = size l2{2}. smt.
rewrite - f3. smt. auto.
have f1 : xR.`1 \in djoinmap d l1{2}. smt.
have f2 : xR.`2 \in djoinmap d l2{2}. smt.
have f3 : size xR.`1 = size l1{2}. smt.
have f4 : size xR.`2 = size l2{2}. smt.
rewrite /merge.
rewrite - f3. smt.
search dmap.
have f : exists (a : b list * b list), (a \in djoinmap d l1{2} `*` djoinmap d l2{2}) /\ xL = merge a.
apply supp_dmap. auto.
elim f. progress.
smt.
smt.
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




lemma djm_main14 : equiv [ DJM.main1 ~ DJM.main4 : ={arg} ==> 
  merge res{1} = res{2} ].
transitivity DJM.main2 (={arg} ==> ={res}) (={arg} ==> merge res{1} = res{2}). 
smt. auto. conseq main12. 
transitivity DJM.main3 (={arg} ==> merge res{1} = res{2} ) (={arg} ==> ={res}). 
smt. auto. symmetry. conseq main23.  auto. auto.
symmetry. conseq main34. auto. auto.
qed.


lemma djoin_pi ['a]  p (ds: 'a distr list) (xs : 'a list)
   : size ds = size xs => mu1 (djoin (pi p ds)) xs  = mu1 (djoin ds) (ip p xs).
proof. rewrite djoin1E.
rewrite djoin1E.
progress. rewrite size_pi. rewrite H. simplify.
rewrite size_ip. auto.  simplify. 
apply eq_big_perm.
apply zippi. 
qed.


    
lemma main5perm  p : 
  equiv [ DJM.main5 ~ DJM.main5 : (pi p arg{1}) = (arg{2}) 
   ==> (res{1}) = (ip p res{2}) ]. progress.
proc.
rnd (pi p) (ip p).  skip. progress. smt.
rewrite map_pi. auto. rewrite  djoin_pi. smt. smt. smt. 
smt.
qed.


lemma djoin_pi2 ['a]  p (ds: 'a distr list) (xs : 'a list)
   : size ds = size xs => mu1 (djoin (ip p ds)) xs  = mu1 (djoin ds) (pi p xs).
proof. rewrite djoin1E.
rewrite djoin1E.
progress. rewrite size_pi. rewrite H. simplify.
rewrite size_ip. auto.  simplify. 
rewrite H. simplify. 
apply  eq_big_perm.
apply zipip. 
qed.




lemma djm_main54 p x : equiv [ DJM.main5 ~ DJM.main4 : (ip p  (arg{1})) = (merge arg{2}) /\ x = arg{2} ==> res{1} = (pi p ( res{2}))  
   ].
proc. 
rnd (ip p) (pi p). skip.  progress. smt.
rewrite  /merge in H. rewrite - H.
rewrite -   djoin_pi2. smt.
rewrite map_ip. auto. smt.
smt.
qed.


lemma djm_main51 p x : equiv [ DJM.main5 ~ DJM.main1 : (ip p  (arg{1})) = (merge arg{2}) /\ x = arg{2} ==> res{1} = (pi p (merge res{2})) ].
transitivity DJM.main4 ((ip p  (arg{1})) = (merge arg{2}) /\ x = arg{2} ==> res{1} = (pi p ( res{2}))) ( ={arg} ==> 
  merge res{2} = res{1} ).
smt. smt.
conseq (djm_main54 p x).
symmetry.
conseq (djm_main14). auto.
qed.    


lemma djm_main511 p x : equiv [ DJM.main5 ~ DJM.main1 : (ip p  (arg{1})) = (merge arg{2}) /\ x = arg{2} ==> res{1} = (pi p (merge res{2}))
  /\ size (fst x) = size res{2}.`1 ].
proc*. 
transitivity{2} {r <- DJM.main1(x);} ((ip p  (arg{1})) = (merge arg{2}) /\ x = arg{2} ==> r{1} = (pi p (merge r{2}))) (={arg} /\ arg{1} = x ==> ={r} /\ size (fst x) = size r{1}.`1).  smt. progress.
call (djm_main51 p x). skip. auto.
inline*.  wp. rnd. rnd. wp. skip. progress.
smt.
qed.






    

 
