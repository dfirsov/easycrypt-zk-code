pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import Aux Permutation Blum_Basics.


section.
local lemma phase1_1 ['a 'b] p (l1 : 'a list) (l2 : 'b list) perm : 
 all p (zip l1 l2)
  =  all p (zip (ip perm l1) (ip perm l2)).
rewrite - zip_ip.
rewrite allP.
rewrite allP.
smt.
qed.


local lemma phase1 ['a 'b] ver (l1 : 'a list) (l2 : 'b list) perm n : 
 all ver (zip l1 l2)
  =>  all ver (zip (take n (ip perm l1)) (take n (ip perm l2))).
progress.
rewrite - (phase1_3 (ip perm l1) (ip perm l2) n).
rewrite phase1_2.
rewrite - phase1_1.    
apply H.
qed.
    

local lemma is_hc_perm_2  (g : graph) (w : hc_wit) :
  !IsHC ((g),w) /\
     K = size w /\ 
     K * K = size g /\ 
     perm_eq w (range 0 K)
  => false \in prj_path w g  .
progress.

  have : nseq (size w) true <> prj_path w g. smt.
progress.
have f : size (prj_path w g) = size w. rewrite lemma1. smt. auto.
apply (aux_lem (prj_path w g)  (size w)).
auto. auto.
qed.

    
local lemma phase2  (g : graph) (w : hc_wit) :
  !IsHC (g,w) /\
     K = size w /\ 
     K * K = size g /\ 
     perm_eq w (range 0 K) =>
   false \in (prj_path w g).
smt (is_hc_perm_2).
qed.


local lemma quasi_fin ['a] (l' : bool list) n (l X : 'a list) ver : 
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




lemma fin_bind_real   (w : hc_wit) (g : graph)  c o1 (p : permutation) X: 
   !IsHC ((g), permute_witness (inv p) w) =>  
   hc_verify (g) c true  (Left (p,o1)) =>
   hc_verify (g) c false (Right (w,X)) 
  => Ver (true,  nth witness ( (zip (prj_path w c)
                             X)) (index false ( (prj_path  w  (permute_graph p g))))) /\
     Ver (false, nth witness ( (zip (prj_path  w c)
                             (prj_path w o1))) (index false ( (prj_path w (permute_graph p g))))).
proof.  
move => p0 p1 p2 .
apply (quasi_fin (prj_path w (permute_graph p g)) K) .
apply (is_hc_perm_2 ).
progress. 
print permute_graph_prop3.
case (IsHC (( permute_graph p g), w)).
move => q. 
apply p0. 
have -> : g = permute_graph (inv p) (permute_graph p g). rewrite permute_graph_prop4. auto.
rewrite - (permute_graph_prop3  (permute_graph p g) (inv p) w ). rewrite q. auto.
elim p2. smt.
rewrite permute_graph_prop2.
elim p1. smt.
elim p2. smt.
smt.
elim p1. progress. 
rewrite lemma8. rewrite lemma8.
apply allP. progress.
have f : x \in (zip (permute_graph p g) (zip c o1)). smt.
apply (allP Ver ( zip (permute_graph p g) (zip c o1))). auto. auto.
have f1 : K <= size (permute_graph p g). elim p1. smt.
have f2 : K = size w. elim p2. smt.
smt (lemma1).
have f1 : size (prj_path w c) = K. elim p1.  elim p2. progress.
rewrite lemma1. smt. auto.
have f2 : size (prj_path w o1) = K. elim p1.  elim p2. progress.
smt. smt.
elim p2. progress. smt.
qed.


end section.



op my_extract (p : hc_prob) (c : hc_com)   (r1 r2 : hc_resp) : int list  =
 with r1 = Left  x, r2 = Right z => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                                     permute_witness (inv p) w
 with r1 = Right z, r2 = Left  x => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                                     permute_witness (inv p) w
 with r1 = Left  x, r2 = Left  z => witness
 with r1 = Right x, r2 = Right z => witness.

op special_soundness_extract (p : hc_prob) (r1 r2 : transcript) : int list = 
 my_extract p r1.`1  r1.`3 r2.`3.

clone include SpecialSoundnessTheory  with  
  op special_soundness_extract <- special_soundness_extract.



op hc_verify1 (p : hc_prob) (c : hc_com)   (r1 r2 : hc_resp) : (bool * (commitment * opening)) * (bool * (commitment * opening))  =
 with r1 = Left  x, r2 = Right z => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
   ((true,  nth witness ((zip (prj_path w c)
                             X)) (index false ( (prj_path (w) (permute_graph p g))))), 
                                 (false, nth witness ( (zip (prj_path w c)
                             (prj_path w o1))) (index false ( (prj_path (w) (permute_graph p g))))))
 with r1 = Right z, r2 = Left  x => let n = K in let g = p  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                            ((true,  nth witness ( (zip (prj_path w c)
                             X)) (index false ( (prj_path ( w) (permute_graph p g))))), 
                                 (false, nth witness ( (zip (prj_path w c)
                             (prj_path w o1))) (index false ( (prj_path ( w) (permute_graph p g))))))
 with r1 = Left  x, r2 = Left  z => ((witness, witness), (witness, witness))
 with r1 = Right x, r2 = Right z => ((witness, witness), (witness, witness)).

 
module SpecialSoundnessAdvReduction (A : SpecialSoundnessAdversary)  = {
  proc run(statement : hc_prob) : bool = {
      var r1,r2,g,p1,p2;
      (r1, r2) <@ A.attack(statement);
      g    <- statement;
      (p1, p2) <- hc_verify1 (g) r1.`1  r1.`3 r2.`3 ;
      return (Ver p1 /\ Ver p2) /\ p1.`1 <> p2.`1 /\ p1.`2.`1 = p2.`2.`1;
  }
}.


timeout 10.
lemma computational_special_soundness:
      forall (s : hc_prob) &m
        (SpecialSoundnessAdversary <: SpecialSoundnessAdversary),
        let attack_prob =
          Pr[SpecialSoundnessAdversary.attack(s) @ &m :
             valid_transcript_pair s res.`1 res.`2 /\
             ! IsHC
                 (s, special_soundness_extract s res.`1 res.`2)] in
        let red_prob =
          Pr[SpecialSoundnessAdvReduction(SpecialSoundnessAdversary).run
             (s) @ &m : res] in
        attack_prob <= red_prob.
proof.  simplify.
progress.
byequiv;auto.
proc*.
inline*. wp.
call (_:true). wp. simplify.
skip.  move => &1  &2 h1. 
split. smt.  
move => h2. move => result_L result_R L1 l2 l3.  elim.
have ->:  statement{2} = s. smt.
clear h1 h2.  elim l3.
move => e1 e2. rewrite e1.  clear e2 e1 l2 L1 result_L.
elim.
case (result_R.`1.`2).
rewrite /special_soundness_extract.
elim result_R.`1.`3.
elim result_R.`2.`3. progress. 
smt. smt. smt. smt.
move => x p1 p2 p3 p4.
simplify. move => p5.
have : K <= size (prj_path x.`1 p1.`2). 
elim p4. move => _. elim.
progress. 
have ->: size (prj_path x.`1 p1.`2) = K.
smt (lemma1).
auto.
have : K <=  size x.`2.  smt.
move => q g. 

elim p4. move => zz1 . elim.
have ->: result_R.`2.`2 = false. smt.
 move => zz2 zz3.
elim zz2.  move => _. elim zz3.
move => _ qq ll. 
rewrite (fin_bind_real  x.`1 s). auto.
smt. smt. simplify.

have ->: (nth witness <: commitment * opening> (zip (prj_path x.`1 result_R.`1.`1) x.`2)
   (index false (prj_path x.`1 (permute_graph p1.`1 s))))
 = (nth (fst witness <: commitment * opening>, snd witness <: commitment * opening>) (zip (prj_path x.`1 result_R.`1.`1) x.`2)
   (index false (prj_path x.`1 (permute_graph p1.`1 s)))). smt.
rewrite nth_zip. smt. simplify.

have ->: (nth witness <: commitment * opening>  (zip (prj_path x.`1 result_R.`1.`1) (prj_path x.`1 p1.`2))
   (index false (prj_path x.`1 (permute_graph p1.`1 s))))
 = (nth (fst witness <: commitment * opening>, snd witness <: commitment * opening>) (zip (prj_path x.`1 result_R.`1.`1) (prj_path x.`1 p1.`2))
   (index false (prj_path x.`1 (permute_graph p1.`1 s)))). smt.
rewrite nth_zip. smt. simplify. auto.
progress. simplify.
rewrite /special_soundness_extract.
elim result_R.`1.`3.
progress.
elim result_R.`2.`3.
move => x p1 p2 p3 p4. 
simplify .
move => z.
rewrite (fin_bind_real  p1.`1 s ).  auto. 
smt. smt. simplify. 
have ->: (nth witness <: commitment * opening> (zip (prj_path p1.`1 result_R.`1.`1) p1.`2)
   (index false (prj_path p1.`1 (permute_graph x.`1 s))))
 = (nth (fst witness <:commitment * opening>, snd witness <:commitment * opening>) (zip (prj_path p1.`1 result_R.`1.`1) p1.`2)
   (index false (prj_path p1.`1 (permute_graph x.`1 s)))). smt.
rewrite nth_zip. 
elim p4. move => q. elim. move => q1 q2. elim q1. smt. simplify.
have ->: (nth witness <: commitment * opening> (zip (prj_path p1.`1 result_R.`1.`1) (prj_path p1.`1 x.`2))
   (index false (prj_path p1.`1 (permute_graph x.`1 s)))) 
 = (nth (fst witness <: commitment * opening>, snd witness <: commitment * opening>)  (zip (prj_path p1.`1 result_R.`1.`1) (prj_path p1.`1 x.`2))
   (index false (prj_path p1.`1 (permute_graph x.`1 s)))). smt.
rewrite nth_zip. 
elim p4. move => q. elim. move => q1 q2. elim q2. elim q1. progress. smt. simplify. auto.
smt.
qed.


theory SSB.
section.
declare module S <: SpecialSoundnessAdversary.

op ss : hc_prob.

module SpecialSoundnessBinder(A : SpecialSoundnessAdversary) : Binder = {
  proc bind() = {
      var r1,r2,g,p1,p2;
      (r1, r2) <@ A.attack(ss);
      g    <- ss;
      (p1, p2) <- hc_verify1 g r1.`1  r1.`3 r2.`3 ;
      return (p1.`2.`1, p1.`1, p1.`2.`2, p2.`1, p2.`2.`2);
  }
}.


local lemma qq &m : 
 Pr[SpecialSoundnessAdvReduction(S).run
             (ss) @ &m : res] <= Pr[BindingExperiment(SpecialSoundnessBinder(S)).main() @ &m : res]  .
byequiv;auto. 
proc. inline*. wp.  call (_:true). skip. progress. 
smt.
smt.
qed.



lemma computational_special_soundness_binding &m :
          Pr[S.attack(ss) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
             ! IsHC
                 (ss,
                  special_soundness_extract ss res.`1 res.`2)] 
  <= Pr[BindingExperiment(SpecialSoundnessBinder(S)).main() @ &m : res].
have f :           Pr[S.attack(ss) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
             ! IsHC
                 (ss,
                  special_soundness_extract ss res.`1 res.`2)] 
 <= Pr[SpecialSoundnessAdvReduction(S).run(ss) @ &m : res].
apply (computational_special_soundness ss  &m S).
smt (qq).
qed.

end section.

end SSB.
