pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import Aux Permutation Basics.


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
    

local lemma is_hc_perm_2 (n : int) (g : graph) (w : hc_wit) :
  !IsHC ((n,g),w) /\
     n = size w /\ 
     n * n = size g /\ 
     perm_eq w (range 0 n)
  => false \in (take n (hc_align w g)) .
progress.
  have : nseq (size w) true <> take (size w) (hc_align w g). smt.
progress.
have f : size (take (size w) (hc_align w g)) = size w.
  have ff : size (hc_align w g) = (size w) * (size w). smt.
  smt.
apply (aux_lem (take (size w) (hc_align w g)) (size w)).
auto. auto.
qed.

    
local lemma phase2 (n : int) (g : graph) (w : hc_wit) :
  !IsHC ((n,g),w) /\
     n = size w /\ 
     n * n = size g /\ 
     perm_eq w (range 0 n) =>
   false \in (take n (hc_align w g)).
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



lemma fin_bind_real   (w : hc_wit) (g : graph) (n : int) c o1 (p : permutation) X: 
   !IsHC ((n,g), permute_wit (inv p) w) =>  
   hc_verify (n,g) c true  (Left (p,o1)) =>
   hc_verify (n,g) c false (Right (w,X)) 
  => Ver (true,  nth witness (take n (zip (hc_align w c)
                             X)) (index false (take n (hc_align w (fap p g))))) /\
     Ver (false, nth witness (take n (zip (hc_align w c)
                             (hc_align w o1))) (index false (take n (hc_align w (fap p g))))).
proof. 
move => p0 p1 p2 .
apply (quasi_fin ((take n (hc_align w (fap p g)))) n) .
apply is_hc_perm_2.   split. 
have ->: IsHC ((n, fap p g), w) = IsHC ((n, fap (inv p) (fap p g)), permute_wit (inv p) w).
smt. smt.
split. elim p2. smt.
split.  elim p1. smt. elim p1 p2. smt.
elim p1 p2. progress. smt.
elim p1 p2. progress. rewrite /hc_align. rewrite - zip_ip. apply phase1. auto.
elim p1 p2. progress.
  have : size (hc_align w (fap p g)) = (size w * size w). smt.
  smt.
elim p1 p2. progress.
  have : size (hc_align w c) = (size w) * (size w). 
  smt.
  have : size (hc_align w o1) = (size w) * (size w). 
  smt.
smt.
elim p2.
progress.
  have : size (hc_align w c) = (size w) * (size w). 
  smt.
smt.
qed.

end section.



op my_extract (p : hc_prob) (c : hc_com)   (r1 r2 : hc_resp) : int list  =
 with r1 = Left  x, r2 = Right z => let n = p.`1 in let g = p.`2  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                                     permute_wit (inv p) w
 with r1 = Right z, r2 = Left  x => let n = p.`1 in let g = p.`2  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                                     permute_wit (inv p) w
 with r1 = Left  x, r2 = Left  z => witness
 with r1 = Right x, r2 = Right z => witness.

op special_soundness_extract (p : hc_prob) (r1 r2 : transcript) : int list = 
 my_extract p r1.`1  r1.`3 r2.`3.

clone include SpecialSoundnessStatements  with  
  op special_soundness_extract <- special_soundness_extract.




clone include ComputationalSpecialSoundnessStatement with
 op special_soundness_red_function <- fun _ r => r.



op hc_verify1 (p : hc_prob) (c : hc_com)   (r1 r2 : hc_resp) : (bool * (commitment * opening)) * (bool * (commitment * opening))  =
 with r1 = Left  x, r2 = Right z => let n = p.`1 in let g = p.`2  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
   ((true,  nth witness (take n (zip (hc_align w c)
                             X)) (index false (take n (hc_align w (fap p g))))), 
                                 (false, nth witness (take n (zip (hc_align w c)
                             (hc_align w o1))) (index false (take n (hc_align w (fap p g))))))
 with r1 = Right z, r2 = Left  x => let n = p.`1 in let g = p.`2  in let p = x.`1 in let o1 = x.`2 in 
                                    let w = z.`1 in let X = z.`2 in 
                            ((true,  nth witness (take n (zip (hc_align w c)
                             X)) (index false (take n (hc_align w (fap p g))))), 
                                 (false, nth witness (take n (zip (hc_align w c)
                             (hc_align w o1))) (index false (take n (hc_align w (fap p g))))))
 with r1 = Left  x, r2 = Left  z => ((witness, witness), (witness, witness))
 with r1 = Right x, r2 = Right z => ((witness, witness), (witness, witness)).

 
module (SpecialSoundnessAdvReduction : SpecialSoundnessAdvReduction) (A : SpecialSoundnessAdversary)  = {
  proc run(statement : hc_prob, aux : auxiliary_input) : bool = {
      var r1,r2,n,g,p1,p2;
      (r1, r2) <@ A.attack(statement, aux);
      (n,g)    <- statement;
      (p1, p2) <- hc_verify1 (n,g) r1.`1  r1.`3 r2.`3 ;
      return (Ver p1 /\ Ver p2) /\ p1.`1 <> p2.`1 /\ p1.`2.`1 = p2.`2.`1;
  }
}.


lemma computational_special_soundness:
      forall (s : hc_prob) (aux : auxiliary_input) &m
        (SpecialSoundnessAdversary <: SpecialSoundnessAdversary),
        let attack_prob =
          Pr[SpecialSoundnessAdversary.attack(s, aux) @ &m :
             valid_transcript_pair s res.`1 res.`2 /\
             ! IsHC
                 (s, special_soundness_extract s res.`1 res.`2)] in
        let red_prob =
          Pr[SpecialSoundnessAdvReduction(SpecialSoundnessAdversary).run
             (s, aux) @ &m : res] in
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
rewrite fin_bind_real.  auto. 
smt. smt. simplify. 
have : s.`1 <= size (hc_align x.`1 p1.`2). 
elim p4. move => _. elim.
progress. 
have ->: size (hc_align x.`1 p1.`2) = s.`1 * s.`1. smt. smt.
have : s.`1 <=  size x.`2.  smt.
smt. smt.
move => q.
have z : result_R.`1.`2 = false. smt.
clear q. 
rewrite /special_soundness_extract.
elim result_R.`1.`3.
elim result_R.`2.`3. progress. 
move => x p1 p2 p3 p4. simplify.
rewrite fin_bind_real.   auto.
smt. smt. simplify. smt. 
elim result_R.`2.`3. 
move => x p1 p2 p3.
simplify. move => p4. progress. smt. smt. 
have : size p1.`2 <= size (hc_align p1.`1 x.`2). 
elim p3. move => _. elim.
progress. 
have ->: size (hc_align p1.`1 x.`2) = s.`1 * s.`1. smt. smt.
have : s.`1 <=  size p1.`2.  smt.
smt. smt. (* fin_bind_real *)
qed.



theory SSB.
section.
declare module S : SpecialSoundnessAdversary.

op ss : hc_prob.
op auxx : auxiliary_input.

module SpecialSoundnessBinder(A : SpecialSoundnessAdversary) : Binder = {
  proc bind() = {
      var r1,r2,n,g,p1,p2;
      (r1, r2) <@ A.attack(ss, auxx);
      (n,g)    <- ss;
      (p1, p2) <- hc_verify1 (n,g) r1.`1  r1.`3 r2.`3 ;
      return (p1.`2.`1, p1.`1, p1.`2.`2, p2.`1, p2.`2.`2);
  }
}.


local lemma qq &m : 
 Pr[SpecialSoundnessAdvReduction(S).run
             (ss, auxx) @ &m : res] <= Pr[BindingExperiment(SpecialSoundnessBinder(S)).main() @ &m : res]  .
byequiv;auto. 
proc. inline*. wp.  call (_:true). skip. progress. 
smt.
smt.
qed.



lemma computational_special_soundness_binding &m :
          Pr[S.attack(ss, auxx) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
             ! IsHC
                 (ss,
                  special_soundness_extract ss res.`1 res.`2)] 
  <= Pr[BindingExperiment(SpecialSoundnessBinder(S)).main() @ &m : res].
have f :           Pr[S.attack(ss, auxx) @ &m :
             valid_transcript_pair ss res.`1 res.`2 /\
             ! IsHC
                 (ss,
                  special_soundness_extract ss res.`1 res.`2)] 
 <= Pr[SpecialSoundnessAdvReduction(S).run
             (ss, auxx) @ &m : res].
apply (computational_special_soundness ss auxx &m S).
smt (qq).
qed.

end section.

end SSB.
