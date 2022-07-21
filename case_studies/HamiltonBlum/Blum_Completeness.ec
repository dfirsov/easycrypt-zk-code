pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import Permutation Blum_Basics.




section.

local lemma prj_lemma (g : graph) (w : hc_wit) (perm : permutation) :
 completeness_relation g w => perm \in perm_d K 
  => prj_path w g = prj_path (permute_witness perm w) (permute_graph perm g).
progress.
have : completeness_relation (permute_graph perm g) (permute_witness perm w).
smt (permute_graph_prop3).
elim. progress. elim H. progress.
rewrite - H4. rewrite  - H7. auto.
qed.


local lemma hc_complete_hoare pa wa : completeness_relation pa wa =>
   hoare[ Completeness(HonestProver, HV).run : arg = (pa,wa) ==> res ].
move => ishc. proc. inline*. wp. rnd. 
wp. rnd. wp. rnd. wp. skip.
progress.
pose b1 := ch.

case (b1 = true). 
move => h. rewrite h. simplify.
  + have ->: (zip (unzip1 pi_gwco) (unzip2 pi_gwco)) = pi_gwco. rewrite zip_unzip. auto.
split.
have : all (fun (xy : bool * (commitment * opening) ) => xy.`2 \in (Com xy.`1)) 
    (zip  (permute_graph prm s{hr}) pi_gwco).
have f3 :   
  size (permute_graph prm s{hr}) = size pi_gwco /\
  all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1)
    (zip (permute_graph prm s{hr}) pi_gwco).
apply (supp_djoinmap Com ((permute_graph prm s{hr}))  pi_gwco). auto.
elim f3. move => f31 f32.
auto.
move => q.
apply (sub_all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1) Ver) .
simplify. apply Com_sound.  auto.
have f1 : size pi_gwco = size (permute_graph prm s{hr}).
smt.
have f2 : size pi_gwco = size (unzip1 pi_gwco).
smt.
rewrite - f2. 
rewrite f1.
rewrite permute_graph_prop2.
split. smt. split. smt. smt.
move => p.
have ->: b1 = false. smt.
simplify. clear p. progress.
elim ishc. smt.
smt.  
have : size pi_gwco = size (permute_graph prm s{hr}). smt.
have ->: size (permute_graph prm s{hr}) = size s{hr}. smt. 
have ->: size s{hr} = K * K. elim ishc. smt.
move => q. 
have qqq : size (prj_path (permute_witness prm w{hr}) pi_gwco) = K.
smt. smt.
have ->: (prj_path (permute_witness prm w{hr}) (unzip1 pi_gwco))
  = (unzip1 (prj_path (permute_witness prm w{hr}) pi_gwco)).
rewrite lemma2. auto.
have ->: 
 (zip (unzip1 (prj_path (permute_witness prm w{hr}) pi_gwco))
        (unzip2 (prj_path (permute_witness prm w{hr}) pi_gwco)))
 = ((prj_path (permute_witness prm w{hr}) pi_gwco)). 
apply zip_unzip.
elim ishc. progress.
apply allP.
move => x1.
have ->: (nseq K true) = (prj_path (permute_witness prm w{hr}) (permute_graph prm s{hr})).
smt(permute_graph_prop3).
progress.
apply Com_sound.
have : x1.`1 \in (nseq K true). 
 have md : (prj_path (permute_witness prm w{hr}) (permute_graph prm s{hr}))
   = (prj_path (w{hr}) (s{hr})).
smt (prj_lemma). smt.
have : x1.`2 \in (prj_path (permute_witness prm w{hr}) pi_gwco).
   smt.
 move => qq.
have : x1.`2 \in pi_gwco. apply (lemma5 x1.`2 (permute_witness prm w{hr})). auto.
move => qqq.
  have :   size (permute_graph prm s{hr}) = size pi_gwco /\ all (fun xy => snd xy \in Com xy.`1) (zip (permute_graph prm s{hr}) pi_gwco).
   apply (supp_djoinmap Com (permute_graph prm s{hr}) pi_gwco ). apply H0.
   elim. progress.
  have : forall x, x \in (zip (permute_graph prm s{hr}) pi_gwco) => x.`2 \in Com x.`1.
apply allP. apply H8.
progress. apply H10. 
have H6' : 
 x1 \in prj_path (permute_witness prm w{hr}) (zip (permute_graph prm s{hr}) pi_gwco).
rewrite - lemma8. auto.
rewrite  (lemma5 x1 (permute_witness prm w{hr})). apply H6'.
smt(lemma7 perm_eq_trans).
smt.
qed.


local lemma hc_complete statement witness &m : completeness_relation statement witness =>
  Pr[Completeness(HonestProver, HV).run(statement, witness) @ &m : true] = 1%r.
move => inlang. byphoare (_: arg = (statement, witness) ==> _);auto. proc. inline*. wp. rnd.  simplify. wp. 
rnd.  wp. 
conseq (_: _ ==> true). progress. smt (@Distr @DBool). 
apply djoinmap_weight. apply Com_lossless.
rnd. wp.  skip. progress. apply perm_d_lossless. (* smt (ishc_prop2).  *)
qed.


local lemma hc_complete_failure statement witness &m : 
 completeness_relation statement witness =>
   Pr[Completeness(HonestProver, HV).run(statement, witness) @ &m : !res] = 0%r.
progress. byphoare (_: arg = (statement,witness) ==> _);auto.
hoare. simplify. conseq (hc_complete_hoare statement witness H).
qed.


lemma hc_completeness: forall (statement : hc_prob) (witness : hc_wit) &m,
        completeness_relation statement witness =>
     Pr[Completeness(HonestProver, HV).run(statement, witness) 
            @ &m : res] = 1%r.
progress. 
rewrite - (hc_complete statement witness &m H).
have f : 0%r = 
 Pr[Completeness(HonestProver, HV).run(statement, witness) @ &m : true]
  - Pr[Completeness(HonestProver, HV).run(statement, witness) @ &m : res].
rewrite Pr[mu_split res].  
rewrite hc_complete_failure;auto. 
smt.
qed.


(* iterated completeness for Blum protocol  *)
lemma hc_completeness_iter: forall (statement:hc_prob) (witness:hc_wit) &m n,
        1 <= n =>
       completeness_relation statement witness =>
      Pr[CompletenessAmp(HonestProver,HV).run(statement, witness,n) @ &m : res] = 1%r.
progress.
apply (BlumProtocol.CompletenessTheory.Perfect.completeness_seq HonestProver HV _ _ _ _ _ &m).
proc.  skip.  auto.
proc.  wp.  rnd.  skip.  progress. smt.
proc.  wp.  skip. auto.
proc. rnd. conseq (_: _ ==> true). progress. smt(djoinmap_weight Com_lossless). wp. rnd. wp. skip. smt (perm_d_lossless).
progress.
apply hc_completeness. auto. auto. auto.
qed.


end section.

