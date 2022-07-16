pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.
require import Permutation Blum_Basics.




section.


local lemma hc_complete_hoare pa wa : IsHC (pa,wa) =>
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
apply (kjk prm ). auto. 

elim ishc. smt.
smt.  smt.
have : size pi_gwco = size (permute_graph prm s{hr}). smt.
have ->: size (permute_graph prm s{hr}) = size s{hr}. smt. 
have ->: size s{hr} = K * K. elim ishc. smt.
move => q. 
have qqq : size (prj_path (permute_witness prm w{hr}) pi_gwco) = K.
smt. smt.

(* have ->: size (unzip1 x0) = size x0. smt. *)
(* have -> : size x0 = size (permute_graph prm s{hr}). smt(supp_djoinmap). *)
(* have -> : size (permute_graph prm s{hr}) = size (s{hr}). smt. smt. *)


(* have : size (prj_path (permute_witness prm w{hr}) x0) = K. *)
(*    have ->: K = size (permute_witness prm w{hr}). smt. *)
(* apply (lemma1 (permute_witness prm w{hr}) x0).  *)
(*   have -> : size (permute_witness prm w{hr}) = size w{hr}. smt. *)
(* have -> : size x0 = size (permute_graph prm s{hr}). smt(supp_djoinmap). *)
(* have -> : size (permute_graph prm s{hr}) = size (s{hr}). smt.  *)
(* elim ishc. smt. *)
(* smt. *)

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
rewrite  (lemma3  (permute_witness prm w{hr}) (permute_graph prm s{hr})). apply lemma4. auto. auto.
progress.
apply Com_sound.



have : x1.`1 \in (nseq K true). smt.
progress.
have : x1.`2 \in (prj_path (permute_witness prm w{hr}) pi_gwco).
   smt.
 move => qq.
have : x1.`2 \in pi_gwco. apply (lemma5 x1.`2 (permute_witness prm w{hr})). auto.
move => qqq.

  have :   size (permute_graph prm s{hr}) = size pi_gwco /\ all (fun xy => snd xy \in Com xy.`1) (zip (permute_graph prm s{hr}) pi_gwco).
   apply (supp_djoinmap Com (permute_graph prm s{hr}) pi_gwco ). apply H0.
   elim. progress.
  have : forall x, x \in (zip (permute_graph prm s{hr}) pi_gwco) => x.`2 \in Com x.`1.
apply allP. apply H9.
progress. apply H10. 
  have z : x1.`1 \in (prj_path (permute_witness prm w{hr}) (permute_graph prm s{hr})). smt.
  have z2 : x1.`1 \in (permute_graph prm s{hr}). smt (lemma5).
have ->: x1 = (x1.`1,x1.`2). smt.
apply (lemma6 x1.`1 (permute_graph prm s{hr}) x1.`2 pi_gwco).
smt.
auto. auto. 
smt(lemma7 perm_eq_trans).
smt.
qed.

local lemma hc_complete statement witness &m : IsHC (statement,witness) =>
  Pr[Completeness(HonestProver, HV).run(statement, witness) @ &m : true] = 1%r.
move => inlang. byphoare (_: arg = (statement, witness) ==> _);auto. proc. inline*. wp. rnd.  simplify. wp. 
rnd.  wp. 
conseq (_: _ ==> true). progress. smt (@Distr @DBool). 
apply djoinmap_weight. apply Com_lossless.
rnd. wp.  skip. progress. apply perm_d_lossless. (* smt (ishc_prop2).  *)
qed.


local lemma hc_complete_failure statement witness &m : IsHC (statement,witness) =>
     Pr[Completeness(HonestProver, HV).run(statement, witness) @ &m : !res] = 0%r.
progress. byphoare (_: arg = (statement,witness) ==> _);auto.
hoare. simplify. conseq (hc_complete_hoare statement witness H).
qed.


lemma hc_completeness: forall (statement : hc_prob) (witness : int list) &m,
        IsHC (statement, witness) =>
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

end section.

