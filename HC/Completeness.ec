pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin.

require import Permutation Basics.

axiom kjk prm n w : prm \in perm_d n =>
 uniq w => (forall i, i \in w => 0 <= i < n) =>
  size w = n => uniq (permute_wit prm w).

axiom prj_lemma (g : graph) (w : hc_wit) (perm : permutation) : 
  take (size w) (ip (prj w) g) 
  = take (size w) (ip (prj (permute_wit perm w)) (fap perm g)).


section.

local lemma hc_complete_hoare pa wa : IsHC (pa,wa) =>
   hoare[ Completeness(HonestProver, HonestVerifier).run : arg = (pa,wa) ==> res ].
move => ishc. proc. inline*. wp. rnd. 
wp. rnd. wp. rnd. wp. skip.
progress.
pose b1 := challenge00.

case (b1 = true). 
move => h. rewrite h. simplify.
  + have ->: (zip (unzip1 x0) (unzip2 x0)) = x0. rewrite zip_unzip. auto.
split.
have : all (fun (xy : bool * (commitment * opening) ) => xy.`2 \in (Com xy.`1)) 
    (zip  (fap prm statement{hr}.`2) x0).
have f3 :   
  size (fap prm statement{hr}.`2) = size x0 /\
  all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1)
    (zip (fap prm statement{hr}.`2) x0).
apply (supp_djoinmap Com ((fap prm statement{hr}.`2))  x0). auto.
elim f3. move => f31 f32.
auto.
move => q.
apply (sub_all (fun (xy : bool * (commitment * opening)) => xy.`2 \in Com xy.`1) Ver) .
simplify. apply Com_sound.  auto.
have f1 : size x0 = size (fap prm statement{hr}.`2).
smt.
have f2 : size x0 = size (unzip1 x0).
smt.
rewrite - f2. 
rewrite f1.
rewrite fap_prop2.
split. smt. split. smt. smt.
move => p.
have ->: b1 = false. smt.
simplify. clear p. progress.
apply (kjk prm statement{hr}.`1). auto. smt (ishc_prop4). smt (ishc_prop4).
smt. 
smt.
have ->: size (unzip1 x0) = size x0. smt.
have -> : size x0 = size (fap prm statement{hr}.`2). smt(supp_djoinmap).
have -> : size (fap prm statement{hr}.`2) = size (statement{hr}.`2). smt. smt.
have ->: size (unzip2 (take statement{hr}.`1 (ip (prj (permute_wit prm witness{hr})) x0)))
 = size (take statement{hr}.`1 (ip (prj (permute_wit prm witness{hr})) x0)). smt.
have : statement{hr}.`1 <= size (ip (prj (permute_wit prm witness{hr})) x0).
have ->: size (ip (prj (permute_wit prm witness{hr})) x0) = size x0.
smt.
have -> : size x0 = size (fap prm statement{hr}.`2). smt(supp_djoinmap).
have -> : size (fap prm statement{hr}.`2) = size (statement{hr}.`2). smt. timeout 20. smt.
progress. smt.
have ->: 
  (unzip2 (take statement{hr}.`1 (ip (prj (permute_wit prm witness{hr})) x0)))
  = ((take statement{hr}.`1 (unzip2 (ip (prj (permute_wit prm witness{hr})) x0)))).
smt.
have ->: 
  (zip (take statement{hr}.`1 (ip (prj (permute_wit prm witness{hr})) (unzip1 x0)))
     (take statement{hr}.`1 (unzip2 (ip (prj (permute_wit prm witness{hr})) x0))))
  = take statement{hr}.`1  
     (zip ((ip (prj (permute_wit prm witness{hr})) (unzip1 x0)))
          ((unzip2 (ip (prj (permute_wit prm witness{hr})) x0)))).
apply take_zip.
have ->: ((ip (prj (permute_wit prm witness{hr})) (unzip1 x0)))
  = (unzip1 (ip (prj (permute_wit prm witness{hr})) (x0))).
rewrite map_ip. auto.
have ->: 
 (zip (unzip1 (ip (prj (permute_wit prm witness{hr})) x0))
        (unzip2 (ip (prj (permute_wit prm witness{hr})) x0)))
 = (ip (prj (permute_wit prm witness{hr})) x0).
apply zip_unzip.
pose pi_w := (permute_wit prm witness{hr}).
pose n := statement{hr}.`1.
pose fapg := (fap prm statement{hr}.`2). 
have ->: 
 all Ver (zip (nseq n true) (take n (ip (prj pi_w) x0)))
 = all (fun x => Ver x)
  (take n (zip (nseq n true) (ip (prj pi_w) x0))).
rewrite - take_zip.
rewrite take_nseq. auto.
have ->: (take n (zip (nseq n true) (ip (prj pi_w) x0))) =
  (take n (zip (ip (prj pi_w) fapg) (ip (prj pi_w) x0))).
  have ->: take n (zip (nseq n true) (ip (prj pi_w) x0)) =
     (zip (nseq n true) (ip (prj pi_w) x0)). 
apply take_oversize.
rewrite size_zip.
rewrite size_nseq. 
  have ->: (max 0 n) = n.  smt(ishc_prop2). smt.
  have ->: take n (zip (ip (prj pi_w) fapg) (ip (prj pi_w) x0))
   = (zip (take n (ip (prj pi_w) fapg)) (take n (ip (prj pi_w) x0))).
   rewrite - take_zip. auto.
  have ->: (take n (ip (prj pi_w) fapg)) = nseq n true.
  rewrite - (ishc_prop3 (statement{hr}, witness{hr}) statement{hr}.`1 statement{hr}.`2 witness{hr}). auto. smt. rewrite /n.
  have ->: statement{hr}.`1 = size (witness{hr}). smt. rewrite -  prj_lemma. auto.   
rewrite - take_nseq.
rewrite take_zip.
rewrite take_nseq.
rewrite take_oversize.
rewrite size_zip.
rewrite size_nseq. 
  have ->: (max 0 n) = n.  smt(ishc_prop2). smt.
auto.   
have f1 : all Ver (zip fapg x0). 
search djoin.
  have :   size (fap prm statement{hr}.`2) = size x0 /\ all (fun xy => snd xy \in Com xy.`1) (zip fapg x0).
   apply (supp_djoinmap Com fapg x0 ). apply H0.
   elim. progress.
  have : forall x, x \in (zip fapg x0) => x.`2 \in Com x.`1.
apply allP. apply H3.
progress.
apply allP. progress. 
  have : x1.`2 \in Com x1.`1. apply H4. auto.
  apply Com_sound.
have f2 : all Ver (zip (ip (prj pi_w) fapg)  (ip (prj pi_w) x0)).
rewrite - zip_ip.
have : forall x, x \in (zip fapg x0) => Ver x.
apply allP. apply f1.
progress.
have : forall x, x \in (ip (prj pi_w) (zip fapg x0)) => Ver x.
progress. apply H2.
  have ff : perm_eq (zip fapg x0) (ip (prj pi_w) (zip fapg x0)).
   smt.
  smt.
apply allP.
timeout 20. smt.
rewrite /permute_wit.
elim ishc. progress.
have : perm_eq (map prm witness{hr}) (map prm (range 0 statement{hr}.`1)).
smt.
progress.
have : perm_eq (map prm (range 0 statement{hr}.`1)) (range 0 statement{hr}.`1).
smt.
smt.
smt.
qed.

local lemma djoinmap_weight (d : 'a -> 'b distr) :  forall l,
  (forall x, is_lossless (d x)) =>
    weight (djoinmap d l) = 1%r.
elim. smt (weight_djoin_nil).
smt (weight_djoin_cons).
qed.

local lemma hc_complete statement witness &m : IsHC (statement,witness) =>
  Pr[Completeness(HonestProver, HonestVerifier).run(statement, witness) @ &m : true] = 1%r.
move => inlang. byphoare (_: arg = (statement, witness) ==> _);auto. proc. inline*. wp. rnd.  simplify. wp. 
rnd.  wp. 
conseq (_: _ ==> true). progress. smt (@Distr @DBool). 
apply djoinmap_weight. apply Com_lossless.
rnd. wp.  skip. progress. apply perm_d_lossless. smt (ishc_prop2). 
qed.


local lemma hc_complete_failure statement witness &m : IsHC (statement,witness) =>
     Pr[Completeness(HonestProver, HonestVerifier).run(statement, witness) @ &m : !res] = 0%r.
progress. byphoare (_: arg = (statement,witness) ==> _);auto.
hoare. simplify. conseq (hc_complete_hoare statement witness H).
qed.


lemma hc_completeness: forall (statement : hc_prob) (witness : int list) &m,
        IsHC (statement, witness) =>
     Pr[Completeness(HonestProver, HonestVerifier).run(statement, witness) 
            @ &m : res] = 1%r.
progress. 
rewrite - (hc_complete statement witness &m H).
have f : 0%r = 
 Pr[Completeness(HonestProver, HonestVerifier).run(statement, witness) @ &m : true]
  - Pr[Completeness(HonestProver, HonestVerifier).run(statement, witness) @ &m : res].
rewrite Pr[mu_split res].  
rewrite hc_complete_failure;auto. 
smt.
qed.

end section.

