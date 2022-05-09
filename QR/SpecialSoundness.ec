pragma Goals:printall.
require import AllCore DBool Bool List Distr.
require import Aux Permutation Basics.


(* t1 for true run, t2 for false run *)
op my_extract (p : qr_prob) (t1 t2 : transcript) : qr_wit
 = ((inv  t2.`3) * t1.`3) .

op special_soundness_extract (p : qr_prob) (t1 t2 : transcript): qr_wit
 = if t1.`2 then my_extract p t1 t2 else my_extract p t2 t1.


lemma perfect_special_soundness (statement:qr_prob) 
 (transcript1 transcript2: transcript):
        valid_transcript_pair statement transcript1 transcript2 =>
   soundness_relation statement 
    (special_soundness_extract statement transcript1 transcript2).
proof.
rewrite /valid_transcript_pair. rewrite /verify_transcript.
case (transcript1.`2). 
case (transcript2.`2). 
smt.
rewrite /qr_verify. simplify.
progress. 
rewrite /special_soundness_extract. 
rewrite H0. simplify. rewrite /my_extract.
rewrite /IsSqRoot.
have -> : statement
   = ((inv  transcript1.`1))  * (transcript1.`3) * (transcript1.`3 ). smt.
rewrite H1.
rewrite H6.
smt.   
timeout 20. smt. (* same as above but derived automatically  *)
qed.
