pragma Goals:printall.
require import AllCore Bool.
require import Basics.

require import CyclicGroup.

print CyclicGroup.
import FDistr.

(* t1 for true run, t2 for false run *)
op my_extract (p : dl_prob) (t1 t2 : transcript) : dl_wit
 =  t1.`3  - t2.`3 .



op special_soundness_extract (p : dl_prob) (t1 t2 : transcript): dl_wit
 = if t1.`2 then my_extract p t1 t2 else my_extract p t2 t1.



lemma perfect_special_soundness (statement:dl_prob) 
 (transcript1 transcript2: transcript):
        valid_transcript_pair statement transcript1 transcript2 =>
   soundness_relation statement 
    (special_soundness_extract statement transcript1 transcript2).
proof. 
rewrite /valid_transcript_pair. rewrite /verify_transcript.
case (transcript1.`2). 
case (transcript2.`2). 
smt.
rewrite /dl_verify. simplify.
progress. 
rewrite /special_soundness_extract. 
rewrite H0. simplify. rewrite /my_extract.
rewrite /soundness_relation / IsDL. 
have  : (statement.`2 * transcript1.`1) /  transcript1.`1
   =  (statement.`1 ^ transcript1.`3) / transcript1.`1. 
smt.
have -> : statement.`2 * transcript1.`1 /  transcript1.`1 = 
  statement.`2. 
  have -> : statement.`2 * transcript1.`1 / transcript1.`1 
    = statement.`2 * transcript1.`1 * (inv transcript1.`1).
smt.
   have -> : statement.`2 * transcript1.`1 * inv transcript1.`1
      = statement.`2 * (transcript1.`1 * inv transcript1.`1).
   rewrite mulA. auto. rewrite  mulN.  rewrite mulC.  apply mul1.
move => f. rewrite f.
rewrite  H1.
have -> : statement.`1 ^ transcript1.`3 / transcript2.`1
 = statement.`1 ^ transcript1.`3 * (inv transcript2.`1).
smt.
have ->: inv transcript2.`1
 = inv (statement.`1 ^ transcript2.`3).
smt.
have -> : inv (statement.`1 ^ transcript2.`3)
  = (statement.`1 ^ (- transcript2.`3)).
rewrite - (pow_opp). auto.
smt.
rewrite /dl_verify. simplify.
progress. 
rewrite /special_soundness_extract. 
rewrite  H. simplify. rewrite /my_extract.
have H4 : statement.`1 ^ transcript2.`3 = statement.`2 * transcript2.`1.
smt. clear H3.
pose tran2 := transcript1.
pose tran1 := transcript2.
rewrite /soundness_relation / IsDL. 
have  : (statement.`2 * tran1.`1) /  tran1.`1
   =  (statement.`1 ^ tran1.`3) / tran1.`1. 
smt.
have -> : statement.`2 * tran1.`1 /  tran1.`1 = 
  statement.`2. 
  have -> : statement.`2 * tran1.`1 / tran1.`1 
    = statement.`2 * tran1.`1 * (inv tran1.`1).
smt.
   have -> : statement.`2 * tran1.`1 * inv tran1.`1
      = statement.`2 * (tran1.`1 * inv tran1.`1).
   rewrite mulA. auto. rewrite  mulN.  rewrite mulC.  apply mul1.
move => f. rewrite f.
have -> : statement.`1 ^ tran1.`3 / tran1.`1
 = statement.`1 ^ tran1.`3 * (inv tran1.`1).
smt.
have ->: inv tran1.`1
 = inv (statement.`1 ^ tran2.`3).
rewrite - H0. smt. 
have -> : inv (statement.`1 ^ tran2.`3)
  = (statement.`1 ^ (- tran2.`3)).
rewrite - (pow_opp). auto.
smt.
qed.
