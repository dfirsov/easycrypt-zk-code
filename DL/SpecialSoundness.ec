pragma Goals:printall.
require import AllCore Bool.
require import Basics.

require import CyclicGroup.
import FDistr.

op my_extract (p : dl_prob) (t1 t2 : transcript) : dl_wit
 =  (inv (t1.`2 - t2.`2)) * (t1.`3  - t2.`3).


op special_soundness_extract (p : dl_prob) (t1 t2 : transcript): dl_wit
 = my_extract p t1 t2.

lemma qqq (a b c : t) : c * (a - b) = c * a + (c * - b).
smt.
qed.

lemma www (a b c : t) : c * (a - b) = c * a - (c * b).
rewrite qqq.
smt.
qed.

lemma ttt (a b : t) : - (a * b) = (-a)  * b.
rewrite mulNf.
auto.
qed.


lemma uuu (a : group) : a ^ one = a.
rewrite inj_gpow_log.
rewrite pow_pow.
smt.
qed.



lemma perfect_special_soundness (statement:dl_prob) 
 (transcript1 transcript2: transcript):
        valid_transcript_pair statement transcript1 transcript2 =>
   soundness_relation statement 
    (special_soundness_extract statement transcript1 transcript2).
proof. 
rewrite /valid_transcript_pair. rewrite /verify_transcript.
rewrite /dl_verify.
progress. 
rewrite /special_soundness_extract /my_extract. 
rewrite /soundness_relation /IsDL.
rewrite H in H1.
clear H.
have ->:
(inv (transcript1.`2 - transcript2.`2) * (transcript1.`3 - transcript2.`3))
  = ((transcript1.`3 - transcript2.`3) * inv (transcript1.`2 - transcript2.`2)). smt.
rewrite - pow_pow.
have -> : 
 g ^ (transcript1.`3 - transcript2.`3) = 
  (statement ^ (transcript1.`2 - transcript2.`2)).
  have ->: g ^ (transcript1.`3 - transcript2.`3)
    = g ^ transcript1.`3 * g ^ (- transcript2.`3).
  smt.
  have ->: g ^ - transcript2.`3 = 
    inv (g ^ transcript2.`3). smt.
   rewrite H1 H2.
  have ->: inv (statement ^ transcript2.`2 * transcript2.`1)  = inv (statement ^ transcript2.`2) * (inv transcript2.`1)    . smt.
have ->: statement ^ transcript1.`2 * transcript2.`1 *
  (inv (statement ^ transcript2.`2) * inv transcript2.`1) =
  statement ^ transcript1.`2 * 
  (inv (statement ^ transcript2.`2)).
smt (mulN mulA mul1 mulC).
have ->: inv (statement ^ transcript2.`2)
  = (statement ^ - transcript2.`2).
rewrite pow_opp. auto.
smt.
rewrite  pow_pow.
rewrite  mulfV. smt.
apply  uuu.
qed.
