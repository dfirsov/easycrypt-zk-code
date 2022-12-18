pragma Goals:printall.
require import AllCore DBool Bool List Distr.
require import AuxResults FS_Basics.

import ZMR.
import ComRing.

(* proof of perfect special soundness  *)
lemma qr_perfect_special_soundness (statement:qr_stat) 
 (transcript1 transcript2: transcript):
        valid_transcript_pair statement transcript1 transcript2 =>
   relation statement 
    (special_soundness_extract statement transcript1 transcript2).
proof.
rewrite /valid_transcript_pair. rewrite /verify_transcript.
case (transcript1.`2). 
case (transcript2.`2). 
auto.
rewrite /qr_verify. simplify.
progress. 
rewrite /special_soundness_extract.  
have -> : statement
   = ((inv  transcript1.`1))  * (transcript1.`3) * (transcript1.`3 ). 
smt(@ComRing).

rewrite H1.
rewrite H7.  smt(@ComRing). 
rewrite /valid_transcript_pair. rewrite /verify_transcript.
case (!transcript2.`2). 
progress. smt().
move => z.
have ->: transcript2.`2 = true. smt().
clear z.
move => z.
have zz: transcript1.`2 = false. smt().
clear z.
rewrite /qr_verify. simplify.
progress. 
rewrite /special_soundness_extract. 
simplify. rewrite /my_extract.
have -> : statement
   = ((inv  transcript2.`1))  * (transcript2.`3) * (transcript2.`3 ). smt(@ComRing).
smt(@ComRing).   
qed.
