pragma Goals:printall.
require import AllCore DBool Bool List Distr Int Aux DJoin Permutation.
require import Generic_Defs_thy.
require import Basics Real.


clone include SpecialSoundnessStatements with 
 op special_soundness_extract <- witness.

clone include ComputationalSpecialSoundnessStatement 
 with  op special_soundness_red_function <- fun x (r : real) => r * r
proof*.


