require import AllCore List.

(* parameter types  *)
type statement, witness, commitment, response, challenge.

(* synonyms   *)
type relation   = statement -> witness -> bool.
type transcript = commitment * challenge * response.

op in_language (R:relation) statement: bool = exists witness, R statement witness.

(* parameter functions *)
op challenge_set : challenge list. 

axiom challenge_set_size : 0 < size challenge_set.
op verify_transcript : statement -> transcript -> bool.
