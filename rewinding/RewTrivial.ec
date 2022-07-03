require import AllCore.
require RewBasics.

clone import RewBasics as RW with type sbits <- unit.


lemma no_globs_rew : forall (A <: Rew), (forall (x y : glob A), x = y) =>
    islossless A.getState /\ islossless A.setState =>
  exists (f : glob A -> unit), injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                             /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState() @ &m : glob A = x] = 1%r) /\
  islossless A.setState.
proof. move => A. progress.
pose f := fun (x : glob A) => tt.
have finj : injective f. rewrite /injective. smt.
exists f. split.  apply finj.
split.
move => &m. byphoare. proc*. call H0. skip. progress. apply H. auto. auto.
split.
progress.
byphoare. proc*. call H1. skip. progress.  apply H. auto. auto.
apply H1.
qed.    
