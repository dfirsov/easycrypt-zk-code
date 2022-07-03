pragma Goals:printall.
require import AllCore.
require import RewBasics.


type ct.                        (* some countable type *)



op ct_sbits : ct -> sbits.
axiom iis:  injective ct_sbits.

op unct: sbits -> ct.


axiom unct_ct x : unct (ct_sbits x) = x.


section.

declare module A : Rew.
declare module B : Rew{A}.

axiom RewProp_A :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

axiom RewProp_B :
  exists (f : glob B -> sbits),
  injective f /\
  (forall &m, Pr[ B.getState() @ &m : (glob B) = ((glob B){m})
                                   /\ res = f ((glob B){m} ) ] = 1%r) /\
  (forall &m b (x: glob B), b = f x =>
    Pr[B.setState(b) @ &m : glob B = x] = 1%r) /\
  islossless B.setState.


  
local module T(A : Rew, B : Rew) : Rew = {
    
  var x : ct
    
  proc getState(): sbits = {
    var stateA, stateB : sbits;
    stateA <- A.getState();
    stateB <- B.getState();
    return pair_sbits (ct_sbits(x),pair_sbits(stateA, stateB));      
  }
  proc setState(state: sbits): unit = {
     A.setState(fst (unpair (snd (unpair state))));
     B.setState(snd (unpair (snd (unpair state))));
     x <- unct (fst (unpair state));
  }
  
}.

 
local lemma rewindable_T :
    exists (f : glob T(A,B) -> sbits),
    injective f /\
    (forall (glT : glob T(A,B)),
  phoare[ T(A,B).getState : (glob T(A,B)) = glT ==> (glob T(A,B)) = glT  /\ res = f glT ] = 1%r) /\
    (forall (glT: glob T(A,B)),
  phoare[T(A,B).setState: state = f glT ==> glob T(A,B) = glT] = 1%r).    
proof. elim (rewindable_A A RewProp_A).
move => fA [s1 [s2 [s3] ]] s4.
elim (rewindable_A B RewProp_B).
move => fB [t1 [t2 [t3]]] t4.
exists (fun (gc : glob T(A,B)) =>  pair_sbits (ct_sbits (gc.`1), pair_sbits(fA gc.`3 , fB gc.`2) ) ).
progress. move => y z. smt.
proc.
have : phoare[ A.getState : (glob A) = (glT.`3) ==> (glob A) = (glT.`3) /\ res = fA (glT.`3)] = 1%r.
apply s2. move => h.
have : phoare[ B.getState : (glob B) = (glT.`2) ==> (glob B) = (glT.`2) /\ res = fB (glT.`2)] = 1%r.
apply t2. move => h'.
call h'.
call h.
skip. progress.
proc. wp. 
call (t3 glT.`2). 
call (s3 glT.`3).
skip. 
progress.
smt. smt. smt.
qed.


local lemma trans_rew :
  exists (f : glob T(A,B) -> sbits),
  injective f /\
  (forall &m, Pr[ T(A,B).getState() @ &m : (glob T(A,B)) = ((glob T(A,B)){m})
                                   /\ res = f ((glob T(A,B)){m} ) ] = 1%r) /\
  (forall &m b (x: glob T(A,B)), b = f x =>
    Pr[T(A,B).setState(b) @ &m : glob T(A,B) = x] = 1%r) /\
  islossless T(A,B).setState.
proof. 
elim rewindable_T.
progress.
exists f.
progress.
byphoare (_: (glob T(A,B)) = (glob T(A,B)){m} ==> _) .  proc*. call (H0 (glob T(A,B)){m}).
skip.  progress. auto. auto.
byphoare (_: arg = f x  ==> _).
proc*. call (H1 x).  skip.  progress. auto. auto.
proc.  wp. 
elim RewProp_B. progress.
elim RewProp_A. progress.
call H5.
call H9.
skip. auto.
qed.



end section.
