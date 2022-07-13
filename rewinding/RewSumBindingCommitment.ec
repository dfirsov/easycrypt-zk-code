pragma Goals:printall.
require import AllCore.
require import Commitment.


require RewSumBindingGeneric.



theory SumBinding.


require RewBasics.

type sbits, irt, rrt,iat.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.


clone import RewBasics as RW with type sbits <- sbits,
                                  type rrt <- rrt,
                                  type irt <- irt,
                                  type iat <- iat,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.


type value. (* Public parameters *)
type commitment.
type openingkey.
type message.

op m1 : message.
op m2 : message.
axiom m1nem2 : m1 <> m2.

clone import CommitmentProtocol with type message <- message,
                              type value <- value,
                              type commitment <- commitment,
                              type openingkey <- openingkey.

module type SumBinder = {
  proc commit(param: value) : commitment
  proc open(m: message) : openingkey
}.


module SumBindingExperiment(S: CommitmentScheme, A: SumBinder) = {
  proc main(m:message) : bool = {
    var param, c, d, v;

    param <@ S.gen();
    c <@ A.commit(param);

    d <@ A.open(m);
    v <@ S.verify(param, m, c, d);
    return v;
  }
}.

(* Inherits from both SumBinder and Rewindable *)
module type RewindableSumBinder = {
  proc commit(param: value) : commitment
  proc open(m: message) : openingkey
  proc getState()          : sbits
  proc * setState(b : sbits) : unit
}.

module R(A : RewindableSumBinder) : Binder = {
  proc bind(x: value) : commitment * message * openingkey * message * openingkey = {
  var c, d1, d2, s;
  c <@ A.commit(x);

  s <@ A.getState();
  d1 <@ A.open(m1);
  A.setState(s);
  d2 <@ A.open(m2);

  return (c, m1, d1, m2, d2);
  }
}.




section.

declare module S <: CommitmentScheme.
declare module A <: RewindableSumBinder {-S}.

axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

  

op Ver (x : value * message * commitment * openingkey) :  bool.
axiom verify_det : forall a,
  phoare [ S.verify : arg = a ==> res = Ver a ] = 1%r.

axiom Aoll : islossless A.open.
axiom Acl : islossless A.commit.
axiom Sgl : islossless S.gen.

local module WInit = {
  proc init() : value * commitment = {
     var x, c;
     x <@ S.gen();
     c <@ A.commit(x);
     return (x, c);
  }
}.


local module WA = {
  proc ex1(vc : value * commitment) : value * message * commitment * openingkey  = {
    var d;
    d <@ A.open(m1);    
    return (vc.`1, m1, vc.`2, d);
  }
  proc ex2(vc : value * commitment) : value * message * commitment * openingkey = {
    var d;
    d <@ A.open(m2);    
    return (vc.`1, m2, vc.`2, d);
  }

  proc getState() = {
    var r;
    r <@ A.getState();
    return r;
  }

  proc run(vc : value * commitment) : value * message * commitment * openingkey = {
    return witness;
  }

  proc setState(s : sbits) = {
    A.setState(s);
  }

}.


clone import RewSumBindingGeneric.RSBA with type sbits <- sbits,
                                  type rrt <- value * message * commitment * openingkey,
                                  type irt <- value * commitment,
                                  type iat <- unit,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.


local lemma f_case &m : 
      Pr[SumBindingExperiment(S,A).main(m1) @ &m : res]
   =   Pr[RSBA.RSBH.SB(WA,WInit).main_1() @ &m : Ver res].
proof. byequiv (_: (={glob A, glob S}) /\ m{1} = m1 ==> _).
proc.   inline WA.ex1. wp.
inline*.
seq 3 6 : (param{1} = x{2} /\ ={c,d,glob A, glob S} /\ m{1} = m1 /\ vc{2} = (x{2}, c{2})).
call (_:true). wp.  call (_:true). call(_:true). wp. skip. progress.
seq 0 0 : (exists p' l' c' d', (p',l',c',d') = (param,m,c,d){1} /\ param{1} = x{2} /\
  ={c, d, glob A, glob S} /\ m{1} = m1 /\ vc{2} = (x{2}, c{2}) ). skip. smt. elim*.
progress.
call {1} (verify_det (p',l',c',d')).  skip. 
progress.  auto. auto. 
qed.


local lemma t_case &m : 
      Pr[SumBindingExperiment(S,A).main(m2) @ &m : res]
   =   Pr[RSBA.RSBH.SB(WA,WInit).main_2() @ &m : Ver res ].
proof. byequiv (_: (={glob A, glob S}) /\ m{1} = m2 ==> _).
proc.   inline WA.ex1. wp.
inline*.
seq 3 6 : (param{1} = x{2} /\ ={c,d,glob A, glob S} /\ m{1} = m2 /\ vc{2} = (x{2}, c{2})).
call (_:true). wp.  call (_:true). call(_:true). wp. skip. progress.
seq 0 0 : (exists p' l' c' d', (p',l',c',d') = (param,m,c,d){1} /\ param{1} = x{2} /\
  ={c, d, glob A, glob S} /\ m{1} = m2 /\ vc{2} = (x{2}, c{2}) ). skip. smt. elim*.
progress.
call {1} (verify_det (p',l',c',d')).  wp. skip. 
progress.  auto. auto. 
qed.


local lemma b_case &m : 
  Pr[ BindingExperiment(S,R(A)).main() @ &m : res ]
  =  Pr[RSBA.RSBH.SB(WA,WInit).main_12() @ &m : Ver res.`1 /\ Ver res.`2 ].
proof. byequiv (_: ={glob A, glob S} ==> _).
proc. inline*. wp.
seq 8 13 : ((x,m,c,d){1} = (r1{2}) /\ (x, m', c, d'){1} = (vc0{2}.`1, m2, vc0{2}.`2, d0{2}) /\  m{1} <> m'{1}).
wp.  call (_:true). wp. call (_:true). wp. call (_:true). wp. call (_:true). wp.  call (_:true). wp. call (_:true).
wp. skip. progress. apply m1nem2.
seq 0 0 : ((x,m,c,d){1} = (r1{2}) /\ (x, m', c, d'){1} = (vc0{2}.`1, m2, vc0{2}.`2, d0{2}) /\  m{1} <> m'{1} 
           /\ exists p' p'' l' l'' c' c'' dd' dd'', (p',l',c',dd') = (x,m,c,d){1} /\ (p'',l'',c'',dd'') = (x, m', c, d'){1}).
skip. smt. elim*. progress.
call {1} (verify_det (p'',l'',c'',dd'')).
call {1} (verify_det (p',l',c',dd')). skip. progress.
auto. auto.
qed.


lemma commitment_sum_binding &m:
    Pr[ SumBindingExperiment(S,A).main(m1) @ &m : res ] +
    Pr[ SumBindingExperiment(S,A).main(m2) @ &m : res ] <=
    1%r + 2%r * Pr[ BindingExperiment(S,R(A)).main() @ &m : res ].
proof.  rewrite f_case t_case b_case.
apply (sum_binding_generic WA WInit).
proc. call Aoll. skip. auto. proc. call Aoll. skip. auto. proc. call Acl. call Sgl. skip. auto.
proc. call(_:true). call(_:true). skip. smt.
proc. call(_:true). call(_:true). skip. smt.
proc. call(_:true). call(_:true). skip. smt.
proc. call(_:true). call(_:true). skip. smt.
(* elim (RewProp). *)
(* progress. *)
(* exists f. *)
(* progress. *)
(* have ->: Pr[WA.getState() @ &m0 : (glob A) = (glob A){m0} /\ res = f (glob A){m0}] = Pr[A.getState() @ &m0 : (glob A) = (glob A){m0} /\ res = f (glob A){m0}]. *)
(*   byequiv. proc*.  inline*. wp. call (_:true). skip. progress. auto.  auto. apply H0. *)
(* have ->: Pr[WA.setState(f x) @ &m0 : (glob A) = x] = Pr[A.setState(f x) @ &m0 : (glob A) = x]. *)
(*   byequiv. proc*. inline*. sp. call (_:true). skip. progress. auto.  auto. apply H1. auto. *)
(* proc. call H2. skip. auto. *)
qed.


end section.
end SumBinding.



theory PedersenExample.

require import Pedersen.
require import CyclicGroup.
require RewBasics.

type sbits, irt, rrt,iat.

op pair_sbits : sbits * sbits -> sbits.
op unpair: sbits -> sbits * sbits.
axiom ips: injective pair_sbits. 
axiom unpair_pair x : unpair (pair_sbits x) = x.


clone import RewBasics as RW with type sbits <- sbits,
                                  type rrt <- rrt,
                                  type irt <- irt,
                                  type iat <- iat,
                                  op pair_sbits <- pair_sbits,
                                  op unpair <- unpair.


(* assuming that message is not singleton type *)
op m1 : message.
op m2 : message.
axiom m1nem2 : m1 <> m2.

op Ver (x: value * message * commitment* openingkey) : bool = x.`3 = (g ^ x.`4) * (x.`1^x.`2).



require RewWithInit.
clone import RewWithInit.RWI as RWAW with type sbits <- sbits,
                                  type rrt <- value * message * commitment * openingkey,
                                  type irt <- value * commitment,
                                  type iat <- unit.


clone import SumBinding  with
  type sbits <- sbits,
  type rrt <- rrt,
  type irt <- irt,
  type iat <- iat,
  type value      <- value,
  type commitment <- commitment,
  type openingkey <- openingkey,
  type message    <- message,
  op m1 <- m1,
  op m2 <- m2,
  op Ver <- Ver,
  op pair_sbits <- pair_sbits,
  op unpair <- unpair.



section.
declare module A <: RewindableSumBinder.


axiom All : islossless A.open.
axiom Acl : islossless A.commit.


axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.


lemma pedersen_sum_binding : forall &m,
      Pr[SumBindingExperiment(Pedersen, A).main(m1) @ &m : res] +
      Pr[SumBindingExperiment(Pedersen, A).main(m2) @ &m : res] <=
      1%r + 2%r * Pr[CommitmentProtocol.BindingExperiment(Pedersen, R(A)).main() @ &m : res].
proof.
apply (commitment_sum_binding Pedersen A).
(* apply RewProp. *)
(* move => x. proc. *)
(* wp.  skip.  auto. *)
(* apply All. *)
(* apply Acl. *)
(* proc. *)
(* wp. rnd.  skip. smt. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
(* apply ips. apply unpair_pair. *)
qed.


end section.
end PedersenExample.
