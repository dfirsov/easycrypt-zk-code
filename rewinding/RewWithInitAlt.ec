pragma Goals:printall.
require import AllCore.

require import Distr.
require import List.
require import AllCore List Binomial.
require import Ring StdRing StdOrder StdBigop Discrete RealSeq RealSeries.
(*---*) import IterOp Bigint Bigreal Bigreal.BRA.
(*---*) import IntOrder RealOrder RField.
require import Finite.
require (*--*) FinType.

require import RandomFacts.
require import JensensSquare.

theory RWI.

type sbits, iat, rrt, irt.

require RewBasics.
clone import RewBasics as RW with type sbits <- sbits,
                                  type iat   <- iat,
                                  type iat2  <- irt,
                                  type rrt   <- rrt,
                                  type irt   <- irt.


require FiniteApproximation.
  

module QQ(A : RewRun, B : Initializer) = {
    module G = GetRunSetRunConj(A)

    proc main51(i:iat) = {
      var rb,s;
      rb <- B.init(i);
      s <- A.getState();
      return (rb, s);
    }

    proc main52(i : irt) = {
      var r;
      r <- G.main(i);
      return r;
    }
    
    proc main5(i:iat) = {
      var s, r;
      s <- main51(i);
      r <- main52(s.`1);
      return (r,s);
    }

    proc main6(i:iat) = {
      var s, r;
      s <- main51(i);
      r <- A.run(s.`1);
      return ((s.`1, r),s);
    }

    proc main(i:iat) = {
      var s, r0, r1, r2;
      r0 <- B.init(i);
      s <- A.getState();
      r1 <- A.run(r0);
      A.setState(s);
      r2 <- A.run(r0);
      return ((r0,r1), (r0, r2));
    }

    proc main_run'(i:iat) = {
      var s, r, r0;
      r0 <- B.init(i);
      s <- A.getState();
      r <- A.run(r0);
      return (r0, r);
    }

    proc main_run(i:iat) = {
      var r, r0;
      r0 <- B.init(i);
      r <- A.run(r0);
      return (r0, r);
    }
}.


section.

declare module A : RewRun.
declare module B : Initializer.

clone import FiniteApproximation.FinApprox as FA with type at <- iat,
                                                              type rt <- irt * sbits.


local module RunMe = {
  module QQ = QQ(A,B)
  proc main(i:iat) : irt * sbits = {
      var s, r;
      s <- QQ.main51(i);
      r <- A.run(s.`1);
      return s;    
  }
}.

(* ASSUMPTIONS *)


axiom Bsens : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={glob A} ].    
axiom Bsens2 : equiv[ B.init ~ B.init : ={arg, glob A, glob B} ==> ={res, glob A} ].    


axiom RewProp :
  exists (f : glob A -> sbits),
  injective f /\
  (forall &m, Pr[ A.getState() @ &m : (glob A) = ((glob A){m})
                                   /\ res = f ((glob A){m} ) ] = 1%r) /\
  (forall &m b (x: glob A), b = f x =>
    Pr[A.setState(b) @ &m : glob A = x] = 1%r) /\
  islossless A.setState.

  
axiom ll_A_run : islossless A.run.
(* /ASSUMPTIONS *)




local lemma sga &m (i : iat) : forall epsilon, epsilon > 0%r => exists (M : (irt * sbits) list), uniq M /\ Pr[ QQ(A,B).main6(i) @ &m : !(res.`2 \in M) ] < epsilon. 
proof.
have : forall (M : (irt * sbits) list), Pr[ QQ(A,B).main6(i) @ &m : !(res.`2 \in M) ] = Pr[ RunMe.main(i) @ &m : !(res \in M) ].
move => M. byequiv (_: (={arg, glob A, glob B}) ==> _ ).
proc. inline*.
seq 2 2 : (={rb, glob A}). sp.  call Bsens2. skip. auto.
call (_:true). wp.  call(_:true). skip. progress. auto. auto.
move => q. move => epsilon.
elim (fin_approx_prog_no_glob RunMe &m i).
move => D J. progress.
elim (H1 epsilon H2).
move => N np. exists (pmap J (range 0 N)). split. smt.
rewrite q. apply np.
qed.



local lemma intlem1 &m M i : Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 ] = Pr[ QQ(A,B).main(i) @ &m : M res.`1 /\ M res.`2 ].
proof. byequiv (_: (={arg, glob A, glob B}) ==> _).
proc. inline*. 
seq 2 1 : (rb{1} = r0{2} /\ ={glob A}). sp. call Bsens2. skip. auto.
wp. call(_:true). wp.
elim (rewindable_A A RewProp).
move => fA [s1 [s2 [s3]]] s4. 
call (_:true). call(_:true).
call (_:true).
wp.
conseq (_: exists ga, (glob A){1} = ga /\ rb{1} = r0{2} /\ ={glob A} ==> _). smt.
elim*. move => ga. call {1} (s2 ga).
skip. progress. auto. auto.
qed.


local lemma intlem2 &m M i : Pr[ QQ(A,B).main6(i) @ &m : M res.`1 ] = Pr[ QQ(A,B).main_run'(i) @ &m : M res ].
proof.  byequiv (_: (={arg, glob A, glob B}) ==> _).
proc. inline*. 
seq 2 1 : (rb{1} = r0{2} /\ ={glob A}). sp. call Bsens2. skip. auto.
wp. call (_:true). wp. call (_:true). skip. progress. auto. auto.
qed.
  

local lemma www : forall &m i, forall (s0 : sbits) r,
   phoare [ QQ(A,B).main51 : arg = i /\ (glob A) = (glob A){m} /\ (glob B) = (glob B){m} ==> res.`2 = s0 /\ res.`1 = r ] 
 = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r].
proof. move => &m i s0 r. bypr.
move => &m0. move => e. byequiv (_: ={arg, glob A, glob B} ==> _).
proc.
seq 1 1 : (={rb, glob A}).
call Bsens2.
skip. auto. 
call (_:true).
skip. progress. progress. trivial.
qed.

local lemma yyy &m0 &m1 M a : (glob A){m0} = (glob A){m1} => Pr[QQ(A,B).main52(a) @ &m1 : M res.`1 /\ M res.`2] = Pr[QQ(A,B).main52(a) @ &m0 : M res.`1 /\ M res.`2]. 
move => q. byequiv. proc. 
inline*. wp. call(_:true). wp. call (_:true). call(_:true). call(_:true).  wp. skip. progress. smt.  auto. auto.
qed.

local lemma zzz &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    /\ islossless A.run
(*    /\ islossless B.init  *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ]).
elim (rewindable_A_plus A RewProp) .
progress.
exists f.
progress. apply ll_A_run. (* apply ll_B_run.*)
bypr.  move => &m1 eq.
have jk  : (glob A){m0} = (glob A){m1}. timeout 20.  smt.
elim eq. move => _ z. rewrite z.
apply (yyy &m0 &m1 ). auto.
qed.


local lemma qqq &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    /\ islossless A.run
(*    /\ islossless B.init *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 r, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = r ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(r) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 /\ res.`1 = r ] = 0%r))
    /\ forall &m M &n s0 i r , f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ QQ(A,B).main52(r) @ &n : M res.`1 /\ M res.`2 ].
proof.  
elim (zzz &m &n).
progress.
exists f.
progress. 
byphoare.
proc.
seq 1 : (f (glob A) = s0) 0%r 0%r 1%r 0%r (f (glob A) = s.`2). 
inline*. wp.
seq 2 : (true).
call (_:true). wp.  skip. auto.
conseq (_: exists q, q = glob A ==> _). smt.
elim*. move => q.
inline*. wp.
call (H1 q).
skip. smt.
hoare.
inline*.
wp.
seq 2 : (true). 
call (_:true). wp. skip. auto.
conseq (_: exists q, q = glob A ==> _). smt.
elim*. move => q.
call (H1 q).
skip. smt.
simplify.
hoare. call(_:true).
skip. smt. auto. auto. auto.
byphoare.
proc.
seq 1 : (f (glob A) = s0) 0%r 0%r 1%r 0%r (f (glob A) = s.`2). 
inline*. wp.
seq 2 : (true). 
call (_:true).  wp. skip. auto.
conseq (_: exists q, q = glob A ==> _). smt.
elim*. move => q.
inline*. wp.
call (H1 q).
skip. smt.
hoare.
inline*.
wp.
seq 2 : (true). sp.
call (_:true). skip. auto.
conseq (_: exists q, q = glob A ==> _). smt.
elim*. move => q.
call (H1 q).
skip. smt.
simplify.
hoare. call(_:true).
inline*.  wp.  call(_:true). wp. call(_:true). call(_:true).  call (_: true).  wp. skip. auto.
skip. smt. auto. auto. auto.
byphoare.
proc.
seq 1 : (true) 1%r 0%r 1%r 0%r . 
call (_:true).  skip. auto.
conseq (_: exists q, q = glob A ==> _). smt.
elim*. move => q.
hoare.
call (H1 q).
skip. smt. exfalso. auto.
auto. auto. auto.
byphoare (_ :  (arg = i) /\ (glob A) = (glob A){m0} /\ (glob B) = (glob B){m0} ==> _).
proc*.
inline QQ(A,B).main5.
pose x := (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 =  f (glob A){n0} /\ res.`1 = r]). 
pose y := (Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2]). simplify.
seq 2 : (s = (r, f (glob A){n0})) (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r ]) y (1%r - x) 0%r (f (glob A) = s.`2). sp.
inline*.
seq 2 : (i1 = i0). sp.
call (_: true).  skip. progress.
conseq (_: exists w, exists z, glob A = w /\ glob B = z /\ i1 = i0 ==>  i1 = i0 /\ f (glob A) = s.`2 /\ rb = s.`1).
smt. smt. elim*.  move => w z. wp.
conseq (_: _ ==> (glob A) = w  /\ s0 = f w /\ i1 = i0 /\ rb =  rb).
progress.
call (H1 w).
progress. 
call (www &m0  i (f (glob A){n0}) r). wp.
skip. progress.
simplify. smt.
have H8 : phoare[ QQ(A,B).main52 : f (glob A) =  f (glob A){n0} /\ arg = r ==> M res.`1 /\ M res.`2] = Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2 ]. apply (H6 &n0). auto.
have q1 : Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2] = y. auto.
have q3 : phoare[ QQ(A,B).main52 : f (glob A) =  f (glob A){n0} /\ arg = r ==> M res.`1 /\ M res.`2] = y.  rewrite - q1.
apply H8.
wp.
call q3.
skip. progress. 
wp. hoare. call(_:true). inline*.  wp.  call(_:true). wp. call(_:true). call(_:true).  call (_: true).  wp. skip. auto.
skip. progress.
smt.
smt.
auto. auto.
qed.

local lemma ooo &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    /\ islossless A.run
(*    /\ islossless B.init  *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 /\ res.`1 = r ] = 0%r))    
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ]).
proof.  
elim (qqq &m &n). progress. exists f. progress .
have eq :  Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2] = Pr[ GetRunSetRunConj(A).main(r) @ &n0 : M res.`1 /\ M res.`2 ].
byequiv;auto.
proc. inline*.  wp. call (_:true). wp. call(_:true). call(_:true). call(_:true). wp. skip. progress.
have eq2 : Pr[QQ(A,B).main5(i) @ &m0 : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = f (glob A){n0} /\ res.`2.`1 = r] = Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r] * Pr[QQ(A,B).main52(r) @ &n0 : M res.`1 /\ M res.`2].
rewrite   (H10 &m0 M &n0).  by reflexivity.
auto.
rewrite eq2 eq.
rewrite (dbl_main_no_number A ).
apply RewProp. 
smt.
qed.

local lemma ppp &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    /\ islossless A.run
(*    /\ islossless B.init *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 /\ res.`1 = r ] = 0%r))    
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])      
    /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ]).
proof.  elim (ooo &m &n). progress. exists f. progress. 
byphoare (_ : (arg = i) /\ (glob A) = (glob A){m0} /\ (glob B) = (glob B){m0} ==> _).
proc*.
inline QQ(A,B).main6.
pose x := (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r]).
pose y := (Pr[A.run(r) @ &n0 : M (r, res)]). simplify.
seq 2 : (s.`2 = f (glob A){n0} /\ s.`1 = r) (Pr[QQ(A,B).main51(i) @ &m0 : res.`2 = f (glob A){n0} /\ res.`1 = r]) y (1%r - x) 0%r (f (glob A) = s.`2). sp.
inline*.
seq 1 : (i1 = i0).
 wp. skip. auto.
 seq 1 : (i1 = i0).
call (_:true). skip. auto.
conseq (_: exists w, exists z, glob A = w /\ glob B = z   ==>  _).
smt. progress. elim*.  move => w z. wp.
conseq (_: _ ==> (glob A) = w  /\ s0 = f w ).
progress.
call (H1 w).  skip.
progress.
call (www &m0 i (f (glob A){n0}) r).
simplify. wp.
skip. progress.
wp.
simplify.
have q2 : forall &n0, f (glob A){n0} = f (glob A){n0} => phoare[ A.run : arg = r /\ f (glob A) = f (glob A){n0} ==> M (r, res)] = Pr[A.run(r) @ &n0 : M (r, res)]. 
move => &no eq. bypr. move => &mo eq2. byequiv.
proc*. call (_:true). skip. progress.  smt. smt. smt. smt.
have q1 : Pr[A.run(r) @ &n0 : M (r, res)] = y. auto.
have q3 : phoare[ A.run : arg = r /\ f (glob A) = f (glob A){n0} ==> M (r, res)] = y.  rewrite - q1.
apply (q2 &n0).
auto.
call q3.
skip. progress. smt.
wp. hoare. call(_:true). inline*.  wp.  
skip. smt.
simplify.
smt. auto. 
auto.
qed.


local lemma bigLemma ['a] (f : 'a -> real) : forall l x,  big predT f (x :: l) = f x + big predT f l.
proof. apply list_ind. smt. move => x l ih. simplify. smt.
qed.


local lemma lll &m P i : forall (M : sbits list), uniq M =>
  Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2.`2 \in M) ] 
  = big predT  (fun x => Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2.`2 = x) ]) M.
proof. apply list_ind.
simplify. rewrite Pr[mu_false]. smt.
simplify.   
move => x l ih. 
rewrite (bigLemma (fun (x0 : sbits) => Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 = x0]) l x). simplify.
elim.
move => ne un.
rewrite - ih. apply un.
have qq : Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2.`2 = x \/ (res.`2.`2 \in l))]
        = Pr[QQ(A,B).main5(i) @ &m : (P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 = x) \/ (P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 \in l)] .
rewrite Pr[ mu_eq ]. smt. auto.
rewrite qq.
rewrite Pr[ mu_disjoint ]. smt.
auto.
qed.

local lemma nnn &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    /\ islossless A.run
(*    /\ islossless B.init *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0 /\ res.`1 = r ] = 0%r))
    /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall P i (M : (irt * sbits) list), uniq M =>
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in M)  ]
      = big predT (fun (x : irt * sbits) =>   Pr[ QQ(A,B).main51(i) @ &m : res = x  ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )) * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )))                    M).
proof. elim (ppp &m &n). progress. exists f. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption.
split. assumption. split. assumption. split. assumption.  split. assumption. 
move => P i. apply list_ind. simplify. rewrite Pr[mu_false]. smt.
simplify.
move => x l ih.
elim. move=> xl ul.
have qq : Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 = x \/ (res.`2 \in l))]
        = Pr[QQ(A,B).main5(i) @ &m : (P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x) \/ (P res.`1.`1 /\ P res.`1.`2 /\ res.`2 \in l)] .
rewrite Pr[ mu_eq ]. smt. auto.
have ->: Pr[QQ(A, B).main5(i) @ &m :
   P res.`1.`1 /\
   P res.`1.`2 /\ (res.`2 = x \/ (res.`2 \in l)) ] 
  = Pr[QQ(A, B).main5(i) @ &m :
       P res.`1.`1 /\
       P res.`1.`2 /\ (res.`2 = x  \/ (res.`2 \in l))].
rewrite Pr[mu_eq]. smt. auto.
rewrite qq.
rewrite Pr[ mu_disjoint ]. smt.
pose E (x0 : irt * sbits) :=  (fun (y : real) =>
          exists &l, f (glob A){l} = x0.`2 /\ Pr[A.run(x0.`1) @ &l : P (x0.`1, res)] = y).
rewrite (bigLemma (fun (x0 : irt * sbits) =>
     Pr[QQ(A,B).main51(i) @ &m : res = x0] *
     some_real
       (E x0) *
     some_real
       (E x0)) l x). 
simplify.
simplify.
rewrite - ih. apply  ul.
have : Pr[QQ(A,B).main51(i) @ &m : res = x ] *
some_real (E x) *
some_real (E x) = Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x ].
case (exists &l, f (glob A){l} = x.`2).
elim. move => &lk lp.
have : E x (some_real (E x)).
apply (some_real_prop (E x)).
exists (Pr[ A.run(x.`1) @ &lk : P (x.`1, res) ]).
split. progress. simplify E. exists &lk.
smt.
move => q. elim.
move => &l0.
elim.
move => o1 o2.    rewrite - o2.
byequiv.  proc*. call (_:true). skip. progress. smt. smt. smt.
elim.
move => &l. elim.
move => c eq.
rewrite - eq.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x]
     = Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1 ] . rewrite Pr[mu_eq]. smt. auto.
rewrite (H10  &m &l  P x.`2 i ).
 smt.  auto.  
move => dnem.
have : (forall &n0, f (glob A){n0} <> x.`2). smt.
move => prr.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt. auto.
have ->: Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 = x]
     = Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1 ] . rewrite Pr[mu_eq]. smt. auto.     
rewrite (H9 x.`2). apply prr.
rewrite (H8 x.`2). apply prr.
auto.
move => opp.
rewrite opp.
auto.
qed.


local lemma jjj &m &n : exists (f : glob A -> sbits),
       injective f 
    /\ (forall (x : glob A),
         phoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ] = 1%r) 
    /\ (forall (x : glob A),
         hoare[ A.getState : (glob A) = x ==> (glob A) = x  /\ res = f x ]) 
    /\ (forall (x: glob A),
         phoare[A.setState: b = f x ==> glob A = x] = 1%r)
    /\ (forall (x: glob A),
         hoare[A.setState: b = f x ==> glob A = x])
    /\ islossless A.setState
    /\ islossless A.run
(*    /\ islossless B.init  *)
    (* assumptions above, payload below *)
    /\ (forall &m M s0 a, f (glob A){m} = s0 => 
         phoare [ QQ(A,B).main52 : f (glob A) = s0 /\ arg = a ==> M res.`1 /\ M res.`2  ] 
       = Pr[ QQ(A,B).main52(a) @ &m : M res.`1 /\ M res.`2  ])
    /\ (forall s0 r, (forall &n, f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m M i, Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] = 0%r))
    /\ (forall s0 r, (forall &n , f (glob A){n} <> s0) => 
         (forall &m i, Pr[ QQ(A,B).main51(i) @ &m :  res.`2 = s0  /\ res.`1 = r ] = 0%r))    
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])      
    /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main6(i) @ &m : M res.`1 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
      = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall &m &n M s0 i r, f (glob A){n} = s0 => 
        Pr[ QQ(A,B).main5(i) @ &m : M res.`1.`1 /\ M res.`1.`2 /\ res.`2.`2 = s0 /\ res.`2.`1 = r ] 
        = Pr[ QQ(A,B).main51(i) @ &m : res.`2 = s0 /\ res.`1 = r ] * Pr[ A.run(r) @ &n : M (r, res) ] * Pr[ A.run(r) @ &n : M (r, res) ])
   /\ (forall P i (M : (irt * sbits) list), uniq M =>
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in M)  ]
      = big predT (fun (x : irt * sbits) =>   Pr[ QQ(A,B).main51(i) @ &m : res = x  ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )) * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )))                    M)
  /\   (forall P i (M : (irt * sbits) list) , uniq M =>
      Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M) ]
      = big predT (fun x =>   Pr[ QQ(A,B).main51(i) @ &m : res = x ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ]  = y )))                    M).
elim (nnn &m &n). progress. exists f. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption. split. assumption. split. assumption. split. assumption.
split. assumption.
split. assumption. split. assumption. split. assumption.  split. assumption. split. assumption.
move => P i.
apply list_ind. simplify. rewrite Pr[mu_false]. smt.
simplify.
move => x l ih .
elim. move=> xl ul.
have : Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 = x \/ (res.`2 \in l))  ]
        = Pr[QQ(A,B).main6(i) @ &m : (P res.`1 /\ res.`2 = x ) \/ (P res.`1 /\ res.`2 \in l ) ].
rewrite Pr[ mu_eq ]. smt. auto.
move => qq. rewrite qq.
rewrite Pr[ mu_disjoint ]. smt.
pose E (x0 : irt * sbits) :=  (fun (y : real) =>
          exists &l, f (glob A){l} = x0.`2 /\ Pr[A.run(x0.`1) @ &l : P (x0.`1, res)] = y).
rewrite  (bigLemma (fun (x0 : (irt * sbits)) =>
     Pr[QQ(A,B).main51(i) @ &m : res = x0] *
     some_real
       (E x0)) l x). 
simplify.
simplify.
rewrite - ih. apply  ul.
have : Pr[QQ(A,B).main51(i) @ &m : res = x] *
some_real (E x) = Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ res.`2 = x ].
case (exists &l, f (glob A){l} = x.`2).
elim. move => &lk lp.
have : E x (some_real (E x)).
apply (some_real_prop (E x)).
exists (Pr[ A.run(x.`1) @ &lk : P (x.`1, res) ]).
split. progress. simplify E. exists &lk.
smt.
move => q. elim.
move => &l0.
elim.
move => o1 o2.    rewrite - o2.
byequiv. proc*. call(_:true). skip. progress. smt. smt. smt.
elim.
move => &l. elim.
move => c eq.
rewrite - eq.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt. auto.   
have ->: Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2 = x] = Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1].  rewrite Pr[mu_eq]. smt. auto.   
rewrite (H11 &m &l P  x.`2 i ).
smt.  smt.
move => dnem.
have : (forall &n0, f (glob A){n0} <> x.`2). smt.
move => prr.
have ->: Pr[QQ(A, B).main51(i) @ &m : res = x] = Pr[QQ(A, B).main51(i) @ &m : res.`2 = x.`2 /\ res.`1 = x.`1].  rewrite Pr[mu_eq]. smt. auto.   
have ->: Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2 = x] = Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ res.`2.`2 = x.`2 /\ res.`2.`1 = x.`1].  rewrite Pr[mu_eq]. smt. auto.      
rewrite (H9 x.`2). apply prr.
rewrite (H7 x.`2). apply prr.
smt.
move => opp.
rewrite opp.
auto.
qed.



local lemma pop &m :
  forall P (M : (irt * sbits) list) i, uniq M =>
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in M) ] >= (Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M) ])^2 .
proof. elim (jjj &m &m). progress.
have : forall (M : (irt * sbits) list), uniq M =>
   (big predT
 (fun x => Pr[ QQ(A,B).main51(i) @ &m : res = x ] 
    * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\ Pr[ A.run(x.`1) @ &l : P (x.`1, res) ] = y)) 
    * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\ Pr[ A.run(x.`1) @ &l : P (x.`1, res) ] = y)))
  M)
   >= (big predT (fun x =>   Pr[ QQ(A,B).main51(i) @ &m : res = x ] * (some_real (fun y => exists &l, f (glob A){l} = x.`2 /\  Pr[ A.run(x.`1) @ &l : P (x.`1, res) ] = y))) M)^2.
move => M0 uM0.
apply (jen_big_spec2 (((fun (x : irt * sbits) =>
     Pr[QQ(A, B).main51(i) @ &m : res = x]))) (fun (x: irt * sbits) => some_real
       (fun (y : real) =>
          exists &l, f (glob A){l} = x.`2 /\ Pr[A.run(x.`1) @ &l : P (x.`1, res)] = y)) M0).
auto.
split. move => x. simplify. rewrite Pr[mu_ge0]. auto.
have : forall (s : (irt * sbits) list),
  uniq s =>
  big predT (fun (x : irt * sbits) => Pr[QQ(A, B).main51(i) @ &m : res = x]) s
  = Pr[QQ(A, B).main51(i) @ &m : mem s res].
apply list_ind. simplify. rewrite Pr[mu_false]. smt.
simplify. move => x l ih lpr.
 rewrite zkj. simplify.
rewrite Pr[mu_disjoint]. smt.
rewrite ih. smt. auto.
move => ke. move => s us. rewrite ke. auto. rewrite Pr[mu_le1]. auto.
move => jen.
rewrite (H13 P i M). auto.
rewrite (H14 P i M). auto.
auto. apply jen. auto.
qed.



local lemma derv2 P &m i : forall epsilon, epsilon > 0%r => exists (M : (irt * sbits) list), uniq M /\
     Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ res.`2 \in M ]^2
   >= Pr[ QQ(A,B).main6(i) @ &m : P res.`1 ]^2 - 2%r * epsilon.
proof. move => epsilon eps_prop.
elim (sga &m i epsilon eps_prop). move => M. simplify.
move => pr1.
exists M.
have : Pr[QQ(A,B).main6(i) @ &m : P res.`1] = Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M)]  + Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ !(res.`2 \in M)].
rewrite Pr[mu_split (res.`2 \in M)]. auto.
move => split_eq.
have : Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M)] = Pr[QQ(A,B).main6(i) @ &m : P res.`1] - Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ ! (res.`2 \in M)].
smt.
move => eq2.
rewrite eq2.
have : Pr[QQ(A,B).main6(i) @ &m : P res.`1] <= 1%r. rewrite Pr[mu_le1]. auto.
have : Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ ! (res.`2 \in M)] <= 1%r. rewrite Pr[mu_le1]. auto.
move => h1 h2 .
progress.
smt.
pose x := Pr[QQ(A,B).main6(i) @ &m : P res.`1].
pose y := Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ ! (res.`2 \in M)].
have : y < epsilon.
  have : Pr[QQ(A, B).main6(i) @ &m : P res.`1 /\ ! (res.`2 \in M)] <= Pr[QQ(A, B).main6(i) @ &m : ! (res.`2 \in M)]. rewrite Pr[mu_sub]. progress. auto.
  move => z.
  smt.
move => ioi.
have : (x - y) ^ 2 = x * x - 2%r * x * y + y * y.
smt.
move => q. rewrite q. clear q.
have : x ^ 2 = x * x. smt.
move => q. rewrite q. clear q.
have multbysmall : forall (a b : real), a <= 1%r => b >= 0%r =>  a * b <= b.
smt.
have : x <= 1%r => 0%r <= y <= epsilon => epsilon >= x * y. smt.
move => q.
smt.
qed.


local lemma derv3 P &m i : forall epsilon,  epsilon > 0%r =>
      Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ]
   >= Pr[ QQ(A,B).main6(i) @ &m : P res.`1 ]^2 - 2%r * epsilon.
proof.  move => epsilon eps_prop.
elim (derv2 P &m  i epsilon eps_prop).
move => M.
elim. move => ul eq.
have :  Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ] >=  Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 \in M ].
rewrite Pr[mu_sub]. progress. auto.
move => eq2.
have :   Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ] >=  Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 \in M ].
smt.
move => eq3. clear eq2.
have : Pr[QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ (res.`2 \in M)] >= Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ res.`2 \in M ]^2.
  have : Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ res.`2 \in M ] ^2 = Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ res.`2 \in M ] * Pr[ QQ(A,B).main6(i) @ &m : P res.`1 /\ res.`2 \in M ]. smt. move => eq41. rewrite eq41. clear eq41.
have : Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M)] *
Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M)] = Pr[QQ(A,B).main6(i) @ &m : P res.`1 /\ (res.`2 \in M)] ^ 2.
smt.
move => kk. rewrite kk.
apply (pop &m P M i ul).
move => eq4.
smt.
qed.


local lemma derv_final P &m i :
   Pr[ QQ(A,B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2 ] >= Pr[ QQ(A,B).main6(i) @ &m : P res.`1 ]^2.
proof.  apply sm_than.
move => e ep.
have ep2 : 0%r < 1%r / 2%r * e. smt.
have :
  Pr[QQ(A, B).main6(i) @ &m : P res.`1] ^ 2 - 2%r * (1%r / 2%r * e) <=
  Pr[QQ(A, B).main5(i) @ &m : P res.`1.`1 /\ P res.`1.`2].
 apply (derv3 P &m i (1%r/2%r * e) ep2).
simplify.
move => q. smt.
qed.


lemma rew_with_init_alternative P &m i :
   Pr[ QQ(A,B).main(i) @ &m : P res.`1 /\ P res.`2 ] >= Pr[ QQ(A,B).main_run(i) @ &m : P res ]^2.
have q : Pr[ QQ(A,B).main(i) @ &m : P res.`1 /\ P res.`2 ] >= Pr[ QQ(A,B).main_run'(i) @ &m : P res ]^2.
rewrite - intlem1 - intlem2. apply derv_final.
have p : Pr[ QQ(A,B).main_run'(i) @ &m : P res ] = Pr[ QQ(A,B).main_run(i) @ &m : P res ].
elim (rewindable_A_plus A RewProp) . progress.
byequiv (_: (={i,glob A, glob B}) ==> _). proc.
seq 1 1 : (={r0, glob A}). call Bsens2. skip. auto.
call (_:true).
conseq (_: exists ga, ga = (glob A){1} /\ ={r0, glob A} ==> _). smt.
elim*. move => ga.
call {1} (H0 ga). skip. progress. auto.  auto.
rewrite - p.
apply q.
qed.


end section.
end RWI.
