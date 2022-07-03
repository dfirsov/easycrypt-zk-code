pragma Goals:printall.

require import AllCore Distr Real DBool.
require RewBasics.

theory RSBH.

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



module type Initializer = {
  proc init(i:iat) : irt
}.


module type RewRunExec1Exec2 = {
  proc getState() : sbits
  proc * setState(b : sbits) : unit 
  proc run(i : irt) : rrt
  proc ex1(i : irt) : rrt
  proc ex2(i : irt) : rrt
}.


module SBB (A : RewRunExec1Exec2) = {
  proc run(i : irt) = {
    var r, x;
    x <$ {0,1};    
    if (x) {
      r <@ A.ex1(i);
    }else{
      r <@ A.ex2(i);
    }
     return r;
  }    

  proc getState() : sbits = {
    var s;
    s <@ A.getState();
    return s;
  }
  proc setState(b : sbits) : unit  = {
    A.setState(b);
  }
}.

module SB (A : RewRunExec1Exec2, B : Initializer) = {
  module SBB = SBB(A)

  proc main(i:iat) = {
    var s,ix,r1,r2;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ SBB.run(ix);
    A.setState(s);
    r2 <@ SBB.run(ix);
    return (r1 , r2);
  }

  proc main_run(i:iat) = {
    var ix,r;
    ix <@ B.init(i);
    r <@ SBB.run(ix);
    return r;
  }
  
  proc main_12(i:iat) = {
    var s,ix,r1,r2;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex1(ix);
    A.setState(s);
    r2 <@ A.ex2(ix);
    return (r1, r2);
  }
  
  proc main_21(i:iat) = {
    var s,ix,r1,r2;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex2(ix);
    A.setState(s);
    r2 <@ A.ex1(ix);
    return (r1, r2);
  }

  proc main_11(i:iat) = {
    var s,ix,r1,r2;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex1(ix);
    A.setState(s);
    r2 <@ A.ex1(ix);
    return (r1, r2);
  }

  proc main_22(i:iat) = {
    var s,ix,r1,r2;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex2(ix);
    A.setState(s);
    r2 <@ A.ex2(ix);
    return (r1, r2);
  }

  proc main_1(i:iat) = {
    var r,ix;
    ix <@ B.init(i);
    r <@ A.ex1(ix);
    return r;
  }

  proc main_2(i:iat) = {
    var r, ix;
    ix <@ B.init(i);
    r <@ A.ex2(ix);
    return r;
  }
}.


section.
declare module A <: RewRunExec1Exec2.
declare module B <: Initializer.

axiom Afl : islossless A.ex1.
axiom Agl : islossless A.ex2.
axiom Ass : islossless A.setState.
axiom Bsens : equiv[ B.init ~ B.init : ={i, glob A, glob B} ==> ={glob A, res} ].


local module M = {
  var x1, x2 : bool
  proc run(i : irt) = {
    var r, x;
    x <$ {0,1};    
    if (x) {
      r <@ A.ex1(i);
    }else{
      r <@ A.ex2(i);
    }
   return (r,x);
  }  

  proc main(i:iat) = {
    var ix, r1, r2, s;
    ix <@ B.init(i);
    s <@ A.getState();
    (r1, x1) <@ run(ix);
    A.setState(s);
    (r2, x2) <@ run(ix);
    return (r1,r2);
  } 

  proc main_12(i:iat) = {
    var ix,r1, r2, s;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex1(ix);
    A.setState(s);
    r2 <@ A.ex2(ix);
    return (r1, r2);
  }

  proc main_12'(i:iat) = {
    var r;
    x1 <$ {0,1};
    x2 <$ {0,1};
    r <@ main_12(i);
    return (r , x1 /\ !x2);
  }  

  proc main_11(i:iat) = {
    var ix, r1, r2, s;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex1(ix);
    A.setState(s);
    r2 <@ A.ex1(ix);
    return (r1 , r2);
  }
  
  proc main_11'(i:iat) = {
    var r;
    x1 <$ {0,1};
    x2 <$ {0,1};
    r <@ main_11(i);
    return (r, x1 /\ x2);
  }  

  proc main_21(i:iat) = {
    var ix, r1, r2, s;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex2(ix);
    A.setState(s);
    r2 <@ A.ex1(ix);
    return (r1, r2);
  }
  
  proc main_21'(i:iat) = {
    var r;
    x1 <$ {0,1};
    x2 <$ {0,1};
    r <@ main_21(i);
    return (r, !x1 /\ x2);
  }  

  proc main_22(i:iat) = {
    var ix,r1, r2, s;
    ix <@ B.init(i);
    s <@ A.getState();
    r1 <@ A.ex2(ix);
    A.setState(s);
    r2 <@ A.ex2(ix);
    return (r1,r2);
  }
  
  proc main_22'(i:iat) = {
    var r;
    x1 <$ {0,1};
    x2 <$ {0,1};
    r <@ main_22(i);
    return (r, !x1 /\ !x2);
  }  

  proc main_run(i:iat) = {
    var ix, r;
    ix <@ B.init(i);
    (r,x1) <@ run(ix);
    return r;
  }

  proc main_1(i:iat) = {
    var ix,r;
    ix <@ B.init(i);
    r <@ A.ex1(ix);
    return r;
  }

  proc main_1'(i:iat) = {
    var r;
    x1 <$ {0,1};
    r <@ main_1(i);
    return (r, x1);
  }  

  proc main_2(i:iat) = {
    var ix, r;
    ix <@ B.init(i);
    r <@ A.ex2(ix);
    return r;
  }

  proc main_2'(i:iat) = {
    var r;
    x1 <$ {0,1};
    r <@ main_2(i);
    return (r, !x1);
  }  
}.


local lemma vau_uav_1 P : equiv [ M.main_run ~ M.main_1' : ={i, glob A, glob B} 
                                ==> P res{1} /\ M.x1{1}  <=> P res{2}.`1 /\ res{2}.`2 ].
proof. proc. inline*.
swap {2} [2..3] -1. sp.
seq 1 1 : (={glob A, ix}). call Bsens. skip.   progress.  sp.
seq 1 1 : (i0{1} = ix{2} /\ ={glob A, ix} /\ x{1} = M.x1{2}).
rnd. skip. progress.
if {1}.
wp. seq 1 1 : (={glob A, r0} /\ x{1} = M.x1{2}).
call(_:true). skip. progress. skip. progress.
wp. call {2} (_: true ==> true). apply Afl.
call {1} (_: true ==> true). apply Agl. skip. progress.
qed.
local lemma probEq_1 &m P i : Pr[ M.main_run(i) @ &m :  P res /\ M.x1 ] = Pr[ M.main_1'(i) @ &m : P res.`1 /\ res.`2 ].
proof. byequiv. conseq (vau_uav_1 P). progress. smt. smt. auto. auto.
qed.
local lemma bitsout_1 &m P j : Pr[ M.main_1'(j) @ &m : P res.`1 /\ res.`2 ] = Pr[ M.main_1(j) @ &m : P res ] / 2%r.
proof.
byphoare (_: arg = j /\  (glob A) = (glob A){m} /\ (glob B) = (glob B){m} ==> _).
proc.
pose z := Pr[ M.main_1(j) @ &m : P res ].
seq 1 : (M.x1) (1%r/2%r) z (1%r - 1%r/2%r) 0%r ((glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j).
rnd.  skip. progress.
rnd.  skip. smt.
conseq (_: ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P r). smt. smt.
have phl : phoare [ M.main_1 : ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ arg = j ==> P res ] 
           = Pr[ M.main_1(j) @ &m : P res ].
bypr. move => &m0  pr1.
byequiv (_: ={i, glob A, glob B} /\ i{1} = j  ==> _). proc. seq 1 1 : (={glob A, ix}). call Bsens.
skip. progress.  
call (_:true). skip.  smt.  progress. smt.  smt. smt. auto. smt.  auto.
call phl. skip. auto. progress. 
inline*. wp. hoare. call (_:true). call(_:true).  wp.
skip. smt. smt. auto. auto.
qed.
local lemma main_lemma_1 &m P i : Pr[ M.main_run(i) @ &m :  P res /\ M.x1 ]
                             = Pr[ M.main_1(i) @ &m : P res ] / 2%r.
proof. rewrite probEq_1. rewrite bitsout_1. auto.
qed.


local lemma vau_uav_2 P  : equiv [ M.main_run ~ M.main_2' : ={glob A, glob B, i} 
                                 ==> P res{1} /\ !M.x1{1} <=> P res{2}.`1 /\ res{2}.`2 ].
proof. proc. inline*.
swap {2} [2..3] -1.
seq 1 2 : (={glob A, ix}). sp. call Bsens. skip. auto. sp.
seq 1 1 : (i0{1} = ix{1} /\ ={glob A, ix} /\ x{1} = M.x1{2}).
rnd. skip. progress.
if {1}.
wp. call {2} (_: true ==> true). apply Agl.
call {1} (_: true ==> true). apply Afl. skip. progress.
wp. call (_:true). skip. progress.
qed.
local lemma probEq_2  &m P j : Pr[ M.main_run(j) @ &m :  P res /\ !M.x1 ] = Pr[ M.main_2'(j) @ &m : P res.`1 /\ res.`2 ].
proof. byequiv. conseq (vau_uav_2 P). progress. smt. smt. auto. auto.
qed.
local lemma bitsout_2 &m P j : Pr[ M.main_2'(j) @ &m : P res.`1 /\ res.`2 ] = Pr[ M.main_2(j) @ &m : P res ] / 2%r.
proof.
byphoare (_: i = j /\ (glob A) = (glob A){m} /\ (glob B) = (glob B){m} ==> _).
proc.
pose z := Pr[ M.main_2(j) @ &m : P res ].
seq 1 : (!M.x1) (1%r/2%r) z (1%r - 1%r/2%r) 0%r ((glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j).
rnd.  skip. progress.
rnd.  skip. smt.
conseq (_: ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P r). smt. smt.
have phl : phoare [ M.main_2 : ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P res ] 
           = (Pr[ M.main_2(j) @ &m : P res ]).
bypr. move => &m0  pr1.
byequiv (_: ={i,glob A, glob B} ==> _). proc. seq 1 1 : (={glob A,ix}). call Bsens.
skip. auto.
call (_:true). skip. smt. auto. auto. smt. auto.
call phl. skip. auto.
inline*. wp. hoare. call (_:true). call(_:true). wp. 
skip. smt. smt. auto. auto.
qed.
local lemma main_lemma_2 &m P j : Pr[ M.main_run(j) @ &m :  P res /\ !M.x1 ]
                             = Pr[ M.main_2(j) @ &m : P res ] / 2%r.
proof. rewrite probEq_2. rewrite bitsout_2. auto.
qed.


lemma fact3 &m P j : Pr[SB(A,B).main_run(j) @ &m : P res ] = 1%r / 2%r * Pr[SB(A,B).main_1(j) @ &m : P res ] 
                                                           + 1%r / 2%r * Pr[SB(A,B).main_2(j) @ &m : P res ].
proof.
have e0 : Pr[SB(A, B).main_run(j) @ &m : P res ] = Pr[M.main_run(j) @ &m : P res ].
byequiv (_: (={i, glob A, glob B}) ==> _). proc. inline*.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto. sp. wp.
seq 1 1 : (i0{2} = ix{2} /\ i0{1} = ix{1} /\ ={glob A, ix,x}). rnd. skip. progress.
if.  auto. call (_:true). skip. progress. call (_:true). skip. progress.
auto. auto.
have e1 : Pr[SB(A, B).main_1(j) @ &m : P res] = Pr[M.main_1(j) @ &m : P res].
byequiv (_: (={i,glob A, glob B}) ==> _). proc. inline*. seq 1 1 : (={glob A, ix}). 
call Bsens. skip. auto.  call (_:true). skip. progress.
auto.  auto.
have e2 : Pr[SB(A, B).main_2(j) @ &m : P res] = Pr[M.main_2(j) @ &m : P res].
byequiv (_: (={glob A, glob B,i}) ==> _). proc.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
call (_:true). skip. progress.
auto. auto.
rewrite e0 e1 e2.
rewrite Pr[mu_split M.x1]. rewrite main_lemma_1. rewrite main_lemma_2. smt. 
qed.


local lemma vau_22 P : equiv [ M.main ~ M.main_22' : ={arg, glob A, glob B} 
                       ==> P res{1}.`1 /\ P res{1}.`2 /\ !M.x1{1} /\ !M.x2{1} => P res{2}.`1.`1 /\ P res{2}.`1.`2 /\ res{2}.`2 ].
proof. proc.  inline*. wp.
swap {1} 4 -2.
swap {1}  9 -6.
swap {2} [3..4] -2. sp.
seq 1 1 : (={glob A, ix} ). call Bsens. skip. auto.
seq 3 3 : (={ix,glob A, s} /\ x{1} = M.x1{2} /\ x0{1} = M.x2{2}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{1}.
seq 3 2 : (M.x1{1}).
wp. call(_:true). wp. call {1} (_: true ==> true). apply Afl.
call {2} (_: true ==> true). apply Agl. skip. progress. sp.
if{1}.  call {1} (_:true ==> true). apply Afl.
call {2} (_:true ==> true). apply Agl.
skip. smt.
call {1} (_:true ==> true). apply Agl.
call {2} (_:true ==> true). apply Agl.
skip. progress.
seq 3 2 : (={ix, glob A, r1, M.x1} /\ !M.x1{1} /\  x0{1} = M.x2{2}).
call (_:true). wp.
call (_:true).
skip. progress. sp.
if{1}.
call {1} (_:true ==> true). apply Afl.
call {2} (_:true ==> true). apply Agl.
skip. smt.
call(_:true). skip. auto.
qed.
local lemma uav_22 P : equiv [ M.main_22' ~ M.main : ={arg, glob A, glob B} 
                             ==> P res{1}.`1.`1 /\ P res{1}.`1.`2 /\ res{1}.`2 => P res{2}.`1 /\ P res{2}.`2 /\ !M.x1{2} /\ !M.x2{2} ].
 proc.  inline*. wp.
swap {1} [3..4] -2. sp.
swap {2} 4 -2.
swap {2} 9 -6.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={ix, glob A, s} /\ x{2} = M.x1{1} /\ x0{2} = M.x2{1}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{2}.
seq 2 3 : (M.x1{1}).
wp. call(_:true). wp. call {2} (_: true ==> true). apply Afl.
call {1} (_: true ==> true). apply Agl. skip. progress. sp.
if{2}.  call {2} (_:true ==> true). apply Afl.
call {1} (_:true ==> true). apply Agl.
skip. progress.
call {1} (_:true ==> true). apply Agl.
call {2} (_:true ==> true). apply Agl.
skip. progress.
seq 2 3 : (={ix, glob A, r1, M.x1} /\ !M.x1{2} /\  x0{2} = M.x2{1}).
call (_:true). wp.
call (_:true).
skip. progress. sp.
if{2}.
call {2} (_:true ==> true). apply Afl.
call {1} (_:true ==> true). apply Agl.
skip. smt.
call(_:true). skip. auto.
qed.
local lemma probEq_22 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ !M.x2 ] 
                               = Pr[ M.main_22'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
proof.
have prle : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ !M.x2 ] 
         <= Pr[ M.main_22'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
byequiv. conseq (vau_22 P). smt.   progress. progress.
have prge : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ !M.x2 ] 
         >= Pr[ M.main_22'(j) @ &m : P res.`1.`1 /\ P res.`1.`2  /\ res.`2 ].
byequiv. conseq (uav_22 P). smt. progress. progress.
smt.
qed.
local lemma bitsout_22 &m P j : Pr[ M.main_22'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ] 
                               = Pr[ M.main_22(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof.
byphoare (_: arg = j /\ (glob A) = (glob A){m} /\ (glob B) = (glob B){m} ==> _).
proc.
pose z := Pr[ M.main_22(j) @ &m : P res.`1 /\ P res.`2 ].
seq 2 : (!M.x1 /\ !M.x2) (1%r/4%r) z (1%r - 1%r/4%r) 0%r ((glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j).
rnd. rnd. skip. progress.
seq 1 : (!M.x1) (1%r/2%r) (1%r/2%r) (1%r/2%r) (0%r). rnd. auto.
rnd. skip. progress. smt.
rnd.  skip. smt. rnd. skip. progress. smt.
smt.
conseq (_: ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P r.`1 /\ P r.`2). smt. smt.
have phl : phoare [ M.main_22 : arg = j /\ ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) ==> P res.`1 /\ P res.`2 ] 
         = (Pr[ M.main_22(j) @ &m : P res.`1 /\ P res.`2 ]).
bypr. move => &m0  pr1.
byequiv (_: ={arg, glob A, glob B} ==> _). proc. seq 1 1 : (={glob A, ix}). call Bsens.
skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. smt. auto. auto.
call phl. skip. auto.
inline*. wp. hoare. call (_:true). call(_:true). call(_:true). call(_:true). call(_:true).
wp. skip. smt. smt. auto. auto.
qed.
local lemma main_lemma_22 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ !M.x2 ]
                             = Pr[ M.main_22(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof.  rewrite probEq_22. rewrite bitsout_22. auto.
qed.
    

local lemma vau_21 P : equiv [ M.main ~ M.main_21' : ={arg, glob A, glob B} 
                             ==> P res{1}.`1 /\ P res{1}.`2 /\ !M.x1{1} /\ M.x2{1} => P res{2}.`1.`1 /\ P res{2}.`1.`2 /\ res{2}.`2 ].
proof. proc.  inline*. wp.
swap {1} 4 -2.
swap {1}  9 -6.
swap {2} [3..4] -2. sp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={ix, glob A, s} /\ x{1} = M.x1{2} /\ x0{1} = M.x2{2}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{1}.
seq 3 2 : (i0{1} = ix{1} /\ M.x1{1}).
wp. call(_:true). wp. call {1} (_: true ==> true). apply Afl.
call {2} (_: true ==> true). apply Agl. skip. progress. sp.
if{1}.  call {1} (_:true ==> true). apply Afl.
call {2} (_:true ==> true). apply Afl.
skip. smt. call {1} (_:true ==> true). apply Agl.
call {2} (_:true ==> true). apply Afl.
skip. progress.
seq 3 2 : (={ix, glob A, r1, M.x1} /\ !M.x1{1} /\  x0{1} = M.x2{2}).
call (_:true). wp.
call (_:true).
skip. progress. sp.
if{1}. call(_:true). skip. progress.
call {1} (_:true ==> true). apply Agl.
call {2} (_:true ==> true). apply Afl.
skip. smt.
qed.
local lemma uav_21 P : equiv [ M.main_21' ~ M.main : ={arg, glob A, glob B} ==> P res{1}.`1.`1 /\ P res{1}.`1.`2 /\ res{1}.`2 => P res{2}.`1 /\ P res{2}.`2 /\ !M.x1{2} /\ M.x2{2} ].
proc.  inline*. wp.
swap {2} 4 -2.
swap {2}  9 -6.
swap {1} [3..4] -2. sp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={ix, glob A, s} /\ x{2} = M.x1{1} /\ x0{2} = M.x2{1}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{2}.
seq 2 3 : (i0{2} = ix{2} /\ M.x1{1}).
wp. call(_:true). wp. call {1} (_: true ==> true). apply Agl.
call {2} (_: true ==> true). apply Afl. skip. progress. sp.
if{2}.  call {2} (_:true ==> true). apply Afl.
call {1} (_:true ==> true). apply Afl.
skip. smt. call {2} (_:true ==> true). apply Agl.
call {1} (_:true ==> true). apply Afl.
skip. progress.
seq 2 3 : (={ix, glob A, r1, M.x1} /\ !M.x1{1} /\  x0{2} = M.x2{1}).
call (_:true). wp.
call (_:true).
skip. progress. sp.
if{2}. call(_:true). skip. progress.
call {1} (_:true ==> true). apply Afl.
call {2} (_:true ==> true). apply Agl.
skip. smt.
qed.
local lemma probEq_21 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ M.x2 ] 
                             = Pr[ M.main_21'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
proof.
have prle : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ M.x2 ] 
         <= Pr[ M.main_21'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
byequiv. conseq (vau_21 P). smt.   progress. progress.
have prge : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ M.x2 ] 
         >= Pr[ M.main_21'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
byequiv. conseq (uav_21 P). smt. progress. progress.
smt.
qed.
local lemma bitsout_21 &m P j : Pr[ M.main_21'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ] 
                              = Pr[ M.main_21(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof.
byphoare (_: i = j /\ (glob A) = (glob A){m} /\ (glob B) = (glob B){m} ==> _).
proc.
pose z := Pr[ M.main_21(j) @ &m : P res.`1 /\ P res.`2 ].
seq 2 : (!M.x1 /\ M.x2) (1%r/4%r) z (1%r - 1%r/4%r) 0%r ((glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j).
rnd. rnd. skip. progress.
seq 1 : (!M.x1) (1%r/2%r) (1%r/2%r) (1%r/2%r) (0%r). rnd. auto.
rnd. skip. progress. smt.
rnd.  skip. smt. rnd. skip. progress. smt.
smt.
conseq (_: (i = j /\ (glob A) = (glob A){m} /\ (glob B) = (glob B){m}) ==> P r.`1 /\ P r.`2). smt. smt.
have phl : phoare [ M.main_21 : ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P res.`1 /\ P res.`2 ] 
           = (Pr[ M.main_21(j) @ &m : P res.`1 /\ P res.`2 ]).
bypr. move => &m0  pr1.
byequiv (_: ={arg, glob A, glob B} ==> _). proc. seq 1 1 : (={glob A, ix}). call Bsens.
skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. smt. auto. auto. smt. auto.
call phl. skip. auto.
inline*. wp. hoare. call (_:true). call(_:true). call(_:true). call(_:true). call(_:true).
wp. skip. smt. smt. auto. auto.
qed.
local lemma main_lemma_21 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ !M.x1 /\ M.x2 ]
                             = Pr[ M.main_21(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof.  rewrite probEq_21. rewrite bitsout_21. auto.
qed.


local lemma vau_11 P : equiv [ M.main ~ M.main_11' : ={arg, glob A, glob B} 
                             ==> P res{1}.`1 /\ P res{1}.`2 /\ M.x1{1} /\ M.x2{1} => P res{2}.`1.`1 /\ P res{2}.`1.`2 /\ res{2}.`2 ].
proof. proc.  inline*. wp.
swap {1} 4 -2.
swap {1}  9 -6.
swap {2} [3..4] -2. sp. 
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={ix, glob A, s} /\ x{1} = M.x1{2} /\ x0{1} = M.x2{2}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{1}.
seq 3 2 : (i0{1} = ix{1}  /\ ={ix, glob A, r1, M.x1} /\ M.x1{1} /\  x0{1} = M.x2{2}).
call (_:true). wp. call(_:true). skip. progress. sp.
if{1}. call(_:true). skip.
progress.
call {1} (_:true ==> true). apply Agl.
call {2} (_:true ==> true). apply Afl.
skip. smt.
seq 3 2 : (i0{1} = ix{1}  /\ !M.x1{1}).
wp. call(_:true). wp. call {1} (_: true ==> true). apply Agl.
call {2} (_: true ==> true). apply Afl. skip. auto. sp.
if{1}. call {1} (_:true ==> true). apply Afl.
call {2} (_:true ==> true). apply Afl.
skip. smt. call {1} (_:true ==> true). apply Agl.
call {2} (_:true ==> true). apply Afl.
skip. progress.
qed.
local lemma uav_11 P : equiv [ M.main_11' ~ M.main : ={arg, glob A, glob B} 
                             ==> P res{1}.`1.`1 /\ P res{1}.`1.`2 /\ res{1}.`2 => P res{2}.`1 /\ P res{2}.`2 /\ M.x1{2} /\ M.x2{2} ].
proc. inline*.
swap {2} 4 -2.
swap {2}  9 -6.
swap {1} [3..4] -2. sp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={ix, glob A, s} /\ x{2} = M.x1{1} /\ x0{2} = M.x2{1}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{2}.
seq 2 3 :  (i0{2} = ix{2} /\ ={ix, glob A, r1, M.x1, s} /\ M.x1{1} /\  x0{2} = M.x2{1}).
call (_:true). wp. call(_:true). skip. smt. sp.
if{2}. wp.
call(_:true). skip. progress.
wp. call {1} (_:true ==> true). apply Afl. wp.
call {2} (_:true ==> true). apply Agl.
skip. smt.
wp.
seq 4 3 : (i0{2} = ix{2} /\ !M.x1{1}).
wp. call {2} (_: true ==> true). apply Ass.
wp. call {1} (_: true ==> true). apply Afl.
call {1} (_: true ==> true). apply Ass.
call {1} (_:true ==> true). apply Afl. wp.
call {2} (_:true ==> true). apply Agl.
skip. auto. sp.
if{2}.  wp. call {2} (_:true ==> true). apply Afl.
skip. progress. wp. call {2} (_:true ==> true). apply Agl.
skip. progress.
qed.
local lemma probEq_11 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ M.x2 ] 
                               = Pr[ M.main_11'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
proof.
have prle : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ M.x2 ] 
            <= Pr[ M.main_11'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
byequiv. conseq (vau_11 P). smt.   progress. progress.
have prge : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ M.x2 ] 
            >= Pr[ M.main_11'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
byequiv. conseq (uav_11 P). smt. progress. progress.
smt.
qed.
local lemma bitsout_11 &m P j : Pr[ M.main_11'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ] 
                                = Pr[ M.main_11(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof.
byphoare (_: (glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j ==> _).
proc.
pose z := Pr[ M.main_11(j) @ &m : P res.`1 /\ P res.`2 ].
seq 2 : (M.x1 /\ M.x2) (1%r/4%r) z (1%r - 1%r/4%r) 0%r ((glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j).
rnd. rnd. skip. progress.
seq 1 : (M.x1) (1%r/2%r) (1%r/2%r) (1%r/2%r) (0%r). rnd. auto.
rnd. skip. progress. smt.
rnd.  skip. smt. rnd. skip. progress. smt.
smt.
conseq (_: ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P r.`1 /\ P r.`2). smt. smt.
have phl : phoare [ M.main_11 : ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P res.`1 /\ P res.`2 ] 
           = (Pr[ M.main_11(j) @ &m : P res.`1 /\ P res.`2 ]).
bypr. move => &m0  pr1.
byequiv (_: ={glob A, glob B, i} /\ i{1} = j ==> _). proc. seq 1 1 : (={glob A, ix}). call Bsens.
skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. smt. auto. auto.  smt. auto.
call phl. skip. auto.
inline*. wp. hoare. call (_:true). call(_:true). call(_:true). call(_:true). call(_:true). wp.
skip. smt. smt. auto. auto.
qed.
local lemma main_lemma_11 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ M.x2 ]
                             = Pr[ M.main_11(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof. rewrite probEq_11. rewrite bitsout_11. auto.
qed.


local lemma vau_12 P : equiv [ M.main ~ M.main_12' : ={arg, glob A, glob B} 
                             ==> P res{1}.`1 /\ P res{1}.`2 /\ M.x1{1} /\ !M.x2{1} => P res{2}.`1.`1 /\ P res{2}.`1.`2 /\ res{2}.`2 ].
proof. proc.  inline*. wp.
swap {1} 4 -2.
swap {1}  9 -6.
swap {2} [3..4] -2. sp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={ix, glob A, s} /\ x{1} = M.x1{2} /\ x0{1} = M.x2{2}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{1}.
seq 3 2 : (i0{1} = ix{1} /\ ={ix, glob A, r1, M.x1} /\ M.x1{1} /\  x0{1} = M.x2{2}).
call (_:true). wp. call(_:true). skip. progress. sp.
if{1}.
call {1} (_:true ==> true). apply Afl.
call {2} (_:true ==> true). apply Agl.
skip. smt.
call (_:true).
skip. smt.
seq 3 2 : (i0{1} = ix{1}  /\ !M.x1{1}).
wp. call(_:true). wp. call {1} (_: true ==> true). apply Agl.
call {2} (_: true ==> true). apply Afl. skip. auto. sp.
if{1}.  call {1} (_:true ==> true). apply Afl.
call {2} (_:true ==> true). apply Agl.
skip. smt. call {1} (_:true ==> true). apply Agl.
call {2} (_:true ==> true). apply Agl.
skip. progress.
qed.
local lemma uav_12 P : equiv [ M.main_12' ~ M.main : ={arg, glob A, glob B} 
                             ==> P res{1}.`1.`1 /\ P res{1}.`1.`2 /\ res{1}.`2 => P res{2}.`1 /\ P res{2}.`2 /\ M.x1{2} /\ !M.x2{2} ].
proc. inline*.
swap {2} 4 -2.
swap {2}  9 -6.
swap {1} [3..4] -2. sp. 
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={ix, glob A, s} /\ x{2} = M.x1{1} /\ x0{2} = M.x2{1}).
call(_:true).
rnd. rnd. skip. smt. sp.
if{2}.
seq 2 3 :  (i0{2} = ix{2} /\ ={ix, glob A, r1, M.x1, s} /\ M.x1{1} /\  x0{2} = M.x2{1}).
call (_:true). wp. call(_:true). skip. smt. sp.
if{2}. wp.
call {1} (_:true ==> true). apply Agl. wp.
call {2} (_:true ==> true). apply Afl.
skip. smt.
wp. call (_:true).
skip. smt.
seq 4 3 : (!M.x1{1}).
wp. call {2} (_: true ==> true). apply Ass.
wp. call {1} (_: true ==> true). apply Agl.
call {1} (_: true ==> true). apply Ass.
call {1} (_:true ==> true). apply Afl. wp.
call {2} (_:true ==> true). apply Agl.
skip. auto. sp.
if{2}.  wp. call {2} (_:true ==> true). apply Afl.
skip. progress. wp. call {2} (_:true ==> true). apply Agl.
skip. progress.
qed.
local lemma probEq_12 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ !M.x2 ] 
                               = Pr[ M.main_12'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
proof.
have prle : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ !M.x2 ] 
            <= Pr[ M.main_12'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
byequiv. conseq (vau_12 P). smt.   progress. progress.
have prge : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ !M.x2 ] 
            >= Pr[ M.main_12'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ].
byequiv. conseq (uav_12 P). smt. progress. progress.
smt.
qed.
local lemma bitsout_12 &m P j : Pr[ M.main_12'(j) @ &m : P res.`1.`1 /\ P res.`1.`2 /\ res.`2 ] 
                                = Pr[ M.main_12(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof.
byphoare (_: (glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j ==> _).
proc.
pose z := Pr[ M.main_12(j) @ &m : P res.`1 /\ P res.`2 ].
seq 2 : (M.x1 /\ !M.x2) (1%r/4%r) z (1%r - 1%r/4%r) 0%r ((glob A) = (glob A){m} /\ (glob B) = (glob B){m} /\ i = j).
rnd. rnd. skip. progress.
seq 1 : (M.x1) (1%r/2%r) (1%r/2%r) (1%r/2%r) (0%r). rnd. auto.
rnd. skip. progress. smt.
rnd.  skip. smt. rnd. skip. progress. smt.
smt.
conseq (_: ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P r.`1 /\ P r.`2). smt. smt.
have phl : phoare [ M.main_12 : ((glob A) = (glob A){m} /\ (glob B) = (glob B){m}) /\ i = j ==> P res.`1 /\ P res.`2 ] 
           = (Pr[ M.main_12(j) @ &m : P res.`1 /\ P res.`2 ]).
bypr. move => &m0  pr1.
byequiv (_: ={glob A, glob B, arg} ==> _). proc. seq 1 1 : (={glob A, ix}). call Bsens.
skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. smt. auto. auto. smt. auto.
call phl. skip. auto.
inline*. wp. hoare. call (_:true). call(_:true). call(_:true). call(_:true). call(_:true).
wp. skip. smt. smt. auto. auto.
qed.
local lemma main_lemma_12 &m P j : Pr[ M.main(j) @ &m :  P res.`1 /\ P res.`2 /\ M.x1 /\ !M.x2 ]
                             = Pr[ M.main_12(j) @ &m : P res.`1 /\ P res.`2 ] / 4%r.
proof. rewrite probEq_12. rewrite bitsout_12. auto.
qed.


local lemma main_lemma &m P j : Pr[ M.main(j) @ &m : P res.`1 /\ P res.`2 ]
  = 1%r/4%r * Pr[ M.main_12(j) @ &m : P res.`1 /\ P res.`2 ]
  + 1%r/4%r * Pr[ M.main_21(j) @ &m : P res.`1 /\ P res.`2 ]
  + 1%r/4%r * Pr[ M.main_11(j) @ &m : P res.`1 /\ P res.`2 ]
  + 1%r/4%r * Pr[ M.main_22(j) @ &m : P res.`1 /\ P res.`2 ].
proof.
rewrite Pr[mu_split M.x1]. rewrite Pr[mu_split M.x2].
have : Pr[M.main(j) @ &m : (P res.`1 /\ P res.`2) /\ !M.x1] = Pr[M.main(j) @ &m : P res.`1 /\ P res.`2 /\ !M.x1 /\ M.x2]
 + Pr[M.main(j) @ &m : P res.`1 /\ P res.`2 /\ !M.x1 /\ !M.x2].
rewrite Pr[mu_split M.x2].  auto.
have z : Pr[M.main(j) @ &m : ((P res.`1 /\ P res.`2) /\ !M.x1) /\ M.x2] = Pr[M.main(j) @ &m : P res.`1 /\ P res.`2 /\ !M.x1 /\ M.x2].
rewrite Pr[mu_eq]. auto. auto. rewrite z. clear z.
have z : Pr[M.main(j) @ &m : ((P res.`1 /\ P res.`2) /\ !M.x1) /\ !M.x2] = Pr[M.main(j) @ &m : P res.`1 /\ P res.`2 /\ !M.x1 /\ !M.x2].
rewrite Pr[mu_eq]. auto. auto. rewrite z. clear z. auto.
move => q. rewrite q. clear q.
have z : Pr[M.main(j) @ &m : ((P res.`1 /\ P res.`2) /\ M.x1) /\ M.x2] = Pr[M.main(j) @ &m : P res.`1 /\ P res.`2 /\ M.x1 /\ M.x2].
rewrite Pr[mu_eq]. auto. auto. rewrite z. clear z.
have z : Pr[M.main(j) @ &m : ((P res.`1 /\ P res.`2) /\ M.x1) /\ !M.x2] = Pr[M.main(j) @ &m : P res.`1 /\ P res.`2 /\ M.x1 /\ !M.x2].
rewrite Pr[mu_eq]. auto. auto. rewrite z. clear z.
rewrite (main_lemma_11 &m P). rewrite (main_lemma_12 &m). rewrite (main_lemma_21 &m).
rewrite (main_lemma_22 &m). smt.
qed.


lemma fact2 &m P j : Pr[ SB(A,B).main(j) @ &m : P res.`1 /\ P res.`2 ] 
  = 1%r/4%r * Pr[ SB(A,B).main_12(j) @ &m : P res.`1 /\ P res.`2 ]
  + 1%r/4%r * Pr[ SB(A,B).main_21(j) @ &m : P res.`1 /\ P res.`2 ]
  + 1%r/4%r * Pr[ SB(A,B).main_11(j) @ &m : P res.`1 /\ P res.`2 ]
  + 1%r/4%r * Pr[ SB(A,B).main_22(j) @ &m : P res.`1 /\ P res.`2 ].
proof.
have e0 : Pr[SB(A, B).main(j) @ &m : P res.`1 /\ P res.`2] = Pr[M.main(j) @ &m : P res.`1 /\ P res.`2 ].
byequiv (_: (={glob A, glob B, arg}) ==> _). proc. inline*. wp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
seq 3 3 : (={glob A, i0, ix,s,x}). rnd. wp. call(_:true). skip. progress.
if. auto.
seq 5 5 : (={glob A, ix,s,x,r,i1,r1,i0,x0}). rnd.  wp. call (_:true). wp.  call(_:true).
skip. progress. if. auto.
call (_:true). skip. progress. call (_:true). skip. progress.
seq 5 5 : (={glob A, ix,s,x,r,r1,i1, i0,x0}). rnd.  wp. call (_:true). wp.  call(_:true).
skip. progress.
if.  auto. call(_:true). skip. progress. call(_:true). skip. progress. auto. auto.
have e1 : Pr[SB(A, B).main_12(j) @ &m : P res.`1 /\ P res.`2] = Pr[M.main_12(j) @ &m : P res.`1 /\ P res.`2].
byequiv (_: (={glob A, glob B, arg}) ==> _). proc. inline*. wp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. progress. auto. auto.
have e2 : Pr[SB(A, B).main_21(j) @ &m : P res.`1 /\ P res.`2] = Pr[M.main_21(j) @ &m : P res.`1 /\ P res.`2].
byequiv (_: (={glob A, glob B, arg}) ==> _). proc. inline*. wp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. progress. auto. auto.
have e3 : Pr[SB(A, B).main_11(j) @ &m : P res.`1 /\ P res.`2] = Pr[M.main_11(j) @ &m : P res.`1 /\ P res.`2].
byequiv (_: (={glob A, glob B, arg}) ==> _). proc. inline*. wp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. progress. auto. auto.
have e4 : Pr[SB(A, B).main_22(j) @ &m : P res.`1 /\ P res.`2] = Pr[M.main_22(j) @ &m : P res.`1 /\ P res.`2].
byequiv (_: (={arg, glob A, glob B}) ==> _). proc. inline*. wp.
seq 1 1 : (={glob A, ix}). call Bsens. skip. auto.
call (_:true). call(_:true). call(_:true). call (_:true). skip. progress. auto. auto.
rewrite e0 e1 e2 e3 e4. apply main_lemma.
qed.


end section.
end RSBH.
