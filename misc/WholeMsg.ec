pragma Goals:printall.
require import Distr DBool AllCore List.


type message, ain.

op m1, m2 : message.

axiom m1_and_m2_diff : m1 <> m2.

module type Tail = {
  proc main(m : message, a : ain) : bool
}.


module W(T : Tail) = {
  proc main(a : ain) = {
    var m, r;
    m <$ duniform [m1; m2];
    r <@ T.main(m,a);
    return r;
  }
}.


section.

declare module T <: Tail.

local module W' = {
  var m : message
  proc main(a:ain) = {
    var r;
    m <$ duniform [m1; m2];
    r <@ T.main(m,a);
    return r;
  }
}.


local lemma scx1 &m x:
    Pr[ W'.main(x) @ &m : res /\ W'.m = m1 ]
  = 1%r/2%r * Pr[ T.main(m1,x) @ &m : res ].
proof. byphoare (_: (glob T) = (glob T){m} /\ a = x ==> _) => //. 
proc. 
pose z := (Pr[ T.main(m1,x) @ &m : res ]).
seq 1 : (W'.m = m1) (1%r/2%r)  z (1%r/2%r) 0%r  ((glob T) = (glob T){m} /\ a = x).
rnd.  skip. progress. 
rnd.  skip. progress. rewrite duniformE =>//=. 
have : m1 <> m2. apply m1_and_m2_diff. progress.
case(m1 = m2) => //. progress. rewrite eq_sym in H0. rewrite H0. smt(). 
have phr : phoare[ T.main : (glob T) = (glob T){m} /\ arg = (m1, x) ==> res ] = Pr[ T.main(m1,x) @ &m : res ].
bypr. progress. byequiv. 
proc*. call (_:true). skip.
progress. auto. smt(). smt(). auto. auto.
call phr. skip. progress.
hoare. call (_:true). skip. progress. rewrite H =>//=. 
rewrite /z =>//.   
qed.


local lemma scx2 &m x:
    Pr[ W'.main(x) @ &m : res /\ W'.m = m2 ]
  = 1%r/2%r * Pr[ T.main(m2,x) @ &m : res ].
proof. byphoare (_: (glob T) = (glob T){m} /\ a = x ==> _) =>//. 
proc. 
pose z := (Pr[ T.main(m2,x) @ &m : res ]).
seq 1 : (W'.m = m2) (1%r/2%r)  z (1%r/2%r) 0%r  ((glob T) = (glob T){m} /\ a = x).
rnd.  skip. auto. 
rnd.  skip. progress. rewrite duniformE =>//=.  
have : m1 <> m2. apply m1_and_m2_diff. progress.
case(m1 = m2) => //. progress. rewrite H0. smt(). 
have phr : phoare[ T.main : (glob T) = (glob T){m} /\ arg = (m2, x) ==> res ] = Pr[ T.main(m2,x) @ &m : res ].
bypr. progress. byequiv. 
proc*. call (_:true). skip.
progress. smt(). smt(). auto. auto.
call phr. skip. progress.
hoare. call (_:true). skip. progress. rewrite H =>//. 
rewrite /z =>//.   
qed.


local lemma spc &m x :
    Pr[ W'.main(x) @ &m : res ]
   = Pr[ T.main(m1,x) @ &m : res ] / 2%r
   + Pr[ T.main(m2,x)  @ &m : res ] / 2%r.
proof. 
have ->: Pr[ W'.main(x) @ &m : res ] =
         Pr[ W'.main(x) @ &m : res /\ W'.m = m1 ] + Pr[ W'.main(x) @ &m : res /\ W'.m = m2 ].
rewrite Pr[mu_split W'.m = m1]. 
have ->: Pr[W'.main(x) @ &m : res /\ W'.m <> m1] = Pr[W'.main(x) @ &m : res /\ W'.m = m2]. 
byequiv(_: _ ==> _) => //. proc. inline*.
call(_:true). rnd. 
skip. progress.  
rewrite supp_duniform mem_seq2 in H. 
elim H => [mL1 | mL2] => //.   
have : m1 <> m2. apply m1_and_m2_diff. progress. rewrite eq_sym in H2. apply H2.
reflexivity.
rewrite scx1 scx2 =>//.  
qed.

   
lemma splitcases &m x :
    Pr[ W(T).main(x) @ &m : res ]
   = Pr[ T.main(m1,x) @ &m : res ] / 2%r
   + Pr[ T.main(m2,x)  @ &m : res ] / 2%r.
proof.
have  ->: Pr[ W(T).main(x) @ &m : res ] = Pr[ W'.main(x) @ &m : res ].
byequiv. proc*. inline*. sim. auto. auto. 
apply spc.
qed.

end section.
    
