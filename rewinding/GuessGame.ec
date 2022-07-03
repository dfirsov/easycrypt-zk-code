require import AllCore List Distr Dexcepted FelTactic.
require import StdOrder StdBigop Finite.
import RealOrder Bigreal.

type bits.


op bD : bits distr.


axiom bDU : is_uniform bD.
axiom bDL : is_lossless bD.


module type GuessGame = {
  proc init(r : int) : unit
  proc guess(x : bits) : bool
}.


module type Adversary (O:GuessGame) = {
   proc play() : unit {O.guess}
}.


module Main (O:GuessGame) (A:Adversary) = {
  proc main(q : int) = {
    var r;
    O.init(q);
    r <@ A(O).play();
    return r;
  }
}.


module GG = {
  var win : bool
  var c, q : int

  proc init(q : int) = {
    c    <- 0;
    win  <- false;
    GG.q <- q;
  }

  proc guess(x : bits) : bool = {
    var r;
    r <- witness;
    if (c < q) {
      r <$ bD;
      win <- win || r = x;
      c <- c + 1;
    }    
    return win;
  }
}.


op supp_size (d : 'a distr) : int = size (to_seq (support d)).


lemma winPr &m : forall (A <:Adversary {-GG}), forall q, 0 <= q =>
 Pr[ Main(GG,A).main(q) @ &m : GG.win  ] 
    <= q%r  / (supp_size bD)%r.
proof. move => A. move => q q_pos.
have ->:  Pr[ Main(GG,A).main(q) @ &m : GG.win ] = Pr[ Main(GG,A).main(q) @ &m : GG.win  /\ (0 <= GG.c <= q) ].
byequiv (_: ={glob A, glob GG, arg} /\ GG.q{1} = GG.q{2} /\ arg{1} = q  ==> _). proc.
seq 1 1 : (={glob A, glob GG} /\ GG.q{1} = GG.q{2} /\ (0 <= GG.c <= GG.q){1} /\ GG.q{1} = q).
inline *.   wp. skip. progress.
 call (_: (0 <= GG.c <= GG.q){1} /\ ={glob GG} /\ GG.q{1} = q).
proc. sp. if. smt.  wp. rnd. skip. smt. skip. smt.
skip. progress. auto.  auto.  
  fel 1 GG.c (fun x => 1%r / (supp_size bD)%r) q GG.win [GG.guess : (GG.c < GG.q)] => //.
   rewrite BRA.sumr_const RField.intmulr count_predT.
    smt (size_range).
   inline *;auto.
   proc;inline *;sp 1;if;last by hoare.
    wp.
    conseq (_ : _ ==> r = x)=> [ /# | ].
    rnd;auto => &hr /> ??? .
    move => z.
    rewrite mu1_uni_ll. apply bDU. apply bDL.
  smt.
   move=> c;proc;sp;inline *.
    by rcondt 1 => //;wp;conseq (_: _ ==> true) => // /#.
  move=> b c;proc;sp;inline *;if => //.
  sp. wp. rnd.  skip.  smt.
qed.
