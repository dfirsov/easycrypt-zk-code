require import AllCore.

type prob, wit, chal, com, resp, sbits.


module type Prover = {
  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.

module type Verifier = {
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
  proc summitup(c : com, r : resp)   : sbits
}.


module type RewProver = {
  proc * setState(s : sbits) : unit
  proc getState() : sbits
  proc commit(x : prob, w : wit) : com
  proc response(ch : chal) : resp
}.

module type RewVerifier = {
  proc * setState(s : sbits) : unit
  proc getState() : sbits
  proc challenge(Ny : prob, c : com) : chal
  proc verify(c : com, r : resp)     : bool
  proc summitup(c : com, r : resp)   : sbits
}.

module type Simulator = {
  proc simulate(Ny : prob) : sbits
}.

(* Correctness *)
module Correct(P : Prover, V : Verifier) = {
  proc main(Ny:prob, w : wit) = {
    var c,b,r,result;
    c <- P.commit(Ny,w);  
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.verify(c,r);  
    return result;
  }
}.

(* ZK *)
module ZK(P : Prover, V : Verifier) = {
  proc main(Ny : prob, w : wit) = {
    var c,b,r,result;
    c <- P.commit(Ny,w);
    b <- V.challenge(Ny,c);
    r <- P.response(b);
    result <- V.summitup(c,r);
    return result;
  }
}.

