require import AllCore Distr.


type commitment, opening, message.

op Com  : message -> (commitment * opening) distr.
op Ver : message * (commitment * opening) -> bool.

axiom Com_sound : forall (x : message * (commitment * opening)), x.`2 \in Com x.`1 => Ver x.
axiom Com_lossless : forall b, is_lossless (Com b).


module type Binder = {
   proc bind() : commitment * message * opening * message * opening
}.

module BindingExperiment (B:Binder) = {
    proc main() : bool = {
      var c, m, m', d, d', v, v';

      (c, m, d, m', d') <@ B.bind();
      v                 <- Ver (m, (c, d));
      v'                <- Ver (m', (c, d'));

      return v /\ v' /\ m <> m';
    }
}.
