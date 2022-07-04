# Reflection, Rewinding, and Coin-Toss in EasyCrypt


Setup
-----

* For this project we used the developement version of EasyCrypt (1.0)
theorem prover with git-hash: 512f0f2bd8dc8c1132f3cd138a17d57d4db9c514

* EasyCrypt was configured with support from the following SMT solvers:
Why3@1.4.0, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.0

* to check the development run:
  
  $> cd DEVELOPMENT_FOLDER
  $> bash checkall


Contents
--------

* checkall - script for running the EasyCrypt proof-checker on the entire development.
  
* GuessGame.ec - introductory examples.

  lemmas from Sec. 2: winPr

* Reflection.ec - probabilistic reflection.

  lemmas from Sec. 3.1: reflection, reflection_simple 

* FiniteApproximation.ec - finite Pr-approximation for distributions and programs.

  lemmas from Sec. 3.2: fin_pr_approx_distr_conv, fin_pr_approx_prog_conv

* Averaging.ec - averaging technique.

  lemmas from Sec. 3.2: averaging

* JensensInf.ec - Jensen's inequality for distributions with infinite support.

  lemmas from Sec. 3.2: Jensen_inf

* SquareConvex.ec - square function is convex.

* ReflectionComp.ec - reflection of composition.

  lemmas from Sec. 3.3: refl_comp_simple, refl_comp

* RewBasics.ec - basic definition of rewindable adversaries.

  defs from Sec. 4: RewProp

* RewTrivial.ec - programs without global state are rewindable.

  lemmas from Sec. 4: no_globs_rew

* RewTransformations.ec - transformation of rewindable adversaries are rewindable.

  lemmas from Sec. 4.1: trans_rew

* RewMultRule.ec - multiplication rule for rewindable adversaries

  lemmas from Sec. 4.2: rew_mult_law, rew_clean, rew_mult_simple

* RewCommutesSimple.ec - basic commutativty of rewindable computations.

  lemmas from Sec. 4.2: rew_comm_law_simple

* RewCommutes.ec - commutatitivty of rewindable computations with initialization.

  lemma from Sec. 4.2: rew_comm_law

* RewWithInit.ec - inequality for rewinding with initialization.

  lemma from Sec. 4.3: rew_with_init

* RewSumBindingGeneric.ec - generic sum-binding inequality.

  lemma from Sec. 5.1: sum_binding_generic

* RewSumBindingCommitment.ec - binding commitments are sum-binding.

  lemma from Sec. 5.1: commitment_sum_binding 

* CoinToss.ec - security of a coin-toss protocol.

  lemma from Sec. 5.2: coin_toss_alice