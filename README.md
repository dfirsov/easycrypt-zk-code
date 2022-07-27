# Zero-Knowledge in EasyCrypt

This repository contains the EasyCrypt code associated with the paper "D. Firsov, D. Unruh. [Zero-Knowledge in EasyCrypt](https://eprint.iacr.org/2022/926)" .

## Contents
- *[generic/](generic)*  - generic formalization of properties and derivations associated with sigma protocols.
- *[case_studies/FiatShamir/](case_studies/FiatShamir/)* - instance of Fiat-Shamir protocol.
- *[case_studies/Schnorr/](case_studies/Schnorr/)* - instance of Schnorr protocol.
- *[case_studies/HamiltonBlum/](case_studies/HamiltonBlum/)* - instance of Blum protocol. 
- *[misc/](misc/)* - miscellaneous useful results.
- *[checkall](checkall)* - script for running the EasyCrypt proof-checker on the entire development.
- *[rewinding/](rewinding/)* - **copy** of a rewinding library implemented by D. Firsov and D. Unruh.
- *[FORMALIZATION_CAVEATS.md](FORMALIZATION_CAVEATS.md)* - description of formalization challenges and choices.
- *[MANUAL.md](MANUAL.md)* - brief description of structure of the generic development.

## Setup
* For this project we used the version of EasyCrypt (1.0) theorem prover with GIT hash: r2022.04-23-gb44893a5.
* EasyCrypt was configured with support from the following SMT solvers: Why3@1.5.0, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.1.
* To check the development run:

      $> cd DEVELOPMENT_FOLDER
      $> bash checkall

* If you want to typecheck this code in Emacs then you must update your load path. Make sure your `~/.emacs` file contains the following load paths:

      '(easycrypt-load-path
       (quote
        ( "DEVELOPMENT_PATH/rewinding" 
          "DEVELOPMENT_PATH/misc"
          "DEVELOPMENT_PATH/misc/while_props"
          "DEVELOPMENT_PATH/generic")))

  





