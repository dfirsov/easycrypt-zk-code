# Zero-Knowledge in EasyCrypt

This repository contains the EasyCrypt code associated with the paper "D. Firsov, D. Unruh. [Zero-Knowledge in EasyCrypt](https://eprint.iacr.org/2022/926)" .

Setup
--------

* For this project we used the developement version of EasyCrypt (1.0) theorem prover with GIT hash: r2022.04-23-gb44893a5

* EasyCrypt was configured with support from the following SMT solvers: Why3@1.5.0, Z3@4.8.7, CVC4@1.6, Alt-Ergo@2.4.1

* to check the development run:

      $> cd DEVELOPMENT_FOLDER
      $> bash checkall

* If you want to typecheck this code in Emacs then you must update your load path:

   Make sure your `~/.emacs` file contains the following load 

      '(easycrypt-load-path
       (quote
        ( "DEVELOPMENT_PATH/rewinding" 
          "DEVELOPMENT_PATH/aux"
          "DEVELOPMENT_PATH/aux/program_logic"
          "DEVELOPMENT_PATH/generic_zero_knowledge")))

  
Contents
------------

- *checkall* - script for running the EasyCrypt proof-checker on the entire development.
- *rewinding/* - formalization of rewinding technique implemented by D. Firsov and D. Unruh.
- *generic_sigma_protocols/* - formalization of properties and derivations associated with sigma protocols.
	- *GenericBasics.ec* - introduces main datatypes and operators (Sec 3.1). 
	- *GenericCompleteness.ec* - basic definitions related to completeness (Sec 3.2) and proof of sequential composition for statistical and perfect completeness (Sec 5.1).
	- *GenericSoundness.ec* - basic definitions related to soundness (Sec 3.3) and proof of sequential composition for statistical soundness (Sec 5.2).
	- *GenericSpecialSoundness.ec* - basic definitions related to special soundness (Sec 3.4) and derivation of extractability from special soundness (Sec 4.2). 
	- *GenericExtractability.ec* - basic definitions related to proof of knowledge (Sec 3.5) and derivation of soundness from extractability (Sec 4.3).
	- *GenericZeroKnowledge.ec* - basic definitions related to zero-knowledge (Sec 3.6) and derivation of zero-knowledge from "one-shot" simulator (Sec 4.1).
- *case_studies/FiatShamir* - instance of Fiat-Shamir protocol
	- *FS_Completeness.ec* - direct proof of completeness and automatic conclusion of iterated completeness.
	- *FS_SpecialSoundness.ec* - direct proof of perfect special soundness.
	- *FS_Sim1Property.ec* - implementation of "one-shot" simulator and proof of its properties (lower-bound on "success"-event; conditional indistinguishability; rewinding in case of "bad"-event)
	- *FS_Extractability.ec* - automatic conclusion of extractability from special soundness. 
	- *FS_Soundness.ec* - automatic conclusion of (iterated) soundness soundness from extractability.
	- *FS_ZeroKnowledge.ec* - automatic conclusion of zero-knowledge from "one-shot" simulator and its properties.
- *case_studies/Schnorr* - instance of Schnorr protocol
 	- *Schnorr_Completeness.ec* - direct proof of completeness and automatic conclusion of iterated completeness.
	- *Schnorr_SpecialSoundness.ec* - direct proof of special soundness.
	- *Schnorr_Extractability.ec* - automatic conclusion of extractability from special soundness.
- *case_studies/HamBlum* - instance of Blum protocol
	- *Blum_Completeness.ec* - 
	- *Blum_SpecialSoundness.ec* -
	- *Blum_Sim1Property.ec*  - 
	- *Blum_Soundness.ec*  -
	- *Blum_Extractability.ec* -
	- *Blum_ZeroKnowledge.ec* - 
- *aux/* - miscellaneous useful results



