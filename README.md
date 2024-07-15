# Conditional Contextual Refinement 2.0

## Dependencies
Our development successfully compiles with following versions (in Linux, OS X):

- coq (= *8.15.2*)

- coq-ext-lib (= *0.11.7*)
- coq-paco (= *4.1.2*)
- coq-itree (= *4.0.0*)
- coq-ordinal (= *0.5.2*)

- coq-stdpp (= *1.7.0*)
- coq-iris (= *3.6.0*)

- coq-compcert (= *3.11*) and its dependencies:
  + coq-flocq (= *4.1.0*)
  + menhir (= *20220210*)
  + coq-menhirlib (= *20220210*)

- ocamlbuild (= *0.14.1*)

All packages can be installed from [OPAM archive for Coq](https://github.com/coq/opam-coq-archive)

## How to build
- make -j[N] -k

## Paper to code mapping

Fig. 1
(examples/map)
- T_Map, M_Map, S_Map -> MapJ.v, MapM.v, MapA.v
- Conditions C/D/E --> `Conds`/`CondsB`/`CondsC` in MapHeader.v
- lower refinement -> `MapJMproof.v`
- upper refinement -> `MapMAproof.v` 

Fig. 2
- Cond/Conds --> `fspec`/`stb` in HoareDef.v

Closed Refinement/Contextual Refinement
- `refines`/`refines_closed` in ModSem.v

Fig. 3
- Definitions --> `fspec_equiv`, `fspec_trivial`, `fspec_append`, `stb_equiv`, `stb_unit`, `stb_append` in HoareDef.v
- Properties --> HoareDef.v

empty wrapper intro/elim --> `wrap_intro`/`wrap_elim` in HoareFacts.v

Definition 1. --> `gccr` in HoareFacts.v

Theorem 2. --> `adequacy_isim` in ISim2.v
sepsimFun --> `isim_fsem` in ISim2.v

Fig. 4 --> ISim2.v

Definition/Rules for strong update modality --> `Upd` in IProp.v

Theorem 3/4 --> `isim_vframe`/`isim_hframe` in ISim2.v

cur_sProps --> `current_iProp` in ProofMode.v

Section 5.1 --> CE1.v
Section 5.2 --> ISim2.v (with `HasFreeze` parameter as `HasFreezeY`)
Section 5.3 --> CE2.v

Fig. 7
- PlainMod --> `Mod` in ModSem.v
- Mod --> `SModSem` in HoareDef.v
- underarrow notation --> `SModSem.to_src` in HoareDef.v

Fig. 8
- Same as Fig. 2/3.

Theorem 5 --> `adequacy_type` in Hoare.v

Fig. 9 --> HoareDef.v
- *assumeAndAbstr/*assertAndConcr --> `ASSUME/ASSERT`
- interp*assume/interp*assert --> `handle_condE_tgt`

Fig. 10 --> TypeChange.v
