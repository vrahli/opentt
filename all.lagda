\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle


open import util
open import name
open import calculus
open import world
open import choice
open import compatible
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import exBar
open import mod
open import encode
open import MarkovPrinciple


module all {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
           (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
           (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
           (N : NewChoice {L} W C K G)
           (EC : Encode)
           (V : ChoiceVal W C K G X N EC)
           (F : Freeze {L} W C K P G N)
           (E0 : Extensionality 0ℓ 0ℓ)
           (EM : ExcludedMiddle (lsuc(L))) -- for ExBar, used in turn in lem
           (MP : MarkovPrinciple (lsuc(L)))
           (CB : ChoiceBar W M C K P G X N EC V F)
           (EB : ExBar W M)
       where

-- Weak consistency of the theory
open import consistency using (weak-consistency)

-- Some relations between some example of bar spaces
open import subBar{L}(W)(M)(C)(K)(P)

-- LEM is false for Beth/Kripke-like modalities using choices
open import not_lem{L}(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)
-- Using classical, we can however prove that LEM is consistent when using an open-like modality (see ExBar in exBar.lagda)
open import lem{L}(W)(M)(C)(K)(G)(X)(N)(EM)(EB)(EC)
-- This version requires choices to be Booleans:
open import not_lpo{L}(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB) using (¬LPO)
-- As opposed to the above version, this one relies on QTBool instead of Bool:
open import not_lpo_qtbool{L}(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB) using (¬LPOq)
-- This version requires choices to be Booleans, but also freezable to always be true:
open import not_mp{L}(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB) using (¬MP ; ¬MP₂ ; ¬MP₃ ; ¬MP₄)
-- In here, we've tried to prove to prove ¬MP for a read/no-write version of MP, but it is not finished
-- open import not_mp{L}(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(CE)(CB)
-- MP is however consistent when restricted to pure functions
open import mpp{L}(W)(M)(C)(K)(G)(X)(N)(EM)(EC) using (MPp-inh ; MPp₂-inh ; MPp₃-inh ; MPp₆-inh)
open import mpp2{L}(W)(M)(C)(K)(G)(X)(N)(MP)(EM)(EC) using (MPp₆-inh₂ ; MPp₇-inh₂)
open import mpp3{L}(W)(M)(C)(K)(G)(X)(N)(MP)(EM)(EC) using (MPp₇-inh₃)
-- Using classsical logic, MP is also consistent when using an open-like modality (see ExBar in exBar.lagda)
open import mp{L}(W)(M)(C)(K)(G)(X)(N)(EC)(EB)(EM) using (MPvalid ; MP₂valid)
-- If we assume that choices are TRUE and FALSE only, using choice sequences we can prove
-- (1) the invalidity of MP_ℙ (¬MPℙ) using the same pattern than the one for ¬MP, which uses Booleans as choices
-- (2) the validity of MP_𝔹 (MP₇-inh) using classical logic and the fact that functions to Bools essentially act as pure functions
open import mp_prop2{L}(W)(M)(C)(K)(P)(G)(X)(N)(EC)(V)(F)(CB)(EM) using (¬MPℙ ; MP₇-inh)

-- Some results about pure expressions
open import pure2{L}(W)(M)(C)(K)(G)(X)(N)(EC) using (Πpure→ ; ∈PURE-NAT→)

-- This instance of 'choiceBar' uses Beth bars and terms as choices:
open import modInstanceBethCs
-- This instance of 'choiceBar' uses Beth bars and bools (#QTBOOL!) as choices:
open import modInstanceBethCsBool
-- This instance of 'choiceBar' uses Beth bars and bools (#BOOL!) as choices:
open import modInstanceBethCsBool2
-- This instance of 'choiceBar' uses Beth bars and nats as choices:
-- (this makes use of the 'freezable' field in *restrictions*, while the other isntances don't---but could/should)
open import modInstanceBethRef
-- This instance of 'choiceBar' uses Beth bars and bools as choices:
open import modInstanceBethRef2
-- This instance of 'choiceBar' uses Kripke bars and bools as choices:
open import modInstanceKripkeRefBool

-- `openBar` provides an example of a bar.
-- We show here that the resulting modality does not satisfy `followChoice` (from `choiceBar`),
-- which we require to prove ¬LEM for example.
-- This is proved for REF, but should be true for FCS too
open import openNotFollowChoice

-- `barKripke` provides an example of a bar containing all worlds.
-- We show here that the resulting modality does not satisfy `□·-choice` (from `choiceBar`),
-- which we require to prove ¬LEM for example. This is true when using FCS as choices but not REF.
open import kripkeCsNotRetrieving
-- We also show that Kripke bars + FCS does not satisfy the ∀∃𝔹 property in exBar either,
-- which we require to prove the compatibility with LEM
-- So, given the above result and this one, we cannot derive whether Kripke+FCS is compatible with LEM or not
open import kripkeCsNotExBar

-- A proof that all functions on the Baire space are continuous by realizing the modulus of continuity using exceptions.
open import continuity7 using (continuity)
-- We show here that the properties used to prove continuity in continuity7 are satisfied by Kripke bars + references
open import contInstanceKripkeRef
-- We show here that the properties used to prove continuity in continuity7 are satisfied by Open bars + references
open import contInstanceOpenRef
-- We show here that the properties used to prove continuity in continuity7 are satisfied by Beth bars + references
open import contInstanceBethRef
-- We show here that the properties used to prove continuity in continuity7 are satisfied by Kripke bars + CS
open import contInstanceKripkeCS
-- We show here that the properties used to prove continuity in continuity7 are satisfied by Open bars + CS
open import contInstanceOpenCS
-- We show here that the properties used to prove continuity in continuity7 are satisfied by Beth bars + CS
open import contInstanceBethCS

-- A first version of the bar theorem (sem) and its condition (semCond) -- contDiagVal puts the 2 results together
open import barContP6 using (sem)
open import barContP9 using (semCond)
open import barContP10 using (contDiagVal)

-- Another attempt at validating continuity without the name-free requirement. It is unfinished: continuity10b has holes
-- updRel2-renn in continuity5b is now broken because of ENC. Can it be fixed?
--open import continuity9b
open import continuity7b
-- This one is unfinished
--open import continuity10b

-- On AC (not finished yet -- see ac2)
-- ac contains a proof that AC₀₀ is valid when using a Kriple □ and a generic element.
open import ac using (AC₀₀-valid)
-- open import ac2

-- A definition of sequents and their semantics
open import sequent

-- A translation from MLTT to BoxTT
open import mltt
\end{code}
