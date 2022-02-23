\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Data.Bool
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Axiom.Extensionality.Propositional

open import util
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import mod

module sequent {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
               (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
               (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where
       --(bar : Bar W) where
open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)


-- ---------------------------------
-- Sequents

record hypothesis : Set where
  constructor mkHyp
  field
    name : Var
    hyp  : Term


hypotheses : Set
hypotheses = List hypothesis


record sequent : Set where
  constructor mkSeq
  field
    hyps  : hypotheses
    concl : Term
    ext   : Term


#hypothesesUpto : List Var → hypotheses → Bool
#hypothesesUpto vs [] = true
#hypothesesUpto vs (mkHyp v t ∷ hs) = (fvars t) ⊆? vs ∧ #hypothesesUpto (v ∷ vs) hs


#hypotheses : hypotheses → Set
#hypotheses hs = #hypothesesUpto [] hs ≡ true


record #sequent : Set where
  constructor mk#Seq
  field
    seq    : sequent
    #hyps  : #hypotheses (sequent.hyps seq)
    #concl : # (sequent.concl seq)
    #ext   : # (sequent.ext seq)


record rule : Set where
  constructor mkRule
  field
    premises : List sequent
    goal     : sequent


-- [t,u,v] is the substitution [0\t,1\u,2\v]
Sub : Set
Sub = List CTerm


dom : Sub → List Var
dom [] = []
dom (x ∷ l) = 0 ∷ Data.List.map suc (dom l)


data ≡subs : 𝕎· → Sub → Sub → hypotheses → Set where
  ≡subs[] : (w : 𝕎·) → ≡subs w [] [] []
-- FINISH


data ≡hyps : 𝕎· → Sub → Sub → hypotheses → Set where
  ≡hyps[] : (w : 𝕎·) → ≡hyps w [] [] []
-- FINISH


covered : (s : Sub) (t : Term) → Set
covered s t = fvars t ⊆ dom s


subs : (s : Sub) (t : Term) (c : covered s t) → CTerm
subs [] t c = {!t!}
subs (u ∷ l) t c = {!!}


sequent_pairwise_true : ℕ → 𝕎· → sequent → Set(lsuc(L))
sequent_pairwise_true i w (mkSeq hyps concl ext) =
  (s1 s2 : Sub) (cc1 : covered s1 concl) (cc2 : covered s2 concl) (ce1 : covered s1 ext) (ce2 : covered s2 ext)
  → ≡subs w s1 s2 hyps
  → ≡hyps w s1 s2 hyps
  → equalTypes i w (subs s1 concl cc1) (subs s2 concl cc2)
     × equalInType i w (subs s1 concl cc1) (subs s1 ext ce1) (subs s2 ext ce2)

\end{code}
