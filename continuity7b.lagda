\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --auto-inline #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
--open import Data.Bool using (Bool ; _∧_ ; _∨_)
--open import Agda.Builtin.String
--open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
--open import Function.Bundles
--open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
open import choiceBar
open import encode


module continuity7b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                    (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
--open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
--open import terms4(W)(C)(K)(G)(X)(N)(EC)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
--open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

{--
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--}

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (force)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (getT≤ℕ)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (¬0∈names-shiftNameUp)
--open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) --using (ren ; updRel2 ; upto𝕎)
open import continuity5b2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (→updRel2-shiftNameDown0)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (++⊆2→1 ; ++⊆2→2 ; ++⊆3→1 ; ++⊆3→2 ; ++⊆3→3 ; ++⊆4→1 ; ++⊆4→2 ; ++⊆4→3 ; ++⊆4→4 ; stepsPresUpdRel2-IFLT₂→ ; →ΣstepsUpdRel2-IFLT₂ ; stepsPresUpdRel2-IFLT₁→ ; →ΣstepsUpdRel2-IFLT₁ ; stepsPresUpdRel2-IFEQ₂→ ; →ΣstepsUpdRel2-IFEQ₂ ; stepsPresUpdRel2-IFEQ₁→ ; →ΣstepsUpdRel2-IFEQ₁ ; stepsPresUpdRel2-SUC₁→ ; →ΣstepsUpdRel2-SUC₁ ; stepsPresUpdRel2-MAPP₁→ ; →ΣstepsUpdRel2-MAPP₁ ; →ΣstepsUpdRel2-upd ; updRel2-CSₗ→ ; upto𝕎-pres-getT ; →ΣstepsUpdRel2-APPLY₂ ; stepsPresUpdRel2-APPLY₁→ ; →ΣstepsUpdRel2-APPLY₁ ; ΣstepsUpdRel2-FIX-APPLY→ ; stepsPresUpdRel2-FIX₁→ ; →ΣstepsUpdRel2-FIX₁ ; updRel2-valₗ→ ; stepsPresUpdRel2-LET₁→ ; →ΣstepsUpdRel2-LET₁ ; stepsPresUpdRel2-SPREAD₁→ ; →ΣstepsUpdRel2-SPREAD₁ ; stepsPresUpdRel2-WREC₁→ ; →ΣstepsUpdRel2-WREC₁ ; stepsPresUpdRel2-DECIDE₁→ ; →ΣstepsUpdRel2-DECIDE₁ ; →¬0∈names-renn-0s ; ¬newChoiceT+∈names ; →¬newChoiceT+-suc ; ¬0∈renₗ-sren ; ¬0∈renᵣ-sren ; →upto𝕎-startNewChoiceT ; names2ren ; upto𝕎-startNewChoices ; subRen-names2ren ; updRel2-NAMEₗ→ ; →upto𝕎-chooseT ; updRel2-¬NUM→ ; stepsPresUpdRel2-CHOOSE₁→ ; →ΣstepsUpdRel2-CHOOSE₁ ; updRel2-WRECr)



abstract

  ΣstepsUpdRel2-IFLT : (n : ℕ) (name : Name) (f g : Term) (r : ren) (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x : Term) (w w1 w2 : 𝕎·)
                       → names a₁ ++ names b₁ ++ names c₁ ++ names d₁ ⊆ dom𝕎· w1
                       → names a₂ ++ names b₂ ++ names c₂ ++ names d₂ ⊆ dom𝕎· w
                       → upto𝕎 name w1 w r
                       → updRel2 name f g r a₁ a₂
                       → updRel2 name f g r b₁ b₂
                       → updRel2 name f g r c₁ c₂
                       → updRel2 name f g r d₁ d₂
                       → stepsPresUpdRel2 n name f g x w2
                       → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                       → ((b₁' : Term) (w1' : 𝕎·) → step b₁ w1 ≡ just (b₁' , w1') → stepsPresUpdRel2 n name f g b₁' w1' → ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r)
                       → step (IFLT a₁ b₁ c₁ d₁) w1 ≡ just (x , w2)
                       → ΣstepsUpdRel2 name f g x w1 w2 (IFLT a₂ b₂ c₂ d₂) w r
  ΣstepsUpdRel2-IFLT n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ua ub uc ud ind inda indb comp with is-NUM a₁
  ... | inj₁ (n₁ , p) rewrite p | updRel2-NUMₗ→ ua with is-NUM b₁
  ... |    inj₁ (n₂ , q) rewrite q | updRel2-NUMₗ→ ub with n₁ <? n₂
  ... |       yes rn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    0 , 1 , c₁ , c₂ , w1 , w , r , refl , concl , uc , upw , subRen-refl r
    where
      concl : steps 1 (IFLT (NUM n₁) (NUM n₂) c₂ d₂ , w) ≡ (c₂ , w)
      concl with n₁ <? n₂
      ... | yes rn' = refl
      ... | no rn' = ⊥-elim (rn' rn)
  ... |       no rn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    0 , 1 , d₁ , d₂ , w1 , w , r , refl , concl , ud , upw , subRen-refl r
    where
      concl : steps 1 (IFLT (NUM n₁) (NUM n₂) c₂ d₂ , w) ≡ (d₂ , w)
      concl with n₁ <? n₂
      ... | yes rn' = ⊥-elim (rn rn')
      ... | no rn' = refl
  ΣstepsUpdRel2-IFLT n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ua ub uc ud ind inda indb comp | inj₁ (n₁ , p) | inj₂ q with step⊎ b₁ w1
  ... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-IFLT₂
      (++⊆3→2 {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆3→2 {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      (++⊆3→3 {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆3→3 {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      uc ud ind'
    where
      ind' : ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
      ind' = indb b₁' w1' refl (stepsPresUpdRel2-IFLT₂→ ind)
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  ΣstepsUpdRel2-IFLT n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ua ub uc ud ind inda indb comp | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-IFLT₁
      (++⊆4→2 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆4→2 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      (++⊆4→3 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆4→3 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      (++⊆4→4 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆4→4 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      ub uc ud ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-IFLT₁→ ind)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))


abstract

  ΣstepsUpdRel2-IFEQ : (n : ℕ) (name : Name) (f g : Term) (r : ren) (a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x : Term) (w w1 w2 : 𝕎·)
                       → names a₁ ++ names b₁ ++ names c₁ ++ names d₁ ⊆ dom𝕎· w1
                       → names a₂ ++ names b₂ ++ names c₂ ++ names d₂ ⊆ dom𝕎· w
                       → upto𝕎 name w1 w r
                       → updRel2 name f g r a₁ a₂
                       → updRel2 name f g r b₁ b₂
                       → updRel2 name f g r c₁ c₂
                       → updRel2 name f g r d₁ d₂
                       → stepsPresUpdRel2 n name f g x w2
                       → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                       → ((b₁' : Term) (w1' : 𝕎·) → step b₁ w1 ≡ just (b₁' , w1') → stepsPresUpdRel2 n name f g b₁' w1' → ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r)
                       → step (IFEQ a₁ b₁ c₁ d₁) w1 ≡ just (x , w2)
                       → ΣstepsUpdRel2 name f g x w1 w2 (IFEQ a₂ b₂ c₂ d₂) w r
  ΣstepsUpdRel2-IFEQ n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ua ub uc ud ind inda indb comp with is-NUM a₁
  ... | inj₁ (n₁ , p) rewrite p | updRel2-NUMₗ→ ua with is-NUM b₁
  ... |    inj₁ (n₂ , q) rewrite q | updRel2-NUMₗ→ ub with n₁ ≟ n₂
  ... |       yes rn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    0 , 1 , c₁ , c₂ , w1 , w , r , refl , concl , uc , upw , subRen-refl r
    where
      concl : steps 1 (IFEQ (NUM n₁) (NUM n₂) c₂ d₂ , w) ≡ (c₂ , w)
      concl with n₁ ≟ n₂
      ... | yes rn' = refl
      ... | no rn' = ⊥-elim (rn' rn)
  ... |       no rn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    0 , 1 , d₁ , d₂ , w1 , w , r , refl , concl , ud , upw , subRen-refl r
    where
      concl : steps 1 (IFEQ (NUM n₁) (NUM n₂) c₂ d₂ , w) ≡ (d₂ , w)
      concl with n₁ ≟ n₂
      ... | yes rn' = ⊥-elim (rn rn')
      ... | no rn' = refl
  ΣstepsUpdRel2-IFEQ n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ua ub uc ud ind inda indb comp | inj₁ (n₁ , p) | inj₂ q with step⊎ b₁ w1
  ... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-IFEQ₂
      (++⊆3→2 {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆3→2 {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      (++⊆3→3 {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆3→3 {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      uc ud ind'
    where
      ind' : ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
      ind' = indb b₁' w1' refl (stepsPresUpdRel2-IFEQ₂→ ind)
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  ΣstepsUpdRel2-IFEQ n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ua ub uc ud ind inda indb comp | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-IFEQ₁
      (++⊆4→2 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆4→2 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      (++⊆4→3 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆4→3 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      (++⊆4→4 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
      (++⊆4→4 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
      ub uc ud ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-IFEQ₁→ ind)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))


abstract

  ΣstepsUpdRel2-SUC : (n : ℕ) (name : Name) (f g : Term) (r : ren) (a₁ a₂ x : Term) (w w1 w2 : 𝕎·)
                      → names a₁ ⊆ dom𝕎· w1
                      → names a₂ ⊆ dom𝕎· w
                      → upto𝕎 name w1 w r
                      → updRel2 name f g r a₁ a₂
                      → stepsPresUpdRel2 n name f g x w2
                      → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                      → step (SUC a₁) w1 ≡ just (x , w2)
                      → ΣstepsUpdRel2 name f g x w1 w2 (SUC a₂) w r
  ΣstepsUpdRel2-SUC n name f g r a₁ a₂ x w w1 w2 naid nbid upw ua ind inda comp with is-NUM a₁
  ... | inj₁ (k , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel2-NUMₗ→ ua =
    0 , 1 , NUM (suc k) , NUM (suc k) , w1 , w , r , refl , refl , updRel2-NUM (suc k) , upw , subRen-refl r
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-SUC₁ ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-SUC₁→ ind)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))


abstract

  ΣstepsUpdRel2-MAPP : (n : ℕ) (name : Name) (f g : Term) (r : ren) (s : 𝕊) (a₁ a₂ x : Term) (w w1 w2 : 𝕎·)
                       → names a₁ ⊆ dom𝕎· w1
                       → names a₂ ⊆ dom𝕎· w
                       → upto𝕎 name w1 w r
                       → updRel2 name f g r a₁ a₂
                       → stepsPresUpdRel2 n name f g x w2
                       → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                       → step (MAPP s a₁) w1 ≡ just (x , w2)
                       → ΣstepsUpdRel2 name f g x w1 w2 (MAPP s a₂) w r
  ΣstepsUpdRel2-MAPP n name f g r s a₁ a₂ x w w1 w2 naid nbid upw ua ind inda comp with is-NUM a₁
  ... | inj₁ (k , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel2-NUMₗ→ ua =
    0 , 1 , NUM (s k) , NUM (s k) , w1 , w , r , refl , refl , updRel2-NUM (s k) , upw , subRen-refl r
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-MAPP₁ ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-MAPP₁→ ind)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))


abstract

  ΣstepsUpdRel2-LET : (n : ℕ) (name : Name) (f g : Term) (r : ren) (a₁ a₂ b₁ b₂ x : Term) (w w1 w2 : 𝕎·) (cf : # f) (cg : # g)
                      → names a₁ ++ names b₁ ⊆ dom𝕎· w1
                      → names a₂ ++ names b₂ ⊆ dom𝕎· w
                      → upto𝕎 name w1 w r
                      → updRel2 name f g r a₁ a₂
                      → updRel2 name f g r b₁ b₂
                      → stepsPresUpdRel2 n name f g x w2
                      → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                      → step (LET a₁ b₁) w1 ≡ just (x , w2)
                      → ΣstepsUpdRel2 name f g x w1 w2 (LET a₂ b₂) w r
  ΣstepsUpdRel2-LET n name f g r a₁ a₂ b₁ b₂ x w w1 w2 cf cg naid nbid upw ua ub ind inda comp with isValue⊎ a₁
  ... | inj₁ v rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
    0 , 1 , sub a₁ b₁ , sub a₂ b₂ , w1 , w , r , refl ,
    comp' , updRel2-sub cf cg ub ua , upw , subRen-refl r
    where
      comp' : steps 1 (LET a₂ b₂ , w) ≡ (sub a₂ b₂ , w)
      comp' with isValue⊎ a₂
      ... | inj₁ u = refl
      ... | inj₂ u = ⊥-elim (u (updRel2-valₗ→ name f g r a₁ a₂ ua v))
  ... | inj₂ v with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-LET₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ub ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-LET₁→ ind)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))


abstract

  ΣstepsUpdRel2-SPREAD : (n : ℕ) (name : Name) (f g : Term) (r : ren) (a₁ a₂ b₁ b₂ x : Term) (w w1 w2 : 𝕎·) (cf : # f) (cg : # g)
                       → names a₁ ++ names b₁ ⊆ dom𝕎· w1
                       → names a₂ ++ names b₂ ⊆ dom𝕎· w
                       → upto𝕎 name w1 w r
                       → updRel2 name f g r a₁ a₂
                       → updRel2 name f g r b₁ b₂
                       → stepsPresUpdRel2 n name f g x w2
                       → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                       → step (SPREAD a₁ b₁) w1 ≡ just (x , w2)
                       → ΣstepsUpdRel2 name f g x w1 w2 (SPREAD a₂ b₂) w r
  ΣstepsUpdRel2-SPREAD n name f g r a₁ a₂ b₁ b₂ x w w1 w2 cf cg naid nbid upw ua ub ind inda comp with is-PAIR a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl (updRel2-PAIRₗ→ ua)
    where
      concl : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ PAIR x₁ x₂ × updRel2 name f g r u₁ x₁ × updRel2 name f g r u₂ x₂))
              → ΣstepsUpdRel2 name f g (sub u₂ (sub (shiftUp 0 u₁) b₁)) w1 w1 (SPREAD a₂ b₂) w r
      concl (x₁ , x₂ , eqa , ur1 , ur2) rewrite eqa =
        0 , 1 , sub u₂ (sub (shiftUp 0 u₁) b₁) , sub x₂ (sub (shiftUp 0 x₁) b₂) , w1 , w , r , refl , refl ,
        updRel2-sub cf cg (updRel2-sub cf cg ub (updRel2-shiftUp 0 cf cg ur1)) ur2 , upw , subRen-refl r
  ... | inj₂ np with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-SPREAD₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ub ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-SPREAD₁→ ind)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))


abstract

  ΣstepsUpdRel2-WREC : (n : ℕ) (name : Name) (f g : Term) (r : ren) (a₁ a₂ b₁ b₂ x : Term) (w w1 w2 : 𝕎·) (cf : # f) (cg : # g)
                       → names a₁ ++ names b₁ ⊆ dom𝕎· w1
                       → names a₂ ++ names b₂ ⊆ dom𝕎· w
                       → upto𝕎 name w1 w r
                       → updRel2 name f g r a₁ a₂
                       → updRel2 name f g r b₁ b₂
                       → stepsPresUpdRel2 n name f g x w2
                       → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                       → step (WREC a₁ b₁) w1 ≡ just (x , w2)
                       → ΣstepsUpdRel2 name f g x w1 w2 (WREC a₂ b₂) w r
  ΣstepsUpdRel2-WREC n name f g r a₁ a₂ b₁ b₂ x w w1 w2 cf cg naid nbid upw ua ub ind inda comp with is-SUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl (updRel2-SUPₗ→ ua)
    where
      concl : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ SUP x₁ x₂ × updRel2 name f g r u₁ x₁ × updRel2 name f g r u₂ x₂))
              → ΣstepsUpdRel2 name f g (sub (WRECr b₁ u₂) (sub (shiftUp 0 u₂) (sub (shiftUp 0 (shiftUp 0 u₁)) b₁))) w1 w1 (WREC a₂ b₂) w r
      concl (x₁ , x₂ , eqa , ur1 , ur2) rewrite eqa =
        0 , 1 ,
        sub (WRECr b₁ u₂) (sub (shiftUp 0 u₂) (sub (shiftUp 0 (shiftUp 0 u₁)) b₁)) ,
        sub (WRECr b₂ x₂) (sub (shiftUp 0 x₂) (sub (shiftUp 0 (shiftUp 0 x₁)) b₂)) ,
        w1 , w , r , refl , refl ,
        updRel2-sub cf cg (updRel2-sub cf cg (updRel2-sub cf cg ub (updRel2-shiftUp 0 cf cg (updRel2-shiftUp 0 cf cg ur1)))
                                             (updRel2-shiftUp 0 cf cg ur2))
                          (updRel2-WRECr cf cg ub ur2) ,
        upw , subRen-refl r
  ... | inj₂ np with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-WREC₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ub ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-WREC₁→ ind)
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))


abstract

  ΣstepsUpdRel2-DECIDE : (n : ℕ) (name : Name) (f g : Term) (r : ren) (a₁ a₂ b₁ b₂ c₁ c₂ x : Term) (w w1 w2 : 𝕎·) (cf : # f) (cg : # g)
                         → names a₁ ++ names b₁ ++ names c₁ ⊆ dom𝕎· w1
                         → names a₂ ++ names b₂ ++ names c₂ ⊆ dom𝕎· w
                         → upto𝕎 name w1 w r
                         → updRel2 name f g r a₁ a₂
                         → updRel2 name f g r b₁ b₂
                         → updRel2 name f g r c₁ c₂
                         → stepsPresUpdRel2 n name f g x w2
                         → ((a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r)
                         → step (DECIDE a₁ b₁ c₁) w1 ≡ just (x , w2)
                         → ΣstepsUpdRel2 name f g x w1 w2 (DECIDE a₂ b₂ c₂) w r
  ΣstepsUpdRel2-DECIDE n name f g r a₁ a₂ b₁ b₂ c₁ c₂ x w w1 w2 cf cg naid nbid upw ua ub uc ind inda comp with is-INL a₁
  ... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl (updRel2-INLₗ→ ua)
    where
      concl : Σ Term (λ u → a₂ ≡ INL u × updRel2 name f g r t u)
              → ΣstepsUpdRel2 name f g (sub t b₁) w1 w1 (DECIDE a₂ b₂ c₂) w r
      concl (u , eqa , ur) rewrite eqa =
        0 , 1 , sub t b₁ , sub u b₂ , w1 , w , r , refl , refl , updRel2-sub cf cg ub ur , upw , subRen-refl r
  ... | inj₂ nl with is-INR a₁
  ... |    inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl (updRel2-INRₗ→ ua)
    where
      concl : Σ Term (λ u → a₂ ≡ INR u × updRel2 name f g r t u)
              → ΣstepsUpdRel2 name f g (sub t c₁) w1 w1 (DECIDE a₂ b₂ c₂) w r
      concl (u , eqa , ur) rewrite eqa =
        0 , 1 , sub t c₁ , sub u c₂ , w1 , w , r , refl , refl , updRel2-sub cf cg uc ur , upw , subRen-refl r
  ... |    inj₂ nr with step⊎ a₁ w1
  ... |       inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-DECIDE₁
      (++⊆3→2 {names a₁} {names b₁} {names c₁} {dom𝕎· w1} naid)
      (++⊆3→2 {names a₂} {names b₂} {names c₂} {dom𝕎· w} nbid)
      (++⊆3→3 {names a₁} {names b₁} {names c₁} {dom𝕎· w1} naid)
      (++⊆3→3 {names a₂} {names b₂} {names c₂} {dom𝕎· w} nbid)
      ub uc ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = inda a₁' w1' refl (stepsPresUpdRel2-DECIDE₁→ ind)
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))



abstract

  updRel2-MSEQₗ→ : {name : Name} {f g : Term} {r : ren} {s : 𝕊} {a : Term}
                → updRel2 name f g r (MSEQ s) a
                → a ≡ MSEQ s
  updRel2-MSEQₗ→ {name} {f} {g} {r} {s} {.(MSEQ s)} (updRel2-MSEQ .s) = refl


abstract

  updRel2-MSEQᵣ→ : {name : Name} {f g : Term} {r : ren} {s : 𝕊} {a : Term}
                → updRel2 name f g r a (MSEQ s)
                → a ≡ MSEQ s
  updRel2-MSEQᵣ→ {name} {f} {g} {r} {s} {.(MSEQ s)} (updRel2-MSEQ .s) = refl

\end{code}
