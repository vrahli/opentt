\begin{code}
{-# OPTIONS --rewriting #-}
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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
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


module continuity7b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

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

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E)



-- TODO: ⊆dom𝕎-start and dom𝕎-startChoice are the same


-- MOVE to continuity-conds
⊆dom𝕎-startNewChoiceT : (cc : ContConds) (w : 𝕎·) (t : Term)
                        → dom𝕎· w ⊆ dom𝕎· (startNewChoiceT Res⊤ w t)
⊆dom𝕎-startNewChoiceT cc w t {name} i = dom𝕎-startNewChoiceT cc name w t i



subRen-names2ren : (cc : ContConds) (w1 w2 : 𝕎·) (r1 r2 : ren) (a : Term) (l : List Name) (u v : List Name)
                   → u ⊆ dom𝕎· w1
                   → v ⊆ dom𝕎· w2
                   → subRen u v r1 r2
                   → subRen u v r1 (names2ren w1 w2 a l r2)
subRen-names2ren cc w1 w2 r1 r2 a [] u v su sv sub = sub
subRen-names2ren cc w1 w2 r1 r2 a (x ∷ l) u v su sv sub with Name∈⊎ x (dom𝕎· w1) | Name∈⊎ x (dom𝕎· w2)
... | inj₁ p | inj₁ q = subRen-names2ren cc (startNewChoiceT Res⊤ w1 a) (startNewChoiceT Res⊤ w2 a) r1 ((newChoiceT w1 a , newChoiceT w2 a) ∷ r2) a l u v (⊆-trans su (⊆dom𝕎-startNewChoiceT cc w1 a)) (⊆-trans sv (⊆dom𝕎-startNewChoiceT cc w2 a)) (subRen-trans (newChoiceT w1 a) (newChoiceT w2 a) r1 r2 (λ z → ¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names a)) (su z)) (λ z → ¬fresh∈dom𝕎2 w2 (names𝕎· w2) (↓vars (names a)) (sv z)) sub)
... | inj₁ p | inj₂ q = subRen-names2ren cc (startNewChoiceT Res⊤ w1 a) (startChoice· x Res⊤ w2) r1 ((newChoiceT w1 a , x) ∷ r2) a l u v (⊆-trans su (⊆dom𝕎-startNewChoiceT cc w1 a)) (⊆-trans sv (ContConds.ccD⊆start cc x w2)) (subRen-trans (newChoiceT w1 a) x r1 r2 (λ z → ¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names a)) (su z)) (λ z → q (sv z)) sub)
... | inj₂ p | inj₁ q = subRen-names2ren cc (startChoice· x Res⊤ w1) (startNewChoiceT Res⊤ w2 a) r1 ((x , newChoiceT w2 a) ∷ r2) a l u v (⊆-trans su (ContConds.ccD⊆start cc x w1)) (⊆-trans sv (⊆dom𝕎-startNewChoiceT cc w2 a)) (subRen-trans x (newChoiceT w2 a) r1 r2 (λ z → p (su z)) (λ z → ¬fresh∈dom𝕎2 w2 (names𝕎· w2) (↓vars (names a)) (sv z)) sub)
... | inj₂ p | inj₂ q = subRen-names2ren cc (startChoice· x Res⊤ w1) (startChoice· x Res⊤ w2) r1 ((x , x) ∷ r2) a l u v (⊆-trans su (ContConds.ccD⊆start cc x w1)) (⊆-trans sv (ContConds.ccD⊆start cc x w2)) (subRen-trans x x r1 r2 (λ z → p (su z)) (λ z → q (sv z)) sub)



-- This is not true if 'g' is impure, for example if 'g' is 'FRESH u', while f is 'FRESH t' then
-- while 'updRel2 name f g a g', it might be the case for 'u' and 't' because the FRESH operators
-- might generate different names.  upto𝕎 should be up to some renaming, not just up to 'name'.
step-updRel2 : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
              {a b x : Term} {w0 w1 w2 w : 𝕎·} {r : ren}
              → ¬ name ∈ names f
--              → ¬ name ∈ names g
              → # f
              → # g
              → (names a) ⊆ dom𝕎· w1 -- Could these two restrictions be guaranteed by "loading" all names into the world? No, we don't have control over g in the extract...
              → (names b) ⊆ dom𝕎· w -- For this one we'd have to require g to be name-free
              → names f ⊆ dom𝕎· w1
              → names g ⊆ dom𝕎· w
              → step a w1 ≡ just (x , w2)
              → stepsPresUpdRel2 n name f g x w2
              → updRel2 name f g r a b
              → upto𝕎 name w1 w r
              → getT≤ℕ w1 n name
              → ¬ name ∈ names𝕎· w1
              → name ∈ dom𝕎· w1
              → name ∈ dom𝕎· w
              → compatible· name w1 Res⊤
              → compatible· name w Res⊤
              → ∀𝕎-get0-NUM w1 name
              → w0 ⊑· w1
              → w0 ⊑· w
              → ∀𝕎 w0 (λ w' _ → (k : ℕ) → k < n → ⇛!sameℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
              → ΣstepsUpdRel2 name f g x w1 w2 b w r
step-updRel2 cc gc {n} {name} {f} {g} {.NAT} {.NAT} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind updRel2-NAT upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAT , NAT , w1 , w , r , refl , refl , updRel2-NAT , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.QNAT} {.QNAT} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind updRel2-QNAT upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QNAT , QNAT , w1 , w , r , refl , refl , updRel2-QNAT , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.TNAT} {.TNAT} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind updRel2-TNAT upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TNAT , TNAT , w1 , w , r , refl , refl , updRel2-TNAT , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LT a₁ b₁)} {.(LT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-LT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LT a₁ b₁ , LT a₂ b₂ , w1 , w , r , refl , refl , updRel2-LT _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-QLT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QLT a₁ b₁ , QLT a₂ b₂ , w1 , w , r , refl , refl , updRel2-QLT _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(NUM x₁)} {.(NUM x₁)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-NUM x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NUM _ , NUM _ , w1 , w , r , refl , refl , updRel2-NUM _ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-NUM a₁
... | inj₁ (n₁ , p) rewrite p | updRel2-NUMₗ→ ur with is-NUM b₁
... |    inj₁ (n₂ , q) rewrite q | updRel2-NUMₗ→ ur₁ with n₁ <? n₂
... |       yes rn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , c₁ , c₂ , w1 , w , r , refl , concl , ur₂ , upw , subRen-refl r
  where
    concl : steps 1 (IFLT (NUM n₁) (NUM n₂) c₂ d₂ , w) ≡ (c₂ , w)
    concl with n₁ <? n₂
    ... | yes rn' = refl
    ... | no rn' = ⊥-elim (rn' rn)
... |       no rn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , d₁ , d₂ , w1 , w , r , refl , concl , ur₃ , upw , subRen-refl r
  where
    concl : steps 1 (IFLT (NUM n₁) (NUM n₂) c₂ d₂ , w) ≡ (d₂ , w)
    concl with n₁ <? n₂
    ... | yes rn' = ⊥-elim (rn rn')
    ... | no rn' = refl
step-updRel2 cc gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn | inj₁ (n₁ , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-IFLT₂
    (++⊆3→2 {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
    (++⊆3→2 {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
    (++⊆3→3 {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
    (++⊆3→3 {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
    ur₂ ur₃ ind'
  where
    ind' : ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆3→1 {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid) (++⊆3→1 {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid) nfiw ngiw z (stepsPresUpdRel2-IFLT₂→ ind) ur₁ upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-IFLT₁
    (++⊆4→2 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
    (++⊆4→2 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
    (++⊆4→3 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
    (++⊆4→3 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
    (++⊆4→4 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
    (++⊆4→4 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
    ur₁ ur₂ ur₃ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆4→1 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid) (++⊆4→1 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid) nfiw ngiw z (stepsPresUpdRel2-IFLT₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(SUC a₁)} {.(SUC a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-SUC a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-NUM a₁
... | inj₁ (k , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel2-NUMₗ→ ur =
  0 , 1 , NUM (suc k) , NUM (suc k) , w1 , w , r , refl , refl , updRel2-NUM (suc k) , upw , subRen-refl r
... | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-SUC₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg naid nbid nfiw ngiw z (stepsPresUpdRel2-SUC₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(PI a₁ b₁)} {.(PI a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-PI a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PI a₁ b₁ , PI a₂ b₂ , w1 , w , r , refl , refl , updRel2-PI _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-LAMBDA a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LAMBDA a₁ , LAMBDA a₂ , w1 , w , r , refl , refl , updRel2-LAMBDA _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-LAM a₁
... | inj₁ (t , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  concl d
  where
    d : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
        ⊎ (t ≡ updBody name f × a₂ ≡ force g)
    d = updRel2-LAMBDAₗ→ ur

    concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
            ⊎ (t ≡ updBody name f × a₂ ≡ force g)
            → ΣstepsUpdRel2 name f g (sub b₁ t) w1 w1 (APPLY a₂ b₂) w r
    concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub b₁ t , sub b₂ u , w1 , w , r , refl , refl , updRel2-sub cf cg ur ur₁ , upw , subRen-refl r
    concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c2
      where
        ind' : stepsPresUpdRel2 n name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        ind' rewrite e1 | e2 | sub-upd name f b₁ cf = ind

        c1 : ΣstepsUpdRel2 name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (APPLY (force g) b₂) w r
        c1 = fst (→ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {b₁} {b₂} {w0} {w1} {w} {r} nnf cf cg compat compat' wgt0 ur₁ (++⊆2→2 {names t} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names g ++ []} {names b₂} {dom𝕎· w} nbid) idom' nfiw ngiw upw ew01 ew0 eqn ind')

        c2 : ΣstepsUpdRel2 name f g (sub b₁ (updBody name f)) w1 w1 (APPLY (force g) b₂) w r
        c2 rewrite sub-upd name f b₁ cf = c1
... | inj₂ q with is-CS a₁
... |    inj₁ (name' , np) rewrite np {--| updRel2-CSₗ→ r--} with is-NUM b₁
... |       inj₁ (k , nq) rewrite nq | updRel2-NUMₗ→ ur₁ with getT⊎ k name' w1
... |          inj₁ (c , nr) rewrite nr | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , 1 , c , c , w1 , w , r , refl , concl , --comp' ,
  updRel2-refl {name} {f} {g} {r} {c} (ContConds.ccG¬names cc k name' w1 c nr) , --updRel2-refl {name} {f} {g} {c} (λ x → nnw (ContConds.ccGnames cc name name' k c w1 nr x)) ,
-- In case c contains a name x, we'd have to guarantee that names∈ren x x r.  We can't know that.
-- Better only consider nats as choices here
  upw , subRen-refl r --Data.Maybe.map (λ t → t , w) (getT n name w)
  where {--()--} {--()--}
    nm2 : Σ Name (λ name'' → a₂ ≡ CS name'' × ¬ name' ≡ name × ¬ name'' ≡ name × names∈ren name' name'' r)
    nm2 = updRel2-CSₗ→  ur

    comp' : steps 1 (APPLY (CS (fst nm2)) (NUM k) , w) ≡ (c , w)
    comp' rewrite upto𝕎-pres-getT k name name' (fst nm2) w1 w r c (fst (snd (snd nm2))) (fst (snd (snd (snd nm2)))) (snd (snd (snd (snd nm2)))) upw nr = refl

    concl : steps 1 (APPLY a₂ (NUM k) , w) ≡ (c , w)
    concl rewrite fst (snd nm2) = comp' --refl
... |          inj₂ nr rewrite nr = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn | inj₂ q | inj₁ (name' , np) | inj₂ y with step⊎ b₁ w1
... |          inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  concl
  where
    ind' : ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w0} {w1} {w1'} {w} nnf cf cg (λ {x} i → naid (there i)) (λ {x} i → nbid (∈-++⁺ʳ (names a₂) i)) nfiw ngiw z (stepsPresUpdRel2-APPLY₂→ ind) ur₁ upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn

    nm2 : Σ Name (λ name'' → a₂ ≡ CS name'' × ¬ name' ≡ name × ¬ name'' ≡ name × names∈ren name' name'' r)
    nm2 = updRel2-CSₗ→  ur

    concl : ΣstepsUpdRel2 name f g (APPLY (CS name') b₁') w1 w1' (APPLY a₂ b₂) w r
    concl rewrite fst (snd nm2) = →ΣstepsUpdRel2-APPLY₂ {name} {f} {g} {name'} {fst nm2} (fst (snd (snd nm2))) (fst (snd (snd (snd nm2)))) (naid (here refl)) (nbid (here refl)) (snd (snd (snd (snd nm2)))) ind'
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn | inj₂ q | inj₂ p with step⊎ a₁ w1
... | inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-APPLY₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ur₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid) nfiw ngiw z (stepsPresUpdRel2-APPLY₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(FIX a₁)} {.(FIX a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-FIX a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-LAM a₁
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  concl d
  where
    d : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
        ⊎ (t ≡ updBody name f × a₂ ≡ force g)
    d = updRel2-LAMBDAₗ→ ur

    concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
            ⊎ (t ≡ updBody name f × a₂ ≡ force g)
            → ΣstepsUpdRel2 name f g (sub (FIX (LAMBDA t)) t) w1 w1 (FIX a₂) w r
    concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub (FIX (LAMBDA t)) t , sub (FIX (LAMBDA u)) u , w1 , w , r , refl , refl , updRel2-sub cf cg ur (updRel2-FIX _ _ (updRel2-LAMBDA _ _ ur)) , upw , subRen-refl r
    concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c3
      where
        ind' : stepsPresUpdRel2 n name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        ind' rewrite e1 | e2 | sub-upd name f (FIX (upd name f)) cf = ind

        c1 : Σ (ΣstepsUpdRel2 name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (APPLY (force g) (FIX (force g))) w r)
               (λ x → 0 < fst (snd x))
        c1 = →ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {FIX (upd name f)} {FIX (force g)} {w0} {w1} {w} {r} nnf cf cg compat compat' wgt0 (updRel2-FIX _ _ updRel2-upd) (names-FIX-upd⊆ {name} {f} idom nfiw) (names-FIX-force⊆ {g} ngiw) idom' nfiw ngiw upw ew01 ew0 eqn ind'

        c2 : ΣstepsUpdRel2 name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (FIX (force g)) w r
        c2 = ΣstepsUpdRel2-FIX-APPLY→ c1

        c3 : ΣstepsUpdRel2 name f g (sub (FIX (upd name f)) (updBody name f)) w1 w1 (FIX (force g)) w r
        c3 rewrite sub-upd name f (FIX (upd name f)) cf = c2
... | inj₂ nt with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-FIX₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg naid nbid nfiw ngiw z (stepsPresUpdRel2-FIX₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(LET a₁ b₁)} {.(LET a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-LET a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with isValue⊎ a₁
... | inj₁ v rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , 1 , sub a₁ b₁ , sub a₂ b₂ , w1 , w , r , refl ,
  comp' , updRel2-sub cf cg ur₁ ur , upw , subRen-refl r
  where
    comp' : steps 1 (LET a₂ b₂ , w) ≡ (sub a₂ b₂ , w)
    comp' with isValue⊎ a₂
    ... | inj₁ u = refl
    ... | inj₂ u = ⊥-elim (u (updRel2-valₗ→ name f g r a₁ a₂ ur v))
... | inj₂ v with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-LET₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ur₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid) nfiw ngiw z (stepsPresUpdRel2-LET₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-SUM a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUM a₁ b₁ , SUM a₂ b₂ , w1 , w , r , refl , refl , updRel2-SUM _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-PAIR a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w , r , refl , refl , updRel2-PAIR _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-SPREAD a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-PAIR a₁
... | inj₁ (u₁ , u₂ , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl d
  where
    d : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ PAIR x₁ x₂ × updRel2 name f g r u₁ x₁ × updRel2 name f g r u₂ x₂))
    d = updRel2-PAIRₗ→ ur

    concl : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ PAIR x₁ x₂ × updRel2 name f g r u₁ x₁ × updRel2 name f g r u₂ x₂))
            → ΣstepsUpdRel2 name f g (sub u₂ (sub u₁ b₁)) w1 w1 (SPREAD a₂ b₂) w r
    concl (x₁ , x₂ , eqa , ur1 , ur2) rewrite eqa =
      0 , 1 , sub u₂ (sub u₁ b₁) , sub x₂ (sub x₁ b₂) , w1 , w , r , refl , refl ,
      updRel2-sub cf cg (updRel2-sub cf cg ur₁ ur1) ur2 , upw , subRen-refl r
... | inj₂ np with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-SPREAD₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ur₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid) nfiw ngiw z (stepsPresUpdRel2-SPREAD₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(SET a₁ b₁)} {.(SET a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-SET a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SET a₁ b₁ , SET a₂ b₂ , w1 , w , r , refl , refl , updRel2-SET _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-ISECT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , w , r , refl , refl , updRel2-ISECT _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-TUNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-TUNION _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-UNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNION a₁ b₁ , UNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-UNION _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-QTUNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-QTUNION _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(INL a₁)} {.(INL a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-INL a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INL a₁ , INL a₂ , w1 , w , r , refl , refl , updRel2-INL _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(INR a₁)} {.(INR a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-INR a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INR a₁ , INR a₂ , w1 , w , r , refl , refl , updRel2-INR _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ ur₂) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-INL a₁
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl d
  where
    d : Σ Term (λ u → a₂ ≡ INL u × updRel2 name f g r t u)
    d = updRel2-INLₗ→ ur

    concl : Σ Term (λ u → a₂ ≡ INL u × updRel2 name f g r t u)
            → ΣstepsUpdRel2 name f g (sub t b₁) w1 w1 (DECIDE a₂ b₂ c₂) w r
    concl (u , eqa , ur) rewrite eqa =
      0 , 1 , sub t b₁ , sub u b₂ , w1 , w , r , refl , refl , updRel2-sub cf cg ur₁ ur , upw , subRen-refl r
... | inj₂ nl with is-INR a₁
... |    inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl d
  where
    d : Σ Term (λ u → a₂ ≡ INR u × updRel2 name f g r t u)
    d = updRel2-INRₗ→ ur

    concl : Σ Term (λ u → a₂ ≡ INR u × updRel2 name f g r t u)
            → ΣstepsUpdRel2 name f g (sub t c₁) w1 w1 (DECIDE a₂ b₂ c₂) w r
    concl (u , eqa , ur) rewrite eqa =
      0 , 1 , sub t c₁ , sub u c₂ , w1 , w , r , refl , refl , updRel2-sub cf cg ur₂ ur , upw , subRen-refl r
... |    inj₂ nr with step⊎ a₁ w1
... |       inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-DECIDE₁
    (++⊆3→2 {names a₁} {names b₁} {names c₁} {dom𝕎· w1} naid)
    (++⊆3→2 {names a₂} {names b₂} {names c₂} {dom𝕎· w} nbid)
    (++⊆3→3 {names a₁} {names b₁} {names c₁} {dom𝕎· w1} naid)
    (++⊆3→3 {names a₂} {names b₂} {names c₂} {dom𝕎· w} nbid)
    ur₁ ur₂ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆3→1 {names a₁} {names b₁} {names c₁} {dom𝕎· w1} naid) (++⊆3→1 {names a₂} {names b₂} {names c₂} {dom𝕎· w} nbid) nfiw ngiw z (stepsPresUpdRel2-DECIDE₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ r₂) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQ a₁ b₁ c₁ , EQ a₂ b₂ c₂ , w1 , w , r , refl , refl , updRel2-EQ _ _ _ _ _ _ ur ur₁ r₂ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.AX} {.AX} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind updRel2-AX upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , AX , AX , w1 , w , r , refl , refl , updRel2-AX , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.FREE} {.FREE} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind updRel2-FREE upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FREE , FREE , w1 , w , r , refl , refl , updRel2-FREE , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(CS name1)} {.(CS name2)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-CS name1 name2 d1 d2 x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , CS _ , CS _ , w1 , w , r , refl , refl , updRel2-CS name1 name2 d1 d2 x₁ {--updRel2-CS _ x₁--} , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(NAME name1)} {.(NAME name2)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-NAME name1 name2 d1 d2 x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAME _ , NAME _ , w1 , w , r , refl , refl , updRel2-NAME name1 name2 d1 d2 x₁ {--updRel2-NAME _ x₁--} , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(FRESH a)} {.(FRESH b)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-FRESH a b ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 ,
  shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a) ,
  shiftNameDown 0 (renn 0 (newChoiceT+ w b) b) ,
  startNewChoiceT Res⊤ w1 a ,
  startNewChoiceT Res⊤ w b ,
  (newChoiceT w1 a , newChoiceT w b) ∷ r ,
  refl , refl ,
  →updRel2-shiftNameDown0 {name} {f} {g} cf cg
    ((newChoiceT w1 a , newChoiceT w b) ∷ r)
    (→¬0∈names-renn-0s (newChoiceT w1 a) a)
    (→¬0∈names-renn-0s (newChoiceT w b) b)
    (updRel2-renn
      {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} {a} {b}
      0 (newChoiceT+ w1 a) (newChoiceT+ w b)
      (¬newChoiceT+∈names w1 a) (¬newChoiceT+∈names w b)
      (→¬newChoiceT+-suc name w1 a idom) (→¬newChoiceT+-suc name w b idom')
      (¬0∈renₗ-sren r) (¬0∈renᵣ-sren r)
      (¬0∈names-shiftNameUp f) (¬0∈names-shiftNameUp g)
      (λ x → suc-≢-0 (sym x)) ur) , -- we have to get force to contain name too, so that updRel2 relates terms with the same names
  →upto𝕎-startNewChoiceT cc name w1 w r a b upw ,
  subRen-trans (newChoiceT w1 a) (newChoiceT w b) r r (¬fresh∈dom𝕎2 w1 (names𝕎· w1) (↓vars (names a))) (¬fresh∈dom𝕎2 w (names𝕎· w) (↓vars (names b))) (subRen-refl r)
step-updRel2 cc gc {n} {name} {f} {g} {.(LOAD a)} {.(LOAD a)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-LOAD a) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , AX , AX , startNewChoices Res⊤ w1 a , startNewChoices Res⊤ w a ,
  names2ren w1 w a (names a) r , refl , refl , updRel2-AX ,
  upto𝕎-startNewChoices cc name w1 w r a (names a) upw ,
  subRen-names2ren cc w1 w r r a (names a) (dom𝕎· w1) (dom𝕎· w) ⊆-refl ⊆-refl (subRen-refl r)
--0 , 0 , LOAD a₁ , TSQUASH a₂ , w1 , w , r , refl , refl , updRel2-TSQUASH _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-CHOOSE a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-NAME a₁
... | inj₁ (nm , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | fst (snd (updRel2-NAMEₗ→ ur)) =
  0 , 1 , AX , AX , chooseT nm w1 b₁ , chooseT (fst nm2) w b₂ , r , refl , refl ,
  updRel2-AX , upw2 , (subRen-refl r)
  where
    nm2 : Σ Name (λ nm' → a₂ ≡ NAME nm' × ¬ nm ≡ name × ¬ nm' ≡ name × names∈ren nm nm' r)
    nm2 = updRel2-NAMEₗ→ ur

    upw2 : upto𝕎 name (chooseT nm w1 b₁) (chooseT (fst nm2) w b₂) r
    upw2 with is-NUM b₁
    ... | inj₁ (k , q) rewrite q | updRel2-NUMₗ→ ur₁ =
      →upto𝕎-chooseT
        cc {name} {nm} {fst nm2} {r} {w1} {w} (NUM k) (naid (here refl)) (nbid (here refl))
        (fst (snd (snd nm2)))
        (fst (snd (snd (snd nm2))))
        (snd (snd (snd (snd nm2))))
        upw
    ... | inj₂ q rewrite ContConds.ccCnum cc nm w1 b₁ q | ContConds.ccCnum cc (fst nm2) w b₂ (updRel2-¬NUM→ name f g r b₁ b₂ ur₁ q) = upw
... | inj₂ nm with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel2-CHOOSE₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ur₁ ind'
  where
    ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
    ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid) nfiw ngiw z (stepsPresUpdRel2-CHOOSE₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel2 cc gc {n} {name} {f} {g} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-TSQUASH a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TSQUASH a₁ , TSQUASH a₂ , w1 , w , r , refl , refl , updRel2-TSQUASH _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-TTRUNC a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TTRUNC a₁ , TTRUNC a₂ , w1 , w , r , refl , refl , updRel2-TTRUNC _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(TCONST a₁)} {.(TCONST a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-TCONST a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TCONST a₁ , TCONST a₂ , w1 , w , r , refl , refl , updRel2-TCONST _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(SUBSING a₁)} {.(SUBSING a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-SUBSING a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUBSING a₁ , SUBSING a₂ , w1 , w , r , refl , refl , updRel2-SUBSING _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.PURE} {.PURE} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind updRel2-PURE upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PURE , PURE , w1 , w , r , refl , refl , updRel2-PURE , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(DUM a₁)} {.(DUM a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-DUM a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , DUM a₁ , DUM a₂ , w1 , w , r , refl , refl , updRel2-DUM _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-FFDEFS a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w , r , refl , refl , updRel2-FFDEFS _ _ _ _ ur ur₁ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(UNIV x₁)} {.(UNIV x₁)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-UNIV x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNIV _ , UNIV _ , w1 , w , r , refl , refl , updRel2-UNIV _ , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LIFT a₁)} {.(LIFT a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-LIFT a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LIFT a₁ , LIFT a₂ , w1 , w , r , refl , refl , updRel2-LIFT _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(LOWER a₁)} {.(LOWER a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-LOWER a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LOWER a₁ , LOWER a₂ , w1 , w , r , refl , refl , updRel2-LOWER _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(SHRINK a₁)} {.(SHRINK a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind (updRel2-SHRINK a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SHRINK a₁ , SHRINK a₂ , w1 , w , r , refl , refl , updRel2-SHRINK _ _ ur , upw , subRen-refl r
step-updRel2 cc gc {n} {name} {f} {g} {.(upd name f)} {.(force g)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid nfiw ngiw comp ind updRel2-upd upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , upd name f , force g , w1 , w , r , refl , refl , updRel2-upd , upw , subRen-refl r

\end{code}
