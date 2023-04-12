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


module continuity7b2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                     (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                     (X : ChoiceExt W C)
                     (N : NewChoice {L} W C K G)
                     (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
--open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
--open import terms4(W)(C)(K)(G)(X)(N)
--open import terms5(W)(C)(K)(G)(X)(N)
--open import terms6(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

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

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E) using (force)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E) using (getT≤ℕ)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (¬0∈names-shiftNameUp)
--open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E) --using (ren ; updRel2 ; upto𝕎)
open import continuity5b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (stepsPresUpdRel2 ; ΣstepsUpdRel2 ; subRen-refl ; stepsPresUpdRel2-APPLY₂→ ; →updRel2-shiftNameDown0 ; updRel2-renn ; subRen-trans)
open import continuity6b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (++⊆2→1 ; ++⊆2→2 ; ++⊆3→1 ; ++⊆3→2 ; ++⊆3→3 ; ++⊆4→1 ; ++⊆4→2 ; ++⊆4→3 ; ++⊆4→4 ; stepsPresUpdRel2-IFLT₂→ ; →ΣstepsUpdRel2-IFLT₂ ; stepsPresUpdRel2-IFLT₁→ ; →ΣstepsUpdRel2-IFLT₁ ; stepsPresUpdRel2-IFEQ₂→ ; →ΣstepsUpdRel2-IFEQ₂ ; stepsPresUpdRel2-IFEQ₁→ ; →ΣstepsUpdRel2-IFEQ₁ ; stepsPresUpdRel2-SUC₁→ ; →ΣstepsUpdRel2-SUC₁ ; stepsPresUpdRel2-MAPP₁→ ; →ΣstepsUpdRel2-MAPP₁ ; →ΣstepsUpdRel2-upd ; updRel2-CSₗ→ ; upto𝕎-pres-getT ; →ΣstepsUpdRel2-APPLY₂ ; stepsPresUpdRel2-APPLY₁→ ; →ΣstepsUpdRel2-APPLY₁ ; ΣstepsUpdRel2-FIX-APPLY→ ; stepsPresUpdRel2-FIX₁→ ; →ΣstepsUpdRel2-FIX₁ ; updRel2-valₗ→ ; stepsPresUpdRel2-LET₁→ ; →ΣstepsUpdRel2-LET₁ ; stepsPresUpdRel2-SPREAD₁→ ; →ΣstepsUpdRel2-SPREAD₁ ; stepsPresUpdRel2-WREC₁→ ; →ΣstepsUpdRel2-WREC₁ ; stepsPresUpdRel2-DECIDE₁→ ; →ΣstepsUpdRel2-DECIDE₁ ; →¬0∈names-renn-0s ; ¬newChoiceT+∈names ; →¬newChoiceT+-suc ; ¬0∈renₗ-sren ; ¬0∈renᵣ-sren ; →upto𝕎-startNewChoiceT ; names2ren ; upto𝕎-startNewChoices ; subRen-names2ren ; updRel2-NAMEₗ→ ; →upto𝕎-chooseT ; updRel2-¬NUM→ ; stepsPresUpdRel2-CHOOSE₁→ ; →ΣstepsUpdRel2-CHOOSE₁ ; updRel2-WRECr)
open import continuity7b(W)(M)(C)(K)(P)(G)(X)(N)(E)



abstract

  -- This is not true if 'g' is impure, for example if 'g' is 'FRESH u', while f is 'FRESH t' then
  -- while 'updRel2 name f g a g', it might be the case for 'u' and 't' because the FRESH operators
  -- might generate different names.  upto𝕎 should be up to some renaming, not just up to 'name'.
  step-updRel2 : (cc : ContConds) (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
               {a b x : Term} {w0 w1 w2 w : 𝕎·} {r : ren}
               → ¬ name ∈ names f
  --              → ¬ name ∈ names g
                  → # f
                  → # g
                  → names a ⊆ dom𝕎· w1 -- Could these two restrictions be guaranteed by "loading" all names into the world? No, we don't have control over g in the extract...
                  → names b ⊆ dom𝕎· w -- For this one we'd have to require g to be name-free
  --              → names f ⊆ dom𝕎· w1
  --              → names g ⊆ dom𝕎· w
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
  step-updRel2 cc gc {n} {name} {f} {g} {.NAT} {.NAT} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind updRel2-NAT upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAT , NAT , w1 , w , r , refl , refl , updRel2-NAT , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.QNAT} {.QNAT} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind updRel2-QNAT upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QNAT , QNAT , w1 , w , r , refl , refl , updRel2-QNAT , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.TNAT} {.TNAT} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind updRel2-TNAT upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TNAT , TNAT , w1 , w , r , refl , refl , updRel2-TNAT , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(LT a₁ b₁)} {.(LT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-LT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LT a₁ b₁ , LT a₂ b₂ , w1 , w , r , refl , refl , updRel2-LT _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-QLT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QLT a₁ b₁ , QLT a₂ b₂ , w1 , w , r , refl , refl , updRel2-QLT _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(NUM x₁)} {.(NUM x₁)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-NUM x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NUM _ , NUM _ , w1 , w , r , refl , refl , updRel2-NUM _ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-IFLT n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ur ur₁ ur₂ ur₃ ind inda indb comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆4→1 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
          (++⊆4→1 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn

      indb : (b₁' : Term) (w1' : 𝕎·) → step b₁ w1 ≡ just (b₁' , w1') → stepsPresUpdRel2 n name f g b₁' w1' → ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
      indb b₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆4→2 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
          (++⊆4→2 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
          comp' ind' ur₁ upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ ur₂ ur₃) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-IFEQ n name f g r a₁ b₁ c₁ d₁ a₂ b₂ c₂ d₂ x w w1 w2 naid nbid upw ur ur₁ ur₂ ur₃ ind inda indb comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆4→1 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
          (++⊆4→1 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn

      indb : (b₁' : Term) (w1' : 𝕎·) → step b₁ w1 ≡ just (b₁' , w1') → stepsPresUpdRel2 n name f g b₁' w1' → ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
      indb b₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆4→2 {names a₁} {names b₁} {names c₁} {names d₁} {dom𝕎· w1} naid)
          (++⊆4→2 {names a₂} {names b₂} {names c₂} {names d₂} {dom𝕎· w} nbid)
          comp' ind' ur₁ upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(SUC a₁)} {.(SUC a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-SUC a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-SUC n name f g r a₁ a₂ x w w1 w2 naid nbid upw ur ind inda comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg naid nbid
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(PI a₁ b₁)} {.(PI a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-PI a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PI a₁ b₁ , PI a₂ b₂ , w1 , w , r , refl , refl , updRel2-PI _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-LAMBDA a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LAMBDA a₁ , LAMBDA a₂ , w1 , w , r , refl , refl , updRel2-LAMBDA _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-LAM a₁
  ... | inj₁ (t , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl (updRel2-LAMBDAₗ→ ur)
    where
      concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
              ⊎ (t ≡ updBody name f × a₂ ≡ force g)
              → ΣstepsUpdRel2 name f g (sub b₁ t) w1 w1 (APPLY a₂ b₂) w r
      concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub b₁ t , sub b₂ u , w1 , w , r , refl , refl , updRel2-sub cf cg ur ur₁ , upw , subRen-refl r
      concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c2
        where
          ind' : stepsPresUpdRel2 n name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
          ind' rewrite e1 | e2 | sub-upd name f b₁ cf = ind

          c1 : ΣstepsUpdRel2 name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (APPLY (force g) b₂) w r
          c1 = fst (→ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {b₁} {b₂} {w0} {w1} {w} {r} nnf cf cg compat compat' wgt0 ur₁ (++⊆2→2 {names t} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names g ++ []} {names b₂} {dom𝕎· w} nbid) idom' upw ew01 ew0 eqn ind')

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
  step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn | inj₂ q | inj₁ (name' , np) | inj₂ y with step⊎ b₁ w1
  ... |          inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl
    where
      ind' : ΣstepsUpdRel2 name f g b₁' w1 w1' b₂ w r
      ind' = step-updRel2 cc gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w0} {w1} {w1'} {w} nnf cf cg (λ {x} i → naid (there i)) (λ {x} i → nbid (∈-++⁺ʳ (names a₂) i)) z (stepsPresUpdRel2-APPLY₂→ ind) ur₁ upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn

      nm2 : Σ Name (λ name'' → a₂ ≡ CS name'' × ¬ name' ≡ name × ¬ name'' ≡ name × names∈ren name' name'' r)
      nm2 = updRel2-CSₗ→  ur

      concl : ΣstepsUpdRel2 name f g (APPLY (CS name') b₁') w1 w1' (APPLY a₂ b₂) w r
      concl rewrite fst (snd nm2) = →ΣstepsUpdRel2-APPLY₂ {name} {f} {g} {name'} {fst nm2} (fst (snd (snd nm2))) (fst (snd (snd (snd nm2)))) (naid (here refl)) (nbid (here refl)) (snd (snd (snd (snd nm2)))) ind'
  ... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn | inj₂ q | inj₂ p with is-MSEQ a₁
  ... | inj₁ (s , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel2-MSEQₗ→ ur =
    0 , 1 , MAPP s b₁ , MAPP s b₂ , w1 , w , r , refl , refl , updRel2-MAPP s b₁ b₂ ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-APPLY a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn | inj₂ q | inj₂ p | inj₂ z with step⊎ a₁ w1
  ... | inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-APPLY₁ (++⊆2→2 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→2 {names a₂} {names b₂} {dom𝕎· w} nbid) ur₁ ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid) z (stepsPresUpdRel2-APPLY₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel2 cc gc {n} {name} {f} {g} {.(MSEQ s)} {.(MSEQ s)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-MSEQ s) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MSEQ _ , MSEQ _ , w1 , w , r , refl , refl , updRel2-MSEQ _ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(MAPP s a₁)} {.(MAPP s a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-MAPP s a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-MAPP n name f g r s a₁ a₂ x w w1 w2 naid nbid upw ur ind inda comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg naid nbid
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(FIX a₁)} {.(FIX a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-FIX a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-LAM a₁
  ... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl (updRel2-LAMBDAₗ→ ur)
    where
      concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel2 name f g r t u)
              ⊎ (t ≡ updBody name f × a₂ ≡ force g)
              → ΣstepsUpdRel2 name f g (sub (FIX (LAMBDA t)) t) w1 w1 (FIX a₂) w r
      concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub (FIX (LAMBDA t)) t , sub (FIX (LAMBDA u)) u , w1 , w , r , refl , refl , updRel2-sub cf cg ur (updRel2-FIX _ _ (updRel2-LAMBDA _ _ ur)) , upw , subRen-refl r
      concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c3
        where
          ind' : stepsPresUpdRel2 n name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
          ind' rewrite e1 | e2 | sub-upd name f (FIX (upd name f)) cf = ind

          na1 : names (FIX (LAMBDA t)) ⊆ dom𝕎· w1
          na1 = naid

          na2 : names (FIX (upd name f)) ⊆ dom𝕎· w1
          na2 rewrite e1 | e2 = naid

          nb1 : names (FIX (force g)) ⊆ dom𝕎· w
          nb1 = nbid

          c1 : Σ (ΣstepsUpdRel2 name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (APPLY (force g) (FIX (force g))) w r)
                 (λ x → 0 < fst (snd x))
          c1 = →ΣstepsUpdRel2-upd cc gc {n} {name} {f} {g} {FIX (upd name f)} {FIX (force g)} {w0} {w1} {w} {r} nnf cf cg compat compat' wgt0 (updRel2-FIX _ _ updRel2-upd) na2 {--(names-FIX-upd⊆ {name} {f} idom nfiw)--} nbid {--(names-FIX-force⊆ {g} ngiw)--} idom' upw ew01 ew0 eqn ind'

          c2 : ΣstepsUpdRel2 name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1 (FIX (force g)) w r
          c2 = ΣstepsUpdRel2-FIX-APPLY→ c1

          c3 : ΣstepsUpdRel2 name f g (sub (FIX (upd name f)) (updBody name f)) w1 w1 (FIX (force g)) w r
          c3 rewrite sub-upd name f (FIX (upd name f)) cf = c2
  ... | inj₂ nt with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel2-FIX₁ ind'
    where
      ind' : ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg naid nbid z (stepsPresUpdRel2-FIX₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel2 cc gc {n} {name} {f} {g} {.(LET a₁ b₁)} {.(LET a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-LET a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-LET n name f g r a₁ a₂ b₁ b₂ x w w1 w2 cf cg naid nbid upw ur ur₁ ind inda comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid)
          (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid)
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-SUM a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUM a₁ b₁ , SUM a₂ b₂ , w1 , w , r , refl , refl , updRel2-SUM _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-PAIR a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w , r , refl , refl , updRel2-PAIR _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-SPREAD a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-SPREAD n name f g r a₁ a₂ b₁ b₂ x w w1 w2 cf cg naid nbid upw ur ur₁ ind inda comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid)
          (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid)
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(WT a₁ b₁)} {.(WT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-WT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , WT a₁ b₁ , WT a₂ b₂ , w1 , w , r , refl , refl , updRel2-WT _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-SUP a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUP a₁ b₁ , SUP a₂ b₂ , w1 , w , r , refl , refl , updRel2-SUP _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-WREC a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-WREC n name f g r a₁ a₂ b₁ b₂ x w w1 w2 cf cg naid nbid upw ur ur₁ ind inda comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid)
          (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid)
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(MT a₁ b₁)} {.(MT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-MT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MT a₁ b₁ , MT a₂ b₂ , w1 , w , r , refl , refl , updRel2-MT _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(SET a₁ b₁)} {.(SET a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-SET a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SET a₁ b₁ , SET a₂ b₂ , w1 , w , r , refl , refl , updRel2-SET _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-ISECT a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , w , r , refl , refl , updRel2-ISECT _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-TUNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-TUNION _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-UNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNION a₁ b₁ , UNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-UNION _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-QTUNION a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w , r , refl , refl , updRel2-QTUNION _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(INL a₁)} {.(INL a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-INL a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INL a₁ , INL a₂ , w1 , w , r , refl , refl , updRel2-INL _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(INR a₁)} {.(INR a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-INR a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INR a₁ , INR a₂ , w1 , w , r , refl , refl , updRel2-INR _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ ur₂) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn =
    ΣstepsUpdRel2-DECIDE n name f g r a₁ a₂ b₁ b₂ c₁ c₂ x w w1 w2 cf cg naid nbid upw ur ur₁ ur₂ ind inda comp
    where
      inda : (a₁' : Term) (w1' : 𝕎·) → step a₁ w1 ≡ just (a₁' , w1') → stepsPresUpdRel2 n name f g a₁' w1' → ΣstepsUpdRel2 name f g a₁' w1 w1' a₂ w r
      inda a₁' w1' comp' ind' =
        step-updRel2
          cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg
          (++⊆3→1 {names a₁} {names b₁} {names c₁} {dom𝕎· w1} naid)
          (++⊆3→1 {names a₂} {names b₂} {names c₂} {dom𝕎· w} nbid)
          comp' ind' ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  step-updRel2 cc gc {n} {name} {f} {g} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ ur ur₁ r₂) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQ a₁ b₁ c₁ , EQ a₂ b₂ c₂ , w1 , w , r , refl , refl , updRel2-EQ _ _ _ _ _ _ ur ur₁ r₂ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ ur ur₁ r₂ r₃) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQB a₁ b₁ c₁ d₁ , EQB a₂ b₂ c₂ d₂ , w1 , w , r , refl , refl , updRel2-EQB _ _ _ _ _ _ _ _ ur ur₁ r₂ r₃ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.AX} {.AX} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind updRel2-AX upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , AX , AX , w1 , w , r , refl , refl , updRel2-AX , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.FREE} {.FREE} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind updRel2-FREE upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FREE , FREE , w1 , w , r , refl , refl , updRel2-FREE , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(CS name1)} {.(CS name2)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-CS name1 name2 d1 d2 x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , CS _ , CS _ , w1 , w , r , refl , refl , updRel2-CS name1 name2 d1 d2 x₁ {--updRel2-CS _ x₁--} , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(NAME name1)} {.(NAME name2)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-NAME name1 name2 d1 d2 x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAME _ , NAME _ , w1 , w , r , refl , refl , updRel2-NAME name1 name2 d1 d2 x₁ {--updRel2-NAME _ x₁--} , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(FRESH a)} {.(FRESH b)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-FRESH a b ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
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
  step-updRel2 cc gc {n} {name} {f} {g} {.(LOAD a)} {.(LOAD a)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-LOAD a) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
    rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    0 , 1 , AX , AX , startNewChoices Res⊤ w1 a , startNewChoices Res⊤ w a ,
    names2ren w1 w a (names a) r , refl , refl , updRel2-AX ,
    upto𝕎-startNewChoices cc name w1 w r a (names a) upw ,
    subRen-names2ren cc w1 w r r a (names a) (dom𝕎· w1) (dom𝕎· w) ⊆-refl ⊆-refl (subRen-refl r)
  --0 , 0 , LOAD a₁ , TSQUASH a₂ , w1 , w , r , refl , refl , updRel2-TSQUASH _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-CHOOSE a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn with is-NAME a₁
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
      ind' = step-updRel2 cc gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w0} {w1} {w1'} {w} nnf cf cg (++⊆2→1 {names a₁} {names b₁} {dom𝕎· w1} naid) (++⊆2→1 {names a₂} {names b₂} {dom𝕎· w} nbid) z (stepsPresUpdRel2-CHOOSE₁→ ind) ur upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel2 cc gc {n} {name} {f} {g} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-TSQUASH a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TSQUASH a₁ , TSQUASH a₂ , w1 , w , r , refl , refl , updRel2-TSQUASH _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-TTRUNC a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TTRUNC a₁ , TTRUNC a₂ , w1 , w , r , refl , refl , updRel2-TTRUNC _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(TCONST a₁)} {.(TCONST a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-TCONST a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TCONST a₁ , TCONST a₂ , w1 , w , r , refl , refl , updRel2-TCONST _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(SUBSING a₁)} {.(SUBSING a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-SUBSING a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUBSING a₁ , SUBSING a₂ , w1 , w , r , refl , refl , updRel2-SUBSING _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.PURE} {.PURE} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind updRel2-PURE upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PURE , PURE , w1 , w , r , refl , refl , updRel2-PURE , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(TERM a₁)} {.(TERM a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-TERM a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TERM a₁ , TERM a₂ , w1 , w , r , refl , refl , updRel2-TERM _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(ENC a)} {.(ENC a)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-ENC a ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ? --0 , 0 , TERM a₁ , TERM a₂ , w1 , w , r , refl , refl , updRel2-TERM _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(DUM a₁)} {.(DUM a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-DUM a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , DUM a₁ , DUM a₂ , w1 , w , r , refl , refl , updRel2-DUM _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-FFDEFS a₁ a₂ b₁ b₂ ur ur₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w , r , refl , refl , updRel2-FFDEFS _ _ _ _ ur ur₁ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(UNIV x₁)} {.(UNIV x₁)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-UNIV x₁) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNIV _ , UNIV _ , w1 , w , r , refl , refl , updRel2-UNIV _ , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(LIFT a₁)} {.(LIFT a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-LIFT a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LIFT a₁ , LIFT a₂ , w1 , w , r , refl , refl , updRel2-LIFT _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(LOWER a₁)} {.(LOWER a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-LOWER a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LOWER a₁ , LOWER a₂ , w1 , w , r , refl , refl , updRel2-LOWER _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(SHRINK a₁)} {.(SHRINK a₂)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind (updRel2-SHRINK a₁ a₂ ur) upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SHRINK a₁ , SHRINK a₂ , w1 , w , r , refl , refl , updRel2-SHRINK _ _ ur , upw , subRen-refl r
  step-updRel2 cc gc {n} {name} {f} {g} {.(upd name f)} {.(force g)} {x} {w0} {w1} {w2} {w} {r} nnf cf cg naid nbid comp ind updRel2-upd upw gtn nnw idom idom' compat compat' wgt0 ew01 ew0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , upd name f , force g , w1 , w , r , refl , refl , updRel2-upd , upw , subRen-refl r

\end{code}
