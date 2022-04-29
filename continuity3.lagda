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
--open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
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


module continuity3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                   (F : Freeze {L} W C K P G N)
                   (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
                   (CB : ChoiceBar W M C K P G X N V F E) -- TODO - We won't need everything from there: use a different module
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
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)

{--
open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(E)
--}

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)

→ΣhighestUpdCtxt-upd : {name : Name} {f b : Term} {w : 𝕎·} {n : ℕ}
                        → # f
                        → ¬Names f
                        → stepsPresHighestℕ name f (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w
                        → ΣhighestUpdCtxt name f n (LET b (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w w
→ΣhighestUpdCtxt-upd {name} {f} {b} {w} {n} cf nnf (k , v , w' , comp , isv , ind) = {!!}



-- We also need something about the way f computes as for the proof about 'differ'
step-sat-isHighestℕ : {w1 w2 : 𝕎·} {a b : Term} {n : ℕ} {name : Name} {f : Term}
                       → step a w1 ≡ just (b , w2)
                       → stepsPresHighestℕ name f b w2
                       → updCtxt name f a
                       → ¬Names f
                       → # f
                       --→ getT 0 name w2 ≡ just (NUM n)
                       → ΣhighestUpdCtxt name f n b w1 w2
step-sat-isHighestℕ {w1} {w2} {.NAT} {b} {n} {name} {f} comp indb updCtxt-NAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAT , w1 , refl , (λ x → x , x) , updCtxt-NAT
step-sat-isHighestℕ {w1} {w2} {.QNAT} {b} {n} {name} {f} comp indb updCtxt-QNAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QNAT , w1 , refl , (λ x → x , x) , updCtxt-QNAT
step-sat-isHighestℕ {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} comp indb (updCtxt-LT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LT a b₁ , w1 , refl , (λ x → x , x) , updCtxt-LT _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} comp indb (updCtxt-QLT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QLT a b₁ , w1 , refl , (λ x → x , x) , updCtxt-QLT _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(NUM x)} {b} {n} {name} {f} comp indb (updCtxt-NUM x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NUM x , w1 , refl , (λ x → x , x) , updCtxt-NUM x
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q with k1 <? k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , c , w1 , refl , (λ x → x , x) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , d , w1 , refl , (λ x → x , x) , ctxt₃
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-IFLT₂ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt name f n b₁' w1 w1'
    ind = step-sat-isHighestℕ z (stepsPresHighestℕ-IFLT₂→ indb) ctxt₁ nnf cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt-IFLT₁ ctxt₁ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt name f n a' w1 w1'
    ind = step-sat-isHighestℕ z (stepsPresHighestℕ-IFLT₁→ indb) ctxt nnf cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} comp indb (updCtxt-PI a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PI a b₁ , w1 , refl , (λ x → x , x) , updCtxt-PI _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} comp indb (updCtxt-LAMBDA a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LAMBDA a , w1 , refl , (λ x → x , x) , updCtxt-LAMBDA _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(APPLY a b₁)} {b} {n} {name} {f} comp indb (updCtxt-APPLY a b₁ ctxt ctxt₁) nnf cf with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = concl d
  where
    d : updCtxt name f t ⊎ t ≡ updBody name f
    d = updCtxt-LAMBDA→ ctxt

    concl : updCtxt name f t ⊎ t ≡ updBody name f
            → ΣhighestUpdCtxt name f n (sub b₁ t) w1 w1
    concl (inj₁ u) = 0 , sub b₁ t , w1 , refl , (λ s → s , s) , updCtxt-sub cf ctxt₁ u
    concl (inj₂ u) rewrite u = c2
      where
        indb' : stepsPresHighestℕ name f (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        indb' rewrite u | sub-upd name f b₁ cf = indb

        c1 : ΣhighestUpdCtxt name f n (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
        c1 = {!!} --→ΣhighestUpdCtxt-upd {name} {f} {b₁} {w1} {n} cf nnf indb'

        c2 : ΣhighestUpdCtxt name f n (sub b₁ (updBody name f)) w1 w1
        c2 rewrite sub-upd name f b₁ cf = c1
... | inj₂ x with is-CS a
... |    inj₁ (name' , p) rewrite p = ⊥-elim (updCtxt-CS→ ctxt)
... |    inj₂ p = {!!}
step-sat-isHighestℕ {w1} {w2} {.(FIX a)} {b} {n} {name} {f} comp indb (updCtxt-FIX a ctxt) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} comp indb (updCtxt-LET a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SUM a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUM a b₁ , w1 , refl , (λ x → x , x) , updCtxt-SUM _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} comp indb (updCtxt-PAIR a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PAIR a b₁ , w1 , refl , (λ x → x , x) , updCtxt-PAIR _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SPREAD a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SET a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SET a b₁ , w1 , refl , (λ x → x , x) , updCtxt-SET _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-TUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TUNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt-TUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-UNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt-UNION _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-QTUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QTUNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt-QTUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(INL a)} {b} {n} {name} {f} comp indb (updCtxt-INL a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INL a , w1 , refl , (λ x → x , x) , updCtxt-INL _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(INR a)} {b} {n} {name} {f} comp indb (updCtxt-INR a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INR a , w1 , refl , (λ x → x , x) , updCtxt-INR _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} comp indb (updCtxt-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} comp indb (updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , EQ a b₁ c , w1 , refl , (λ x → x , x) , updCtxt-EQ _ _ _ ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ {w1} {w2} {.AX} {b} {n} {name} {f} comp indb updCtxt-AX nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , AX , w1 , refl , (λ x → x , x) , updCtxt-AX
step-sat-isHighestℕ {w1} {w2} {.FREE} {b} {n} {name} {f} comp indb updCtxt-FREE nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FREE , w1 , refl , (λ x → x , x) , updCtxt-FREE
step-sat-isHighestℕ {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} comp indb (updCtxt-CHOOSE a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} comp indb (updCtxt-TSQUASH a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TSQUASH a , w1 , refl , (λ x → x , x) , updCtxt-TSQUASH _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} comp indb (updCtxt-TTRUNC a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TTRUNC a , w1 , refl , (λ x → x , x) , updCtxt-TTRUNC _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} comp indb (updCtxt-TCONST a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TCONST a , w1 , refl , (λ x → x , x) , updCtxt-TCONST _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} comp indb (updCtxt-SUBSING a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUBSING a , w1 , refl , (λ x → x , x) , updCtxt-SUBSING _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(DUM a)} {b} {n} {name} {f} comp indb (updCtxt-DUM a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , DUM a , w1 , refl , (λ x → x , x) , updCtxt-DUM _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} comp indb (updCtxt-FFDEFS a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FFDEFS a b₁ , w1 , refl , (λ x → x , x) , updCtxt-FFDEFS _ _ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} comp indb (updCtxt-UNIV x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNIV x , w1 , refl , (λ x → x , x) , updCtxt-UNIV x
step-sat-isHighestℕ {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} comp indb (updCtxt-LIFT a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LIFT a , w1 , refl , (λ x → x , x) , updCtxt-LIFT _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} comp indb (updCtxt-LOWER a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LOWER a , w1 , refl , (λ x → x , x) , updCtxt-LOWER _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} comp indb (updCtxt-SHRINK a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SHRINK a , w1 , refl , (λ x → x , x) , updCtxt-SHRINK _ ctxt
step-sat-isHighestℕ {w1} {w2} {.(upd name f)} {b} {n} {name} {f} comp indb updCtxt-upd nnf cf = {!!}
-- LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1))))

{--
step-sat-isHighestℕ {w1} {w2} {.NAT} {b} {n} {name} {f} comp indb updCtxt-NAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , NAT , w1 , refl , (n , g0 , ≤-refl) , updCtxt-NAT
step-sat-isHighestℕ {w1} {w2} {.QNAT} {b} {n} {name} {f} comp indb updCtxt-QNAT nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-QNAT
step-sat-isHighestℕ {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} comp indb (updCtxt-LT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LT a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} comp indb (updCtxt-QLT a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-QLT a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(NUM x)} {b} {n} {name} {f} comp indb (updCtxt-NUM x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-NUM x
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q with k1 <? k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , ctxt₃
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  fst hn ,
  IFLT (NUM k1) (fst (snd (snd ind))) c d ,
  fst (snd (snd (snd ind))) ,
  fst (snd hn) ,
  snd (snd hn) ,
  updCtxt-IFLT (NUM k1) (fst (snd (snd ind))) c d ctxt (snd (snd (snd (snd (snd (snd ind)))))) ctxt₂ ctxt₃
  where
    ind : getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n b₁' w1'
    ind = step-sat-isHighestℕ z {!indb!} ctxt₁ nnf cf

    hn : Σ ℕ (λ k' → Σ (steps k' (IFLT (NUM k1) b₁' c d , w1') ≡ (IFLT (NUM k1) (fst (snd (snd ind))) c d , fst (snd (snd (snd ind)))))
                        (isHighestℕ {k'} {w1'} {fst (snd (snd (snd ind)))} {IFLT (NUM k1) b₁' c d} {IFLT (NUM k1) (fst (snd (snd ind))) c d} n name))
    hn = isHighestℕ-IFLT₂ {fst (snd ind)} {b₁'} {fst (snd (snd ind))} {w1'} {fst (snd (snd (snd ind)))} {n} {name} k1 c d (fst (snd (snd (snd (snd ind))))) (fst (snd (snd (snd (snd (snd ind))))))
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} comp indb (updCtxt-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf cf | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  fst ind ,
  fst hn ,
  IFLT (fst (snd (snd ind))) b₁ c d ,
  fst (snd (snd (snd ind))) ,
  fst (snd hn) ,
  snd (snd hn) ,
  updCtxt-IFLT (fst (snd (snd ind))) b₁ c d (snd (snd (snd (snd (snd (snd ind)))))) ctxt₁ ctxt₂ ctxt₃
  where
    ind : getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n a' w1'
    ind = step-sat-isHighestℕ z {!!} ctxt nnf cf

    hn : Σ ℕ (λ k' → Σ (steps k' (IFLT a' b₁ c d , w1') ≡ (IFLT (fst (snd (snd ind))) b₁ c d , fst (snd (snd (snd ind)))))
                        (isHighestℕ {k'} {w1'} {fst (snd (snd (snd ind)))} {IFLT a' b₁ c d} {IFLT (fst (snd (snd ind))) b₁ c d} n name))
    hn = isHighestℕ-IFLT₁ {fst (snd ind)} {a'} {fst (snd (snd ind))} {w1'} {fst (snd (snd (snd ind)))} {n} {name} b₁ c d (fst (snd (snd (snd (snd ind))))) (fst (snd (snd (snd (snd (snd ind))))))
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} comp indb (updCtxt-PI a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-PI a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} comp indb (updCtxt-LAMBDA a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LAMBDA a ctxt
step-sat-isHighestℕ {w1} {w2} {.(APPLY a b₁)} {b} {n} {name} {f} comp indb (updCtxt-APPLY a b₁ ctxt ctxt₁) nnf cf with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = concl d
  where
    d : updCtxt name f t ⊎ t ≡ updBody name f
    d = updCtxt-LAMBDA→ ctxt

    concl : updCtxt name f t ⊎ t ≡ updBody name f
            → getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n (sub b₁ t) w1
    concl (inj₁ u) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-sub cf ctxt₁ u
    concl (inj₂ u) rewrite u = c2
      where
        c1 : ΣhighestUpdCtxt name f n (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
             --updCtxt name f (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))))
        c1 = {!!}
-- This is not going to work.
-- Instead, we need to prove that b reduces to a term b' such that updCtxt name f b'
-- and that this computation satisfies isHighestℕ

        c2 : getT≤ℕ w1 n name × ΣhighestUpdCtxt name f n (sub b₁ (updBody name f)) w1
        c2 rewrite sub-upd name f b₁ cf = (n , g0 , ≤-refl) , c1 -- 0 , _ , _ , refl , (n , g0 , ≤-refl) , c1
... | inj₂ x with is-CS a
... |    inj₁ (name' , p) rewrite p = ⊥-elim (updCtxt-CS→ ctxt)
... |    inj₂ p = {!!}
step-sat-isHighestℕ {w1} {w2} {.(FIX a)} {b} {n} {name} {f} comp indb (updCtxt-FIX a ctxt) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} comp indb (updCtxt-LET a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SUM a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SUM a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} comp indb (updCtxt-PAIR a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SPREAD a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} comp indb (updCtxt-SET a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SET a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-TUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TUNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-UNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-UNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} comp indb (updCtxt-QTUNION a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-QTUNION a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(INL a)} {b} {n} {name} {f} comp indb (updCtxt-INL a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-INL a ctxt
step-sat-isHighestℕ {w1} {w2} {.(INR a)} {b} {n} {name} {f} comp indb (updCtxt-INR a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-INR a ctxt
step-sat-isHighestℕ {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} comp indb (updCtxt-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} comp indb (updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-EQ a b₁ c ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ {w1} {w2} {.AX} {b} {n} {name} {f} comp indb updCtxt-AX nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-AX
step-sat-isHighestℕ {w1} {w2} {.FREE} {b} {n} {name} {f} comp indb updCtxt-FREE nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-FREE
step-sat-isHighestℕ {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} comp indb (updCtxt-CHOOSE a b₁ ctxt ctxt₁) nnf cf = {!!}
step-sat-isHighestℕ {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} comp indb (updCtxt-TSQUASH a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TSQUASH a ctxt
step-sat-isHighestℕ {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} comp indb (updCtxt-TTRUNC a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TTRUNC a ctxt
step-sat-isHighestℕ {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} comp indb (updCtxt-TCONST a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-TCONST a ctxt
step-sat-isHighestℕ {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} comp indb (updCtxt-SUBSING a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SUBSING a ctxt
step-sat-isHighestℕ {w1} {w2} {.(DUM a)} {b} {n} {name} {f} comp indb (updCtxt-DUM a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-DUM a ctxt
step-sat-isHighestℕ {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} comp indb (updCtxt-FFDEFS a b₁ ctxt ctxt₁) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-FFDEFS a b₁ ctxt ctxt₁
step-sat-isHighestℕ {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} comp indb (updCtxt-UNIV x) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-UNIV x
step-sat-isHighestℕ {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} comp indb (updCtxt-LIFT a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LIFT a ctxt
step-sat-isHighestℕ {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} comp indb (updCtxt-LOWER a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-LOWER a ctxt
step-sat-isHighestℕ {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} comp indb (updCtxt-SHRINK a ctxt) nnf cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = (n , g0 , ≤-refl) , 0 , _ , _ , refl , (n , g0 , ≤-refl) , updCtxt-SHRINK a ctxt
step-sat-isHighestℕ {w1} {w2} {.(upd name f)} {b} {n} {name} {f} comp indb updCtxt-upd nnf cf = {!!}
-- LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1))))
--}



steps→𝕎s : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term}
             → steps k (a , w1) ≡ (b , w2)
             → List 𝕎·
steps→𝕎s {0} {w1} {w2} {a} {b} comp = Data.List.[ w1 ]
steps→𝕎s {suc k} {w1} {w2} {a} {b} comp with step a w1
... | just (x , w) = w1 ∷ steps→𝕎s {k} {w} {w2} {x} {b} comp
... | nothing = Data.List.[ w1 ]



isHighestℕ→ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name)
               (comp : steps k (a , w1) ≡ (b , w2))
               → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
               → (w : 𝕎·) → w ∈ steps→𝕎s {k} {w1} {w2} {a} {b} comp → getT≤ℕ w n name
isHighestℕ→ {0} {w1} {w2} {a} {b} n name comp h w (here px) rewrite px = h
isHighestℕ→ {suc k} {w1} {w2} {a} {b} n name comp h w i with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = c i
  where
    c : w ∈ (w1 ∷ steps→𝕎s {k} {w'} {w2} {a'} {b} comp) → getT≤ℕ w n name
    c (here px) rewrite px = fst h
    c (there j) = isHighestℕ→ {k} {w'} {w2} {a'} {b} n name comp (snd h) w j
... | inj₂ z rewrite z = c i
  where
    c : w ∈ (w1 ∷ []) → getT≤ℕ w n name
    c (here px) rewrite px = h



→isHighestℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name)
               (comp : steps k (a , w1) ≡ (b , w2))
               → ((w : 𝕎·) → w ∈ steps→𝕎s {k} {w1} {w2} {a} {b} comp → getT≤ℕ w n name)
               → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
→isHighestℕ {0} {w1} {w2} {a} {b} n name comp h = h w1 (here refl)
→isHighestℕ {suc k} {w1} {w2} {a} {b} n name comp h with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = h w1 (here refl) , →isHighestℕ {k} {w'} {w2} {a'} {b} n name comp (λ w i → h w (there i))
... | inj₂ z rewrite z = h w1 (here refl)



stepsVal→ : (a b : Term) (w w' : 𝕎·) (n : ℕ) → isValue a → steps n (a , w) ≡ (b , w') → b ≡ a × w' ≡ w
stepsVal→ a b w w' n isv comp rewrite stepsVal a w n isv | pair-inj₁ comp | pair-inj₂ comp = refl , refl



val-steps→ : {w w1 w2 : 𝕎·} {a b v : Term} {n m : ℕ} (i : ℕ) (name : Name)
              → isValue v
              → (comp1 : steps m (a , w) ≡ (b , w1))
              → (comp2 : steps n (a , w) ≡ (v , w2))
              → Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
                  isHighestℕ {m} {w} {w1} {a} {b} i name comp1
                  → isHighestℕ {k} {w1} {w2} {b} {v} i name comp
                  → isHighestℕ {n} {w} {w2} {a} {v} i name comp2))
val-steps→ {w} {w1} {w2} {a} {b} {v} {n} {0} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = n , ≤-refl , comp2 , λ x y → y
val-steps→ {w} {w1} {w2} {a} {b} {v} {0} {suc m} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
        | stepVal a w isv
  = 0 , ≤-refl , ≡pair (fst (stepsVal→ a b w w1 m isv comp1)) (snd (stepsVal→ a b w w1 m isv comp1)) , λ (x1 , x2) x3 → x1
val-steps→ {w} {w1} {w2} {a} {b} {v} {suc n} {suc m} i name isv comp1 comp2 with step⊎ a w
... | inj₁ (a' , w' , z) rewrite z =
  fst q , ≤-trans (fst (snd q)) (<⇒≤ (n<1+n n)) , fst (snd (snd q)) , λ (x1 , x2) x3 → x1 , snd (snd (snd q)) x2 x3
  where
    q : Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
           isHighestℕ {m} {w'} {w1} {a'} {b} i name comp1
           → isHighestℕ {k} {w1} {w2} {b} {v} i name comp
           → isHighestℕ {n} {w'} {w2} {a'} {v} i name comp2))
    q = val-steps→ {w'} {w1} {w2} {a'} {b} {v} {n} {m} i name isv comp1 comp2
... | inj₂ z rewrite z
           | pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
           | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = 0 , _≤_.z≤n , refl , λ x y → x


isHighestℕ→getT≤ℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name) (comp : steps k (a , w1) ≡ (b , w2))
                       → isHighestℕ {k} {w1} {w2} {a} {b} n name comp
                       → getT≤ℕ w1 n name
isHighestℕ→getT≤ℕ {0} {w1} {w2} {a} {b} n name comp h = h
isHighestℕ→getT≤ℕ {suc k} {w1} {w2} {a} {b} n name comp h with step⊎ a w1
... | inj₁ (a' , w' , z) rewrite z = fst h
... | inj₂ z rewrite z = h



-- We also need something about the way f computes as for the proof about 'differ'
steps-sat-isHighestℕ-aux : {name : Name} {f : Term}
                            → ¬Names f
                            → # f
                            → (k : ℕ)
                            → (ind : (k' : ℕ) → k' < k → presHighestℕ name f k')
                            → presHighestℕ name f k
steps-sat-isHighestℕ-aux {name} {f} nnf cf 0 ind {w1} {w2} {a} {b} {n} comp isvb ctxt g0
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp)
  = g0 --n , g0 , ≤-refl
steps-sat-isHighestℕ-aux {name} {f} nnf cf (suc k) ind {w1} {w2} {a} {b} {n} comp isvb ctxt g0 with step⊎ a w1
... | inj₁ (x , w , p) rewrite p =
  fst (ii gw') , snd (snd (snd comp2)) (snd (ii gw')) comp3
  where
    ind0 : (k' : ℕ) → k' < suc k → presHighestℕ name f k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presHighestℕ name f k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

    q : ΣhighestUpdCtxt name f n x w1 w
    q = step-sat-isHighestℕ p (k , b , w2 , comp , isvb , ind1) ctxt nnf cf

    k' : ℕ
    k' = fst q

    x' : Term
    x' = fst (snd q)

    w' : 𝕎·
    w' = fst (snd (snd q))

    comp1 : steps k' (x , w) ≡ (x' , w')
    comp1 = fst (snd (snd (snd q)))

    ii : getT≤ℕ w' n name → (getT≤ℕ w1 n name × isHighestℕ {k'} {w} {w'} {x} {x'} n name comp1)
    ii = fst (snd (snd (snd (snd q))))

    uc : updCtxt name f x'
    uc = snd (snd (snd (snd (snd q))))

    comp2 : Σ ℕ (λ k0 → k0 ≤ k × Σ (steps k0 (x' , w') ≡ (b , w2)) (λ cmp →
                  isHighestℕ {k'} {w} {w'} {x} {x'} n name comp1
                  → isHighestℕ {k0} {w'} {w2} {x'} {b} n name cmp
                  → isHighestℕ {k} {w} {w2} {x} {b} n name comp))
    comp2 = val-steps→ {w} {w'} {w2} {x} {x'} {b} {k} {k'} n name isvb comp1 comp

    comp3 : isHighestℕ {fst comp2} {w'} {w2} {x'} {b} n name (fst (snd (snd comp2)))
    comp3 = ind1 (fst comp2) (fst (snd comp2)) {w'} {w2} {x'} {b} {n} (fst (snd (snd comp2))) isvb uc g0

    gw' : getT≤ℕ w' n name
    gw' = isHighestℕ→getT≤ℕ {proj₁ comp2} {w'} {w2} {x'} {b} n name (proj₁ (snd (snd comp2))) comp3
... | inj₂ p rewrite p | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = g0 --n , g0 , ≤-refl



-- We also need something about the way f computes as for the proof about 'differ'
steps-sat-isHighestℕ : {name : Name} {f : Term} {k : ℕ}
                        → ¬Names f
                        → # f
                        → presHighestℕ name f k
steps-sat-isHighestℕ {name} {f} {k} nnf cf = <ℕind _ (steps-sat-isHighestℕ-aux {name} {f} nnf cf) k





-- define an 'external' version of #νtestM that follows the computation of (APPLY F f), and keeps
-- track of the highest number f is applied to, and prove that this 'external' version returns
-- the same value as the 'internal' one (i.e., #νtestM)
foo : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
      {i : ℕ} {w : 𝕎·} {F f g : CTerm}
      → #¬Names F
      → #¬Names f
      → #¬Names g
      → ∈Type i w #BAIRE→NAT F
      → ∈Type i w #BAIRE f
      → ∈Type i w #BAIRE g
      → equalInType i w (#BAIREn (#νtestM F f)) f g
--       ((n : ℕ) → n < ? → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
      → equalInType i w #NAT (#APPLY F f) (#APPLY F g)
foo nc cn kb gc {i} {w} {F} {f} {g} nnF nnf nng ∈F ∈f ∈g eqb =
  equalInType-trans (equalInType-APPLY-force ∈F ∈f) (equalInType-trans eqf (equalInType-sym (equalInType-APPLY-force ∈F ∈g)))
  where
    neqt : NATeq w (#νtestM F f) (#νtestM F f)
    neqt = νtestM-NAT nc cn kb gc i w F f nnF nnf ∈F ∈f

    tn : ℕ
    tn = fst neqt

    x : NATeq w (#νtestM F f) (#NUM tn)
    x = tn , fst (snd neqt) , compAllRefl _ _

    cx : #νtestM F f #⇛ #NUM tn at w
    cx = NATeq→⇛ {w} {#νtestM F f} x

    eqb1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#NATn (#νtestM F f)) a₁ a₂
                         → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    eqb1 = equalInType-FUN→ (≡CTerm→equalInType (≡BAIREn (#νtestM F f)) eqb)

    eqb2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                         → □· w' (λ w'' _ → Σ ℕ (λ k → a₁ #⇛ #NUM k at w'' × a₂ #⇛ #NUM k at w'' × k < tn))
                         → □· w' (λ w'' _ → NATeq w'' (#APPLY f a₁) (#APPLY g a₂)))
    eqb2 w1 e1 a₁ a₂ eqa = equalInType-NAT→ i w1 (#APPLY f a₁) (#APPLY g a₂) (eqb1 w1 e1 a₁ a₂ (→equalInType-NATn (∀𝕎-mon e1 cx) eqa))

    eqb3 : ∀𝕎 w (λ w' _ → (k : ℕ) → k < tn
                         → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
    eqb3 w1 e1 k ltk = kb z w1 (⊑-refl· _)
      where
        z : □· w1 (λ w'' _ → NATeq w'' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        z = eqb2 w1 e1 (#NUM k) (#NUM k) (Mod.∀𝕎-□ M (λ w2 e2 → k , #compAllRefl (#NUM k) w2 , #compAllRefl (#NUM k) w2 , ltk))

    inn : ∈Type i w #NAT (#APPLY F (#force f))
    inn = equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈f))

    aw : ∀𝕎 w (λ w' _ → NATeq w' (#APPLY F (#force f)) (#APPLY F (#force f)) → NATeq w' (#APPLY F (#force f)) (#APPLY F (#force g)))
    aw w1 e1 (n , comp1 , comp2) = n , comp1 , ¬Names→⇓→⇛ w1 w1 ⌜ #APPLY F (#force g) ⌝ (NUM n) (#¬Names-APPLY {F} {#force g} nnF (#¬Names-force {g} nng)) comp
      where
        comp : #APPLY F (#force g) #⇓ #NUM n at w1
        comp = {!!}

-- We need to prove something like this, where w1 and w1' differ only in name
-- (we should be able to prove that for any world w3 between w1' and w2 (Σ ℕ (λ j → getT 0 name w3 ≡ just (NUM j) × j ≤ m0)) -- see steps-sat-isHighestℕ being proved below
-- (and then define a 'differ' relation relating CTXT(upd name f)/CTXT(force f)/CTXT(force g))
--  → APPLY F (upd name f) ⇓ NUM n from w1' to w2 -- These 3 hypotheses come from #νtestM⇓→
--  → getT 0 name w2 ≡ just (NUM m0)
--  → m0 ≤ m
--  → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < m → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k))) -- from eqb2
--  → APPLY F (force f) ⇓ NUM n at w1
--  → APPLY F (force g) ⇓ NUM n at w1

    eqf : equalInType i w #NAT (#APPLY F (#force f)) (#APPLY F (#force g))
    eqf = →equalInType-NAT i w (#APPLY F (#force f)) (#APPLY F (#force g)) (Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w (#APPLY F (#force f)) (#APPLY F (#force f)) inn))




continuity : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
             (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → #¬Names F
             → #¬Names f
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → ∈Type i w (#contBody F f) (#PAIR (#νtestM F f) #lam3AX)
continuity nc cn kb gc i w F f nnF nnf ∈F ∈f =
  ≡CTerm→equalInType (sym (#contBody≡ F f)) h0
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestM F f) #lam3AX)
                                (#PAIR (#νtestM F f) #lam3AX))
    aw w1 e1 =
      #νtestM F f , #νtestM F f , #lam3AX , #lam3AX ,
      testM-NAT nc cn kb gc i w1 F f nnF nnf (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) ,
      #compAllRefl (#PAIR (#νtestM F f) #lam3AX) w1 ,
      #compAllRefl (#PAIR (#νtestM F f) #lam3AX) w1 ,
      eql1
      where
        ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                             → equalTypes i w2
                                           (#FUN (#FFDEFS #BAIRE g₁) (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f))) (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                           (#FUN (#FFDEFS #BAIRE g₂) (#FUN (#EQ f g₂ (#BAIREn (#νtestM F f))) (#EQ (#APPLY F f) (#APPLY F g₂) #NAT))))
        ea2 w2 e2 g₁ g₂ eg =
          eqTypesFUN←
            (eqTypesFFDEFS← eqTypesBAIRE eg)
            (eqTypesFUN←
              (eqTypesEQ← (→equalTypesBAIREn i w2 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                          (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) eg))
              (eqTypesEQ← eqTypesNAT
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg)))

        eql2 : equalInType i w1 (#PI #BAIRE
                                     (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                              (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ #νtestM F f ⌟))
                                                       (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                  #lam3AX
                                  #lam3AX
        eql2 = equalInType-PI
                 (λ w2 e2 → eqTypesBAIRE)
                 (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₁)) (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₂)) (ea2 w2 e2 g₁ g₂ eg))
                 aw2
          where
            aw3 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                                  → equalInType i w2 (#FUN (#FFDEFS #BAIRE g₁)
                                                           (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f)))
                                                                 (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                                 (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
            aw3 w2 e2 g₁ g₂ eg =
              equalInType-FUN
                (eqTypesFFDEFS← eqTypesBAIRE (equalInType-refl eg))
                (eqTypesFUN←
                  (eqTypesEQ← (→equalTypesBAIREn i w2 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                              (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                              (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-refl eg)))
                  (eqTypesEQ← eqTypesNAT
                              (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                              (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-refl eg))))
                aw4
              where
                aw4 : ∀𝕎 w2 (λ w' _ → (x₁ x₂ : CTerm)
                                     → equalInType i w' (#FFDEFS #BAIRE g₁) x₁ x₂
                                     → equalInType i w' (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f)))
                                                               (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                                                         (#APPLY (#APPLY #lam3AX g₁) x₁)
                                                         (#APPLY (#APPLY #lam3AX g₂) x₂))
                aw4 w3 e3 x₁ x₂ ex =
                  equalInType-FUN
                    (eqTypesEQ← (→equalTypesBAIREn i w3 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))))
                                 (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                                 (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-refl (equalInType-mon eg w3 e3))))
                    (eqTypesEQ← eqTypesNAT
                                 (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                                 (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-refl (equalInType-mon eg w3 e3))))
                    aw5
                  where
                    aw5 : ∀𝕎 w3 (λ w' _ → (y₁ y₂ : CTerm)
                                        → equalInType i w' (#EQ f g₁ (#BAIREn (#νtestM F f))) y₁ y₂
                                        → equalInType i w' (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)
                                                            (#APPLY (#APPLY (#APPLY #lam3AX g₁) x₁) y₁)
                                                            (#APPLY (#APPLY (#APPLY #lam3AX g₂) x₂) y₂))
                    aw5 w4 e4 y₁ y₂ ey =
                      equalInType-EQ
                        eqTypesNAT
                        concl
                      where
                        hyp : □· w4 (λ w5 _ → equalInType i w5 (#BAIREn (#νtestM F f)) f g₁)
                        hyp = equalInType-EQ→ ey

                        ff : □· w3 (λ w' _ → FFDEFSeq g₁ (equalInType i w' #BAIRE) w' x₁ x₂)
                        ff = equalInTypeFFDEFS→ ex

                        aw6 : ∀𝕎 w4 (λ w' e' → equalInType i w' (#BAIREn (#νtestM F f)) f g₁
                                              → ↑wPred (λ w'' _ → FFDEFSeq g₁ (equalInType i w'' #BAIRE) w'' x₁ x₂) e4 w' e'
                                              → equalInType i w' #NAT (#APPLY F f) (#APPLY F g₁))
                        aw6 w5 e5 h1 (g , h2 , nng) = equalInType-trans cc (∈BAIRE→NAT→ (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-sym h2))
                          where
                            h3 : equalInType i w5 (#BAIREn (#νtestM F f)) f g
                            h3 = equalInType-BAIREn-BAIRE-trans h2 h1 (testM-NAT nc cn kb gc i w5 F f nnF nnf (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))))

                            cc : equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)
                            cc = {!!}

-- → #¬Names F
-- → #¬Names f
-- → #¬Names g
-- → equalInType i w5 (#BAIREn (#νtestM F f)) f g
--       ((n : ℕ) → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
-- → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)

                        concl : □· w4 (λ w5 _ → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g₁))
                        concl = ∀𝕎-□Func2 aw6 hyp (Mod.↑□ M ff e4)

            aw2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                                  → equalInType i w2 (sub0 g₁ (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                                                        (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ #νtestM F f ⌟))
                                                                                 (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                                 (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
            aw2 w2 e2 g₁ g₂ eg = ≡CTerm→equalInType (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₁)) (aw3 w2 e2 g₁ g₂ eg)

        eql1 : equalInType i w1 (sub0 (#νtestM F f)
                                      (#[0]PI #[0]BAIRE
                                              (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                       (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                                 #lam3AX
                                 #lam3AX
        eql1 = ≡CTerm→equalInType (sym (sub0-contBodyPI F f (#νtestM F f))) eql2

    seq : □· w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestM F f) #lam3AX)
                                (#PAIR (#νtestM F f) #lam3AX))
    seq = Mod.∀𝕎-□ M aw

    h0 : ∈Type i w (#SUM #NAT
                         (#[0]PI #[0]BAIRE
                                 (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                          (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                   (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                   (#PAIR (#νtestM F f) #lam3AX)
    h0 = equalInType-SUM (λ w' e' → eqTypesNAT) (equalTypes-contBodyPI i w F f ∈F ∈f) seq

\end{code}
