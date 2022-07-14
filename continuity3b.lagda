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


module continuity3b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)


-- This is similar to step-sat-isHighestℕ in continuity3.lagda.
-- updCtxt2's properties can essentially be copied from terms3b.lagda as this is almost the same definition.
-- We only need to prove that name's value increases, but for this only upd must update name.
-- So we
--   (1) require that ¬ name ∈ names f and
--   (2) that updCtxt2 name f (NAME name') only when ¬ name ≡ name'
step-sat-isHighestℕ2 : (cc : ContConds) (gc : get-choose-ℕ) {w1 w2 : 𝕎·} {a b : Term} {n : ℕ} {name : Name} {f : Term}
                       → compatible· name w1 Res⊤
                       → ∀𝕎-get0-NUM w1 name
                       → step a w1 ≡ just (b , w2)
                       → stepsPresHighestℕ2 name f b w2
                       → updCtxt2 name f a
                       → ¬ name ∈ names f -- This is so that (upd name f) does not update name when computing f
                       → ¬ name ∈ names𝕎· w1 -- This is so that reading choices does not bring name
                       → name ∈ dom𝕎· w1 -- this is so that FRESH does not pick name
                       → # f
                       → ΣhighestUpdCtxt2 name f n b w1 w2
step-sat-isHighestℕ2 cc gc {w1} {w2} {.NAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-NAT nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAT , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NAT
step-sat-isHighestℕ2 cc gc {w1} {w2} {.QNAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-QNAT nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QNAT , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-QNAT
step-sat-isHighestℕ2 cc gc {w1} {w2} {.TNAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-TNAT nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TNAT , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TNAT
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LT a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-QLT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QLT a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-QLT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(NUM x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-NUM x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NUM _ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NUM _
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(IFLT a b c d)} {x} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf with is-NUM a
... | inj₁ (k1 , p) rewrite p with is-NUM b
... |    inj₁ (k2 , q) rewrite q with k1 <? k2
... |       yes r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , c , w1 , refl , (λ x → x , x) , (nnw , idom) , ctxt₂
... |       no r rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , d , w1 , refl , (λ x → x , x) , (nnw , idom) , ctxt₃
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(IFLT a b c d)} {x} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf | inj₁ (k1 , p) | inj₂ q with step⊎ b w1
... |       inj₁ (b' , w1' , z) rewrite p | z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-IFLT₂ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt2 name f n b' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {b} {b'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-IFLT₂→ indb) ctxt₁ nnf nnw idom cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(IFLT a b c d)} {x} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-IFLT₁ ctxt₁ ctxt₂ ctxt₃ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-IFLT₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUC a ctxt) nnf nnw idom cf with is-NUM a
... | inj₁ (k1 , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , NUM (suc k1) , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NUM _
... | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-SUC₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-SUC₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-PI a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PI a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-PI _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LAMBDA a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LAMBDA a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LAMBDA _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf with is-LAM g
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  concl d
  where
    d : updCtxt2 name f t ⊎ t ≡ updBody name f
    d = updCtxt2-LAMBDA→ ctxt

    concl : updCtxt2 name f t ⊎ t ≡ updBody name f
            → ΣhighestUpdCtxt2 name f n (sub a t) w1 w1
    concl (inj₁ u) = 0 , sub a t , w1 , refl , (λ s → s , s) , (nnw , idom) , updCtxt2-sub cf u ctxt₁
    concl (inj₂ u) rewrite u = c2
      where
        indb' : stepsPresHighestℕ2 name f (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        indb' rewrite u | sub-upd name f a cf = indb

        c1 : ΣhighestUpdCtxt2 name f n (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
        c1 = →ΣhighestUpdCtxt2-upd cc gc {name} {f} {a} {w1} {n} compat wgt0 cf nnf nnw idom ctxt₁ indb'

        c2 : ΣhighestUpdCtxt2 name f n (sub a (updBody name f)) w1 w1
        c2 rewrite sub-upd name f a cf = c1
... | inj₂ x with is-CS g
... |    inj₁ (name' , p) rewrite p with is-NUM a
... |       inj₁ (m , q) rewrite q with getT⊎ m name' w1
... |          inj₁ (c , r) rewrite r | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , c , w1 , refl , (λ s → s , s) , (nnw , idom) , ¬∈names𝕎→updCtxt2 cc f name name' m c w1 r nnw
... |          inj₂ r rewrite r = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf | inj₂ x | inj₁ (name' , p) | inj₂ y with step⊎ a w1
... |          inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-APPLY₂ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-APPLY₂→ indb) ctxt₁ nnf nnw idom cf
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf | inj₂ x | inj₂ y with step⊎ g w1
... | inj₁ (g' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-APPLY₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n g' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {g} {g'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-APPLY₁→ indb) ctxt nnf nnw idom cf
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FIX a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FIX a ctxt) nnf nnw idom cf with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  concl d
  where
    d : updCtxt2 name f t ⊎ t ≡ updBody name f
    d = updCtxt2-LAMBDA→ ctxt

    concl : updCtxt2 name f t ⊎ t ≡ updBody name f
            → ΣhighestUpdCtxt2 name f n (sub (FIX (LAMBDA t)) t) w1 w1
    concl (inj₁ u) = 0 , sub (FIX (LAMBDA t)) t , w1 , refl , (λ s → s , s) , (nnw , idom) , updCtxt2-sub cf u (updCtxt2-FIX _ ctxt)
    concl (inj₂ u) rewrite u = c2 --c2
      where
        indb' : stepsPresHighestℕ2 name f (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        indb' rewrite u | sub-upd name f (FIX (upd name f)) cf = indb

        c1 : ΣhighestUpdCtxt2 name f n (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 w1
        c1 = →ΣhighestUpdCtxt2-upd cc gc {name} {f} {FIX (upd name f)} {w1} {n} compat wgt0 cf nnf nnw idom (updCtxt2-FIX _ updCtxt2-upd) indb'

        c2 : ΣhighestUpdCtxt2 name f n (sub (FIX (upd name f)) (updBody name f)) w1 w1
        c2 rewrite sub-upd name f (FIX (upd name f)) cf = c1
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-FIX₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-FIX₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LET a b₁ ctxt ctxt₁) nnf nnw idom cf with isValue⊎ a
... | inj₁ x rewrite  sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub a b₁ , w1 , refl , (λ s → s , s) , (nnw , idom) , updCtxt2-sub cf ctxt₁ ctxt
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-LET₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-LET₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUM a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUM a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SUM _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-PAIR a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PAIR a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-PAIR _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SPREAD a b₁ ctxt ctxt₁) nnf nnw idom cf with is-PAIR a
... | inj₁ (u , v , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub v (sub u b₁) , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-sub cf (updCtxt2-sub cf ctxt₁ (updCtxt2-PAIR→₁ ctxt)) (updCtxt2-PAIR→₂ ctxt)
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-SPREAD₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-SPREAD₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SET a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SET a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SET _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(ISECT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-ISECT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , ISECT a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-ISECT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TUNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-UNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-UNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-QTUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QTUNION a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-QTUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(INL a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INL a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INL a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-INL _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(INR a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INR a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INR a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-INR _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf with is-INL a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub t b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-sub cf ctxt₁ (updCtxt2-INL→ ctxt)
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , sub t c , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-sub cf ctxt₂ (updCtxt2-INR→ ctxt)
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-DECIDE₁ ctxt₁ ctxt₂ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-DECIDE₁→ indb) ctxt nnf nnw idom cf
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , EQ a b₁ c , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-EQ _ _ _ ctxt ctxt₁ ctxt₂
step-sat-isHighestℕ2 cc gc {w1} {w2} {.AX} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-AX nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , AX , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-AX
step-sat-isHighestℕ2 cc gc {w1} {w2} {.FREE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-FREE nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FREE , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-FREE
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(CS name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CS name') nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , CS name' , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-CS _
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(NAME name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-NAME name' x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAME name' , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-NAME _ x
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FRESH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FRESH a ctxt) nnf nnw idom cf
  rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
  = 0 , shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a) , startNewChoiceT Res⊤ w1 a ,
    refl , (λ x → gt' x , x) , (nnw' , idom') , upd1
  where
    gt' : getT≤ℕ (startNewChoiceT Res⊤ w1 a) n name → getT≤ℕ w1 n name
    gt' z rewrite ∈dom𝕎→getT-startNewChoiceT cc name 0 Res⊤ a w1 idom = z

    nnw' : ¬ name ∈ names𝕎· (startNewChoiceT Res⊤ w1 a)
    nnw' = λ z → nnw (∈names𝕎-startNewChoiceT→ cc name w1 a z)

    idom' : name ∈ dom𝕎· (startNewChoiceT Res⊤ w1 a)
    idom' = dom𝕎-startNewChoiceT cc name w1 a idom

    imp1 : (x : Name) →  x ∈ names (renn 0 (newChoiceT+ w1 a) a) → ¬ x ≡ 0
    imp1 x i z rewrite z = ⊥-elim (suc-≢-0 {newChoiceT w1 a} (sym (fst (∈names-renn-same {0} {newChoiceT+ w1 a} {a} i))))

    imp2 : 0 ∈ names (renn 0 (newChoiceT+ w1 a) a) → 0 < 0
    imp2 z = ⊥-elim (suc-≢-0 {newChoiceT w1 a} (sym (fst (∈names-renn-same {0} {newChoiceT+ w1 a} {a} z))))

    upd3 : updCtxt2 (suc name) (shiftNameUp 0 f) (renn 0 (newChoiceT+ w1 a) a)
    upd3 = updCtxt2-renn (suc name) 0 (newChoiceT+ w1 a) (shiftNameUp 0 f) a (suc-≢-0 {name}) (∈dom𝕎→¬s≡newChoiceT+ name w1 a idom) (¬0∈names-shiftNameUp f) (→#shiftNameUp 0 {f} cf) ctxt

    upd2 : updCtxt2 (sucIf≤ 0 name) (shiftNameUp 0 f) (renn 0 (newChoiceT+ w1 a) a)
    upd2 rewrite sym (suc≡sucIf≤0 name) = upd3

    upd1 : updCtxt2 name f (shiftNameDown 0 (renn 0 (newChoiceT+ w1 a) a))
    upd1 = →updCtxt2-shiftNameDown 0 {name} {f} cf {renn 0 (newChoiceT+ w1 a) a} imp1 imp2 upd2
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LOAD a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LOAD a) nnf nnw idom cf
  rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = concl
  where
   concl : ΣhighestUpdCtxt2 name f n AX w1 (startNewChoices Res⊤ w1 a)
   concl = ΣhighestUpdCtxt2-startNewChoices cc name f n w1 a nnw idom
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CHOOSE a b₁ ctxt ctxt₁) nnf nnw idom cf with is-NAME a
... | inj₁ (nm , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  0 , AX , chooseT nm w1 b₁ , refl ,
  choose-pres-getT≤ℕ cc name nm w1 b₁ n (updCtxt2-NAME→ ctxt) ,
  choose-pres-∈names𝕎 cc name nm w1 b₁ nnw idom ,
  updCtxt2-AX
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1' , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  ΣhighestUpdCtxt2-CHOOSE₁ ctxt₁ ind
  where
    ind : ΣhighestUpdCtxt2 name f n a' w1 w1'
    ind = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (stepsPresHighestℕ2-CHOOSE₁→ indb) ctxt nnf nnw idom cf
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TSQUASH a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TSQUASH a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TSQUASH _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TTRUNC a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TTRUNC a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TTRUNC _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TCONST a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TCONST a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-TCONST _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUBSING a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUBSING a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SUBSING _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.PURE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-PURE nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PURE , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-PURE
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(DUM a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-DUM a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , DUM a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-DUM _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FFDEFS a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FFDEFS a b₁ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-FFDEFS _ _ ctxt ctxt₁
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-UNIV x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNIV _ , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-UNIV _
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LIFT a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LIFT a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LIFT _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LOWER a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LOWER a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-LOWER _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SHRINK a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SHRINK a , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-SHRINK _ ctxt
step-sat-isHighestℕ2 cc gc {w1} {w2} {.(upd name f)} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-upd nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , upd name f , w1 , refl , (λ x → x , x) , (nnw , idom) , updCtxt2-upd



∈names𝕎→¬∈name𝕎ᵣ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (name : Name)
                     (comp : steps k (a , w1) ≡ (b , w2))
                     → ∈names𝕎 {k} {w1} {w2} {a} {b} name comp
                     → ¬ name ∈ names𝕎· w2
∈names𝕎→¬∈name𝕎ᵣ {0} {w1} {w2} {a} {b} name comp inw
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp)
  = fst inw
∈names𝕎→¬∈name𝕎ᵣ {suc k} {w1} {w2} {a} {b} name comp inw with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z = ∈names𝕎→¬∈name𝕎ᵣ {k} {w1'} {w2} {a'} {b} name comp (snd (snd inw))
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = fst inw



∈names𝕎→∈dom𝕎ᵣ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (name : Name)
                     (comp : steps k (a , w1) ≡ (b , w2))
                     → ∈names𝕎 {k} {w1} {w2} {a} {b} name comp
                     → name ∈ dom𝕎· w2
∈names𝕎→∈dom𝕎ᵣ {0} {w1} {w2} {a} {b} name comp inw
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp)
  = snd inw
∈names𝕎→∈dom𝕎ᵣ {suc k} {w1} {w2} {a} {b} name comp inw with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z = ∈names𝕎→∈dom𝕎ᵣ {k} {w1'} {w2} {a'} {b} name comp (snd (snd inw))
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = snd inw



val-steps→names : {w w1 w2 : 𝕎·} {a b v : Term} {n m : ℕ} (i : ℕ) (name : Name)
              → isValue v
              → (comp1 : steps m (a , w) ≡ (b , w1))
              → (comp2 : steps n (a , w) ≡ (v , w2))
              → Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
                  (isHighestℕ {m} {w} {w1} {a} {b} i name comp1
                   → isHighestℕ {k} {w1} {w2} {b} {v} i name comp
                   → isHighestℕ {n} {w} {w2} {a} {v} i name comp2)
                  × (∈names𝕎 {m} {w} {w1} {a} {b} name comp1
                     → ∈names𝕎 {k} {w1} {w2} {b} {v} name comp
                     → ∈names𝕎 {n} {w} {w2} {a} {v} name comp2)))
val-steps→names {w} {w1} {w2} {a} {b} {v} {n} {0} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1)
  = n , ≤-refl , comp2 , (λ x y → y) , (λ x y → y)
val-steps→names {w} {w1} {w2} {a} {b} {v} {0} {suc m} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
        | stepVal a w isv
  = 0 , ≤-refl ,
    ≡pair (fst (stepsVal→ a b w w1 m isv comp1)) (snd (stepsVal→ a b w w1 m isv comp1)) ,
    (λ (x1 , x2) x3 → x1) ,
    (λ (x1 , x2 , x3) (y1 , y2) → x1 , x2)
val-steps→names {w} {w1} {w2} {a} {b} {v} {suc n} {suc m} i name isv comp1 comp2 with step⊎ a w
... | inj₁ (a' , w' , z) rewrite z =
  fst q , ≤-trans (fst (snd q)) (<⇒≤ (n<1+n n)) , fst (snd (snd q)) ,
  (λ (x1 , x2) x3 → x1 , fst (snd (snd (snd q))) x2 x3) ,
  (λ (x1 , x2 , x3) y → x1 , x2 , snd (snd (snd (snd q))) x3 y)
  where
    q : Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
           (isHighestℕ {m} {w'} {w1} {a'} {b} i name comp1
            → isHighestℕ {k} {w1} {w2} {b} {v} i name comp
            → isHighestℕ {n} {w'} {w2} {a'} {v} i name comp2)
           × (∈names𝕎 {m} {w'} {w1} {a'} {b} name comp1
              → ∈names𝕎 {k} {w1} {w2} {b} {v} name comp
              → ∈names𝕎 {n} {w'} {w2} {a'} {v} name comp2)))
    q = val-steps→names {w'} {w1} {w2} {a'} {b} {v} {n} {m} i name isv comp1 comp2
... | inj₂ z rewrite z
           | pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
           | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) =
    0 , _≤_.z≤n , refl , (λ x y → x) , (λ x y → x)



steps-sat-isHighestℕ2-aux : (cc : ContConds) (gc : get-choose-ℕ) {name : Name} {f : Term}
                             → ¬ name ∈ names f
                             → # f
                             → (k : ℕ)
                             → (ind : (k' : ℕ) → k' < k → presHighestℕ2 name f k')
                             → presHighestℕ2 name f k
steps-sat-isHighestℕ2-aux cc gc {name} {f} nnf cf 0 ind {w1} {w2} {a} {b} {n} comp isv upd compat wgt0 nnw idom
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = (λ g → g) , (nnw , idom)
steps-sat-isHighestℕ2-aux cc gc {name} {f} nnf cf (suc k) ind {w1} {w2} {a} {b} {n} comp isv ctxt compat wgt0 nnw idom with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z =
  cgn , (nnw , idom , snd (snd (snd (snd comp2))) inw (snd comp3))
  where
    ind0 : (k' : ℕ) → k' < suc k → presHighestℕ2 name f k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presHighestℕ2 name f k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

    q : ΣhighestUpdCtxt2 name f n a' w1 w1'
    q = step-sat-isHighestℕ2 cc gc {w1} {w1'} {a} {a'} {n} {name} {f} compat wgt0 z (k , b , w2 , comp , isv , ind1) ctxt nnf nnw idom cf

    k' : ℕ
    k' = fst q

    a'' : Term
    a'' = fst (snd q)

    w1'' : 𝕎·
    w1'' = fst (snd (snd q))

    comp1 : steps k' (a' , w1') ≡ (a'' , w1'')
    comp1 = fst (snd (snd (snd q)))

    e1 : w1 ⊑· w1'
    e1 = step⊑ {w1} {w1'} {a} {a'} z

    e2 : w1' ⊑· w1''
    e2 = steps→⊑ k' a' a'' {w1'} {w1''} comp1

    e3 : w1 ⊑· w1''
    e3 = ⊑-trans· e1 e2

    ii : getT≤ℕ w1'' n name → (getT≤ℕ w1 n name × isHighestℕ {k'} {w1'} {w1''} {a'} {a''} n name comp1)
    ii = fst (snd (snd (snd (snd q))))

    inw : ∈names𝕎 {k'} {w1'} {w1''} {a'} {a''} name comp1
    inw = fst (snd (snd (snd (snd (snd q)))))

    uc : updCtxt2 name f a''
    uc = snd (snd (snd (snd (snd (snd q)))))

    comp2 : Σ ℕ (λ k0 → k0 ≤ k × Σ (steps k0 (a'' , w1'') ≡ (b , w2)) (λ cmp →
                  (isHighestℕ {k'} {w1'} {w1''} {a'} {a''} n name comp1
                   → isHighestℕ {k0} {w1''} {w2} {a''} {b} n name cmp
                   → isHighestℕ {k} {w1'} {w2} {a'} {b} n name comp)
                  × (∈names𝕎 {k'} {w1'} {w1''} {a'} {a''} name comp1
                     → ∈names𝕎 {k0} {w1''} {w2} {a''} {b} name cmp
                     → ∈names𝕎 {k} {w1'} {w2} {a'} {b} name comp)))
    comp2 = val-steps→names {w1'} {w1''} {w2} {a'} {a''} {b} {k} {k'} n name isv comp1 comp

    comp3 : (getT≤ℕ w2 n name → isHighestℕ {fst comp2} {w1''} {w2} {a''} {b} n name (fst (snd (snd comp2))))
            × ∈names𝕎 {fst comp2} {w1''} {w2} {a''} {b} name (fst (snd (snd comp2)))
    comp3 = ind1 (fst comp2) (fst (snd comp2)) {w1''} {w2} {a''} {b} {n}
                 (fst (snd (snd comp2))) isv uc
                 (⊑-compatible· e3 compat) (∀𝕎-mon e3 wgt0)
                 (∈names𝕎→¬∈name𝕎ᵣ {k'} {w1'} {w1''} {a'} {a''} name comp1 inw)
                 (∈names𝕎→∈dom𝕎ᵣ {k'} {w1'} {w1''} {a'} {a''} name comp1 inw)

    cgn : getT≤ℕ w2 n name → getT≤ℕ w1 n name × isHighestℕ {k} {w1'} {w2} {a'} {b} n name comp
    cgn g = fst (ii gw') , fst (snd (snd (snd comp2))) (snd (ii gw')) (fst comp3 g)
      where
        gw' : getT≤ℕ w1'' n name
        gw' = isHighestℕ→getT≤ℕ {proj₁ comp2} {w1''} {w2} {a''} {b} n name (fst (snd (snd comp2))) (fst comp3 g)
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = (λ g → g) , (nnw , idom)



abstract
  -- We also need something about the way f computes as for the proof about 'differ'
  steps-sat-isHighestℕ2 : (cc : ContConds) (gc : get-choose-ℕ) {name : Name} {f : Term} {k : ℕ}
                        → ¬ name ∈ names f
                        → # f
                        → presHighestℕ2 name f k
  steps-sat-isHighestℕ2 cc gc {name} {f} {k} nnf cf = <ℕind _ (steps-sat-isHighestℕ2-aux cc gc {name} {f} nnf cf) k

\end{code}
