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


module continuity2b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)



data updCtxt2 (name : Name) (f : Term) : Term → Set where
  updCtxt2-VAR     : (x : Var) → updCtxt2 name f (VAR x)
  updCtxt2-NAT     : updCtxt2 name f NAT
  updCtxt2-QNAT    : updCtxt2 name f QNAT
  updCtxt2-LT      : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (LT a b)
  updCtxt2-QLT     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (QLT a b)
  updCtxt2-NUM     : (x : ℕ) → updCtxt2 name f (NUM x)
  updCtxt2-IFLT    : (a b c d : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f d → updCtxt2 name f (IFLT a b c d)
  updCtxt2-SUC     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SUC a)
  updCtxt2-PI      : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (PI a b)
  updCtxt2-LAMBDA  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (LAMBDA a)
  updCtxt2-APPLY   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (APPLY a b)
  updCtxt2-FIX     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (FIX a)
  updCtxt2-LET     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (LET a b)
  updCtxt2-SUM     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SUM a b)
  updCtxt2-PAIR    : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (PAIR a b)
  updCtxt2-SPREAD  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SPREAD a b)
  updCtxt2-SET     : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (SET a b)
  updCtxt2-ISECT   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (ISECT a b)
  updCtxt2-TUNION  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (TUNION a b)
  updCtxt2-UNION   : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (UNION a b)
  updCtxt2-QTUNION : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (QTUNION a b)
  updCtxt2-INL     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (INL a)
  updCtxt2-INR     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (INR a)
  updCtxt2-DECIDE  : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (DECIDE a b c)
  updCtxt2-EQ      : (a b c : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f c → updCtxt2 name f (EQ a b c)
  updCtxt2-AX      : updCtxt2 name f AX
  updCtxt2-FREE    : updCtxt2 name f FREE
  updCtxt2-CS      : (name' : Name) → updCtxt2 name f (CS name')
  updCtxt2-NAME    : (name' : Name) → ¬ name' ≡ name → updCtxt2 name f (NAME name')
  updCtxt2-FRESH   : (a : Term) → updCtxt2 name f a → updCtxt2 name f (FRESH a)
  updCtxt2-CHOOSE  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (CHOOSE a b)
--  updCtxt2-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updCtxt2 name1 name2 f a₁ a₂ → updCtxt2 name1 name2 f b₁ b₂ → updCtxt2 name1 name2 f c₁ c₂ → updCtxt2 name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  updCtxt2-TSQUASH : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TSQUASH a)
  updCtxt2-TTRUNC  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TTRUNC a)
  updCtxt2-TCONST  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (TCONST a)
  updCtxt2-SUBSING : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SUBSING a)
  updCtxt2-PURE    : updCtxt2 name f PURE
  updCtxt2-DUM     : (a : Term) → updCtxt2 name f a → updCtxt2 name f (DUM a)
  updCtxt2-FFDEFS  : (a b : Term) → updCtxt2 name f a → updCtxt2 name f b → updCtxt2 name f (FFDEFS a b)
  updCtxt2-UNIV    : (x : ℕ) → updCtxt2 name f (UNIV x)
  updCtxt2-LIFT    : (a : Term) → updCtxt2 name f a → updCtxt2 name f (LIFT a)
  updCtxt2-LOWER   : (a : Term) → updCtxt2 name f a → updCtxt2 name f (LOWER a)
  updCtxt2-SHRINK  : (a : Term) → updCtxt2 name f a → updCtxt2 name f (SHRINK a)
  updCtxt2-upd     : updCtxt2 name f (upd name f)


presHighestℕ2 : (name : Name) (f : Term) (k : ℕ) → Set(lsuc L)
presHighestℕ2 name f k =
  {w1 w2 : 𝕎·} {a b : Term} {n : ℕ}
  (comp : steps k (a , w1) ≡ (b , w2))
  → isValue b
  → updCtxt2 name f a
  → compatible· name w1 Res⊤
  → ∀𝕎-get0-NUM w1 name
  → getT≤ℕ w2 n name --getT 0 name w2 ≡ just (NUM n)
  → isHighestℕ {k} {w1} {w2} {a} {b} n name comp


stepsPresHighestℕ2 : (name : Name) (f : Term) (b : Term) (w : 𝕎·) → Set(lsuc L)
stepsPresHighestℕ2 name f b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    steps k (b , w) ≡ (v , w')
    × isValue v
    × ((k' : ℕ) → k' ≤ k → presHighestℕ2 name f k'))))


ΣhighestUpdCtxtAux2 : (k' : ℕ) (name : Name) (f : Term) (n : ℕ) (a a' : Term) (w0 w w' : 𝕎·) → Set(L)
ΣhighestUpdCtxtAux2 k' name f n a a' w0 w w' =
  Σ (steps k' (a , w) ≡ (a' , w')) (λ comp →
    (getT≤ℕ w' n name → (getT≤ℕ w0 n name × isHighestℕ {k'} {w} {w'} {a} {a'} n name comp))
    × updCtxt2 name f a')


ΣhighestUpdCtxt2 : (name : Name) (f : Term) (n : ℕ) (a : Term) (w0 w : 𝕎·) → Set(L)
ΣhighestUpdCtxt2 name f n a w0 w =
  Σ ℕ (λ k' → Σ Term (λ a' → Σ 𝕎· (λ w' →
    ΣhighestUpdCtxtAux2 k' name f n a a' w0 w w')))



-- This is similar to step-sat-isHighestℕ in continuity3.lagda.
-- updCtxt2's properties can essentially be copied from terms3b.lagda as this is almost the same definition.
-- We only need to prove that name's value increases, but for this only upd must update name.
-- So we
--   (1) require that ¬ name ∈ names f and
--   (2) that updCtxt2 name f (NAME name') only when ¬ name ≡ name'
step-sat-isHighestℕ2 : (gc : get-choose-ℕ) {w1 w2 : 𝕎·} {a b : Term} {n : ℕ} {name : Name} {f : Term}
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
step-sat-isHighestℕ2 gc {w1} {w2} {.NAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-NAT nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAT , w1 , refl , (λ x → x , x) , updCtxt2-NAT
step-sat-isHighestℕ2 gc {w1} {w2} {.QNAT} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-QNAT nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QNAT , w1 , refl , (λ x → x , x) , updCtxt2-QNAT
step-sat-isHighestℕ2 gc {w1} {w2} {.(LT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LT a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-LT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(QLT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-QLT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QLT a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-QLT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(NUM x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-NUM x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NUM _ , w1 , refl , (λ x → x , x) , updCtxt2-NUM _
step-sat-isHighestℕ2 gc {w1} {w2} {.(IFLT a b₁ c d)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-IFLT a b₁ c d ctxt ctxt₁ ctxt₂ ctxt₃) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(SUC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUC a ctxt) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(PI a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-PI a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PI a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-PI _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(LAMBDA a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LAMBDA a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LAMBDA a , w1 , refl , (λ x → x , x) , updCtxt2-LAMBDA _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf with is-LAM g
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  {!!} --ret (sub a t) w
... | inj₂ x with is-CS g
... |    inj₁ (name' , p) rewrite p with is-NUM a
... |       inj₁ (m , q) rewrite q = {!!} --Data.Maybe.map (λ t → t , w) (getT n name w)
... |       inj₂ y with step⊎ a w1
... |          inj₁ (a' , w1' , z) rewrite z = {!!} --ret (APPLY (CS name) u) w'
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 gc {w1} {w2} {.(APPLY g a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-APPLY g a ctxt ctxt₁) nnf nnw idom cf | inj₂ x | inj₂ y with step⊎ g w1
... | inj₁ (g' , w1' , z) rewrite z = {!!} --ret (APPLY g a) w'
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-sat-isHighestℕ2 gc {w1} {w2} {.(FIX a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FIX a ctxt) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(LET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LET a b₁ ctxt ctxt₁) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(SUM a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUM a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUM a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-SUM _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(PAIR a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-PAIR a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PAIR a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-PAIR _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(SPREAD a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SPREAD a b₁ ctxt ctxt₁) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(SET a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SET a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SET a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-SET _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(ISECT a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-ISECT a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , ISECT a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-ISECT _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(TUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TUNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-TUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(UNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-UNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-UNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(QTUNION a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-QTUNION a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , QTUNION a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-QTUNION _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(INL a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INL a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INL a , w1 , refl , (λ x → x , x) , updCtxt2-INL _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(INR a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-INR a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , INR a , w1 , refl , (λ x → x , x) , updCtxt2-INR _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(DECIDE a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-DECIDE a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(EQ a b₁ c)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-EQ a b₁ c ctxt ctxt₁ ctxt₂) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.AX} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-AX nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , AX , w1 , refl , (λ x → x , x) , updCtxt2-AX
step-sat-isHighestℕ2 gc {w1} {w2} {.FREE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-FREE nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FREE , w1 , refl , (λ x → x , x) , updCtxt2-FREE
step-sat-isHighestℕ2 gc {w1} {w2} {.(CS name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CS name') nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , CS name' , w1 , refl , (λ x → x , x) , updCtxt2-CS _
step-sat-isHighestℕ2 gc {w1} {w2} {.(NAME name')} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-NAME name' x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , NAME name' , w1 , refl , (λ x → x , x) , updCtxt2-NAME _ x
step-sat-isHighestℕ2 gc {w1} {w2} {.(FRESH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FRESH a ctxt) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(CHOOSE a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-CHOOSE a b₁ ctxt ctxt₁) nnf nnw idom cf = {!!}
step-sat-isHighestℕ2 gc {w1} {w2} {.(TSQUASH a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TSQUASH a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TSQUASH a , w1 , refl , (λ x → x , x) , updCtxt2-TSQUASH _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(TTRUNC a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TTRUNC a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TTRUNC a , w1 , refl , (λ x → x , x) , updCtxt2-TTRUNC _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(TCONST a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-TCONST a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , TCONST a , w1 , refl , (λ x → x , x) , updCtxt2-TCONST _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(SUBSING a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SUBSING a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SUBSING a , w1 , refl , (λ x → x , x) , updCtxt2-SUBSING _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.PURE} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-PURE nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , PURE , w1 , refl , (λ x → x , x) , updCtxt2-PURE
step-sat-isHighestℕ2 gc {w1} {w2} {.(DUM a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-DUM a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , DUM a , w1 , refl , (λ x → x , x) , updCtxt2-DUM _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(FFDEFS a b₁)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-FFDEFS a b₁ ctxt ctxt₁) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , FFDEFS a b₁ , w1 , refl , (λ x → x , x) , updCtxt2-FFDEFS _ _ ctxt ctxt₁
step-sat-isHighestℕ2 gc {w1} {w2} {.(UNIV x)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-UNIV x) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , UNIV _ , w1 , refl , (λ x → x , x) , updCtxt2-UNIV _
step-sat-isHighestℕ2 gc {w1} {w2} {.(LIFT a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LIFT a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LIFT a , w1 , refl , (λ x → x , x) , updCtxt2-LIFT _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(LOWER a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-LOWER a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , LOWER a , w1 , refl , (λ x → x , x) , updCtxt2-LOWER _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(SHRINK a)} {b} {n} {name} {f} compat wgt0 comp indb (updCtxt2-SHRINK a ctxt) nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , SHRINK a , w1 , refl , (λ x → x , x) , updCtxt2-SHRINK _ ctxt
step-sat-isHighestℕ2 gc {w1} {w2} {.(upd name f)} {b} {n} {name} {f} compat wgt0 comp indb updCtxt2-upd nnf nnw idom cf rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) = 0 , upd name f , w1 , refl , (λ x → x , x) , updCtxt2-upd

\end{code}
