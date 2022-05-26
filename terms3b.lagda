\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; _<?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Data.Bool.Properties using ()
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

open import util
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import choiceExt
open import newChoice


module terms3b {L : Level} (W : PossibleWorlds {L})
               (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
               (N : NewChoice W C M G)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)
open import terms2(W)(C)(M)(G)(E)(N)
open import terms3(W)(C)(M)(G)(E)(N)



-- This is similar to differ in terms3.lagda, but in addition relates terms with names too.
-- This one is reflexive, while differ is not (or only for name-free terms)
data differ2 (name1 name2 : Name) (f : Term) : Term → Term → Set where
  differ2-VAR     : (x : Var) → differ2 name1 name2 f (VAR x) (VAR x)
  differ2-NAT     : differ2 name1 name2 f NAT NAT
  differ2-QNAT    : differ2 name1 name2 f QNAT QNAT
  differ2-LT      : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (LT a₁ b₁) (LT a₂ b₂)
  differ2-QLT     : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (QLT a₁ b₁) (QLT a₂ b₂)
  differ2-NUM     : (x : ℕ) → differ2 name1 name2 f (NUM x) (NUM x)
  differ2-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f c₁ c₂ → differ2 name1 name2 f d₁ d₂ → differ2 name1 name2 f (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  differ2-SUC     : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (SUC a) (SUC b)
  differ2-PI      : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (PI a₁ b₁) (PI a₂ b₂)
  differ2-LAMBDA  : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (LAMBDA a) (LAMBDA b)
  differ2-APPLY   : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (APPLY a₁ b₁) (APPLY a₂ b₂)
  differ2-FIX     : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (FIX a) (FIX b)
  differ2-LET     : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (LET a₁ b₁) (LET a₂ b₂)
  differ2-SUM     : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (SUM a₁ b₁) (SUM a₂ b₂)
  differ2-PAIR    : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (PAIR a₁ b₁) (PAIR a₂ b₂)
  differ2-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  differ2-SET     : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (SET a₁ b₁) (SET a₂ b₂)
  differ2-ISECT   : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (ISECT a₁ b₁) (ISECT a₂ b₂)
  differ2-TUNION  : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (TUNION a₁ b₁) (TUNION a₂ b₂)
  differ2-UNION   : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (UNION a₁ b₁) (UNION a₂ b₂)
  differ2-QTUNION : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  differ2-INL     : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (INL a) (INL b)
  differ2-INR     : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (INR a) (INR b)
  differ2-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f c₁ c₂ → differ2 name1 name2 f (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  differ2-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f c₁ c₂ → differ2 name1 name2 f (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  differ2-AX      : differ2 name1 name2 f AX AX
  differ2-FREE    : differ2 name1 name2 f FREE FREE
  differ2-CS      : (name : Name) → differ2 name1 name2 f (CS name) (CS name)
  differ2-NAME    : (name : Name) → differ2 name1 name2 f (NAME name) (NAME name)
  differ2-FRESH   : (a b : Term) → differ2 (suc name1) (suc name2) (shiftNameUp 0 f) a b → differ2 name1 name2 f (FRESH a) (FRESH b)
  differ2-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  differ2-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f c₁ c₂ → differ2 name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  differ2-TSQUASH : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (TSQUASH a) (TSQUASH b)
  differ2-TTRUNC  : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (TTRUNC a) (TTRUNC b)
  differ2-TCONST  : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (TCONST a) (TCONST b)
  differ2-SUBSING : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (SUBSING a) (SUBSING b)
  differ2-PURE    : differ2 name1 name2 f PURE PURE
  differ2-DUM     : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (DUM a) (DUM b)
  differ2-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → differ2 name1 name2 f a₁ a₂ → differ2 name1 name2 f b₁ b₂ → differ2 name1 name2 f (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  differ2-UNIV    : (x : ℕ) → differ2 name1 name2 f (UNIV x) (UNIV x)
  differ2-LIFT    : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (LIFT a) (LIFT b)
  differ2-LOWER   : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (LOWER a) (LOWER b)
  differ2-SHRINK  : (a b : Term) → differ2 name1 name2 f a b → differ2 name1 name2 f (SHRINK a) (SHRINK b)
  differ2-upd     : differ2 name1 name2 f (upd name1 f) (upd name2 f)



differ2-NUM→ : {name1 name2 : Name} {f t : Term} {m : ℕ}
               → differ2 name1 name2 f (NUM m) t
               → t ≡ NUM m
differ2-NUM→ {name1} {name2} {f} {.(NUM m)} {m} (differ2-NUM .m) = refl



{--
differ2-CSₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ2 name1 name2 f (CS name) t
differ2-CSₗ→ {name1} {name2} {name} {f} {t} ()


differ2-NAMEₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ2 name1 name2 f (NAME name) t
differ2-NAMEₗ→ {name1} {name2} {name} {f} {t} ()
--}



differ2-LAMBDAₗ→ : {name1 name2 : Name} {f g t : Term}
                  → differ2 name1 name2 f (LAMBDA g) t
                  → Σ Term (λ g' → t ≡ LAMBDA g' × differ2 name1 name2 f g g')
                    ⊎ (g ≡ updBody name1 f × t ≡ upd name2 f)
differ2-LAMBDAₗ→ {name1} {name2} {f} {g} {.(LAMBDA b)} (differ2-LAMBDA .g b d) = inj₁ (b , refl , d)
differ2-LAMBDAₗ→ {name1} {name2} {f} {.(updBody name1 f)} {.(upd name2 f)} differ2-upd = inj₂ (refl , refl)


differ2-PAIRₗ→ : {name1 name2 : Name} {f a b t : Term}
                  → differ2 name1 name2 f (PAIR a b) t
                  → Σ Term (λ a' → Σ Term (λ b' → t ≡ PAIR a' b' × differ2 name1 name2 f a a' × differ2 name1 name2 f b b'))
differ2-PAIRₗ→ {name1} {name2} {f} {a} {b} {.(PAIR a₂ b₂)} (differ2-PAIR .a a₂ .b b₂ diff diff₁) = a₂ , b₂ , refl , diff , diff₁


differ2-INLₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ2 name1 name2 f (INL a) t
                → Σ Term (λ a' → t ≡ INL a' × differ2 name1 name2 f a a')
differ2-INLₗ→ {name1} {name2} {f} {a} {.(INL a₂)} (differ2-INL .a a₂ diff) = a₂ , refl , diff


differ2-INRₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ2 name1 name2 f (INR a) t
                → Σ Term (λ a' → t ≡ INR a' × differ2 name1 name2 f a a')
differ2-INRₗ→ {name1} {name2} {f} {a} {.(INR a₂)} (differ2-INR .a a₂ diff) = a₂ , refl , diff



→differ2-shiftUp : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                   → differ2 name1 name2 f a b
                   → differ2 name1 name2 f (shiftUp v a) (shiftUp v b)
→differ2-shiftUp v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ2-VAR x) = differ2-VAR _
→differ2-shiftUp v {name1} {name2} {f} cf {.NAT} {.NAT} differ2-NAT = differ2-NAT
→differ2-shiftUp v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ2-QNAT = differ2-QNAT
→differ2-shiftUp v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ2-LT a₁ a₂ b₁ b₂ diff diff₁) = differ2-LT _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ2-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ2-QLT _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ2-NUM x) = differ2-NUM x
→differ2-shiftUp v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ2-IFLT _ _ _ _ _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁) (→differ2-shiftUp v cf diff₂) (→differ2-shiftUp v cf diff₃)
→differ2-shiftUp v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ2-SUC a b diff) = differ2-SUC _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ2-PI a₁ a₂ b₁ b₂ diff diff₁) = differ2-PI _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp (suc v) cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ2-LAMBDA a b diff) = differ2-LAMBDA _ _ (→differ2-shiftUp (suc v) cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ2-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ2-APPLY _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ2-FIX a b diff) = differ2-FIX _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ2-LET a₁ a₂ b₁ b₂ diff diff₁) = differ2-LET _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp (suc v) cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ2-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ2-SUM _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp (suc v) cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ2-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ2-PAIR _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ2-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ2-SPREAD _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp (suc (suc v)) cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ2-SET a₁ a₂ b₁ b₂ diff diff₁) = differ2-SET _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp (suc v) cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ2-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differ2-ISECT _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ2-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-TUNION _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp (suc v) cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ2-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-UNION _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ2-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-QTUNION _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ2-INL a b diff) = differ2-INL _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ2-INR a b diff) = differ2-INR _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-DECIDE _ _ _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp (suc v) cf diff₁) (→differ2-shiftUp (suc v) cf diff₂)
→differ2-shiftUp v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ2-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-EQ _ _ _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁) (→differ2-shiftUp v cf diff₂)
→differ2-shiftUp v {name1} {name2} {f} cf {.AX} {.AX} differ2-AX = differ2-AX
→differ2-shiftUp v {name1} {name2} {f} cf {.FREE} {.FREE} differ2-FREE = differ2-FREE
→differ2-shiftUp v {name1} {name2} {f} cf {.(CS name)} {.(CS name)} (differ2-CS name) = differ2-CS name
→differ2-shiftUp v {name1} {name2} {f} cf {.(NAME name)} {.(NAME name)} (differ2-NAME name) = differ2-NAME name
→differ2-shiftUp v {name1} {name2} {f} cf {.(FRESH a)} {.(FRESH b)} (differ2-FRESH a b diff) = differ2-FRESH _ _ (→differ2-shiftUp v (→#shiftNameUp 0 {f} cf) diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ2-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ2-CHOOSE _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
--→differ2-shiftUp v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ2-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-IFC0 _ _ _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁) (→differ2-shiftUp v cf diff₂)
→differ2-shiftUp v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ2-TSQUASH a b diff) = differ2-TSQUASH _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ2-TTRUNC a b diff) = differ2-TTRUNC _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(TCONST a)} {.(TCONST b)} (differ2-TCONST a b diff) = differ2-TCONST _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ2-SUBSING a b diff) = differ2-SUBSING _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(PURE)} {.(PURE)} (differ2-PURE) = differ2-PURE
→differ2-shiftUp v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ2-DUM a b diff) = differ2-DUM _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ2-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ2-FFDEFS _ _ _ _ (→differ2-shiftUp v cf diff) (→differ2-shiftUp v cf diff₁)
→differ2-shiftUp v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ2-UNIV x) = differ2-UNIV x
→differ2-shiftUp v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ2-LIFT a b diff) = differ2-LIFT _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ2-LOWER a b diff) = differ2-LOWER _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ2-SHRINK a b diff) = differ2-SHRINK _ _ (→differ2-shiftUp v cf diff)
→differ2-shiftUp v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ2-upd rewrite sucIf≤s0 v | #shiftUp (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = differ2-upd



{--
sucIf≤-sucIf≤ : {x i j : Name}
                → i ≤ x
                → sucIf≤ i (sucIf≤ j x) ≡ sucIf≤ (suc j) (sucIf≤ i x)
sucIf≤-sucIf≤ {x} {i} {j} lex with x <? j
... | yes p with x <? i
... |    yes q = ⊥-elim (n≮n (suc x) (_≤_.s≤s (≤-trans q lex)))
... |    no q with suc x <? suc j
... |       yes r = refl
... |       no r = ⊥-elim (r (_≤_.s≤s p))
sucIf≤-sucIf≤ {x} {i} {j} lex | no p with x <? i
... |    yes q = ⊥-elim (n≮n (suc x) (_≤_.s≤s (≤-trans q lex)))
... |    no q with suc x <? i
... |       yes r = ⊥-elim (q (≤-trans (<⇒≤ (n<1+n (suc x))) r))
... |       no r with suc x <? suc j
... |          yes s = ⊥-elim (p (s≤s-inj s))
... |          no s = refl
--}


{--
shiftNameUp-shiftNameUp : {i j : ℕ} {t : Term}
                          → ((n : Name) → n ∈ names t → i ≤ n)
                          → shiftNameUp i (shiftNameUp j t)
                             ≡ shiftNameUp (suc j) (shiftNameUp i t)
shiftNameUp-shiftNameUp {i} {j} {VAR x} imp = refl
shiftNameUp-shiftNameUp {i} {j} {NAT} imp = refl
shiftNameUp-shiftNameUp {i} {j} {QNAT} imp = refl
shiftNameUp-shiftNameUp {i} {j} {LT t t₁} imp = ≡LT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {QLT t t₁} imp = ≡QLT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {NUM x} imp = refl
shiftNameUp-shiftNameUp {i} {j} {IFLT t t₁ t₂ t₃} imp = ≡IFLT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ˡ k)))) (shiftNameUp-shiftNameUp {i} {j} {t₂} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ˡ k))))) (shiftNameUp-shiftNameUp {i} {j} {t₃} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) (∈-++⁺ʳ (names t₂) k)))))
shiftNameUp-shiftNameUp {i} {j} {SUC t} imp = ≡SUC (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {PI t t₁} imp = ≡PI (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {LAMBDA t} imp = ≡LAMBDA (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {APPLY t t₁} imp = ≡APPLY (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {FIX t} imp = ≡FIX (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {LET t t₁} imp = ≡LET (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {SUM t t₁} imp = ≡SUM (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {PAIR t t₁} imp = ≡PAIR (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {SPREAD t t₁} imp = ≡SPREAD (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {SET t t₁} imp = ≡SET (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {ISECT t t₁} imp = ≡ISECT (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {TUNION t t₁} imp = ≡TUNION (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {UNION t t₁} imp = ≡UNION (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {QTUNION t t₁} imp = ≡QTUNION (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {INL t} imp = ≡INL (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {INR t} imp = ≡INR (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {DECIDE t t₁ t₂} imp = ≡DECIDE (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ˡ k)))) (shiftNameUp-shiftNameUp {i} {j} {t₂} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) k))))
shiftNameUp-shiftNameUp {i} {j} {EQ t t₁ t₂} imp = ≡EQ (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ˡ k)))) (shiftNameUp-shiftNameUp {i} {j} {t₂} (λ n k → imp n (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names t₁) k))))
shiftNameUp-shiftNameUp {i} {j} {AX} imp = refl
shiftNameUp-shiftNameUp {i} {j} {FREE} imp = refl
shiftNameUp-shiftNameUp {i} {j} {CS x} imp = ≡CS (sucIf≤-sucIf≤ {x} {i} {j} (imp x (here refl)))
shiftNameUp-shiftNameUp {i} {j} {NAME x} imp = ≡NAME (sucIf≤-sucIf≤ {x} {i} {j} (imp x (here refl)))
shiftNameUp-shiftNameUp {i} {j} {FRESH t} imp = ≡FRESH (shiftNameUp-shiftNameUp {suc i} {suc j} {t} c)
  where
    c : (n : Name) → n ∈ names t → suc i ≤ n
    c 0 z = {!!}
    c (suc n) z = _≤_.s≤s (imp n (suc→∈lowerNames {n} {names t} z))
shiftNameUp-shiftNameUp {i} {j} {CHOOSE t t₁} imp = ≡CHOOSE (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {TSQUASH t} imp = ≡TSQUASH (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {TTRUNC t} imp = ≡TTRUNC (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {TCONST t} imp = ≡TCONST (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {SUBSING t} imp = ≡SUBSING (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {NN t} imp = ≡NN (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {DUM t} imp = ≡DUM (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {FFDEFS t t₁} imp = ≡FFDEFS (shiftNameUp-shiftNameUp {i} {j} {t} (λ n k → imp n (∈-++⁺ˡ k))) (shiftNameUp-shiftNameUp {i} {j} {t₁} (λ n k → imp n (∈-++⁺ʳ (names t) k)))
shiftNameUp-shiftNameUp {i} {j} {UNIV x} imp = refl
shiftNameUp-shiftNameUp {i} {j} {LIFT t} imp = ≡LIFT (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {LOWER t} imp = ≡LOWER (shiftNameUp-shiftNameUp {i} {j} {t} imp)
shiftNameUp-shiftNameUp {i} {j} {SHRINK t} imp = ≡SHRINK (shiftNameUp-shiftNameUp {i} {j} {t} imp)
--}



→differ2-shiftNameUp : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                   → differ2 name1 name2 f a b
                   → differ2 (sucIf≤ v name1) (sucIf≤ v name2) (shiftNameUp v f) (shiftNameUp v a) (shiftNameUp v b)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ2-VAR x) = differ2-VAR _
→differ2-shiftNameUp v {name1} {name2} {f} cf {.NAT} {.NAT} differ2-NAT = differ2-NAT
→differ2-shiftNameUp v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ2-QNAT = differ2-QNAT
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ2-LT a₁ a₂ b₁ b₂ diff diff₁) = differ2-LT _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ2-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ2-QLT _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ2-NUM x) = differ2-NUM x
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ2-IFLT _ _ _ _ _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁) (→differ2-shiftNameUp v cf diff₂) (→differ2-shiftNameUp v cf diff₃)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ2-SUC a b diff) = differ2-SUC _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ2-PI a₁ a₂ b₁ b₂ diff diff₁) = differ2-PI _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ2-LAMBDA a b diff) = differ2-LAMBDA _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ2-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ2-APPLY _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ2-FIX a b diff) = differ2-FIX _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ2-LET a₁ a₂ b₁ b₂ diff diff₁) = differ2-LET _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ2-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ2-SUM _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ2-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ2-PAIR _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ2-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ2-SPREAD _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ2-SET a₁ a₂ b₁ b₂ diff diff₁) = differ2-SET _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ2-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differ2-ISECT _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ2-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-TUNION _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ2-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-UNION _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ2-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-QTUNION _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ2-INL a b diff) = differ2-INL _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ2-INR a b diff) = differ2-INR _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-DECIDE _ _ _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁) (→differ2-shiftNameUp v cf diff₂)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ2-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-EQ _ _ _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁) (→differ2-shiftNameUp v cf diff₂)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.AX} {.AX} differ2-AX = differ2-AX
→differ2-shiftNameUp v {name1} {name2} {f} cf {.FREE} {.FREE} differ2-FREE = differ2-FREE
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(CS name)} {.(CS name)} (differ2-CS name) = differ2-CS _
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(NAME name)} {.(NAME name)} (differ2-NAME name) = differ2-NAME _
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(FRESH a)} {.(FRESH b)} (differ2-FRESH a b diff) = differ2-FRESH (shiftNameUp (suc v) a) (shiftNameUp (suc v) b) c1
  where
    c3 : differ2 (sucIf≤ (suc v) (suc name1))
                (sucIf≤ (suc v) (suc name2))
                (shiftNameUp (suc v) (shiftNameUp 0 f))
                (shiftNameUp (suc v) a)
                (shiftNameUp (suc v) b)
    c3 = →differ2-shiftNameUp (suc v) {suc name1} {suc name2} (→#shiftNameUp 0 {f} cf) diff

    c2 : differ2 (suc (sucIf≤ v name1))
                (suc (sucIf≤ v name2))
                (shiftNameUp (suc v) (shiftNameUp 0 f))
                (shiftNameUp (suc v) a)
                (shiftNameUp (suc v) b)
    c2 rewrite suc-sucIf≤ v name1 | suc-sucIf≤ v name2 = c3

    c1 : differ2 (suc (sucIf≤ v name1))
                (suc (sucIf≤ v name2))
                (shiftNameUp 0 (shiftNameUp v f))
                (shiftNameUp (suc v) a)
                (shiftNameUp (suc v) b)
    c1 rewrite shiftNameUp-shiftNameUp {0} {v} {f} _≤_.z≤n = c2
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ2-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ2-CHOOSE _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
--→differ2-shiftNameUp v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ2-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-IFC0 _ _ _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁) (→differ2-shiftNameUp v cf diff₂)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ2-TSQUASH a b diff) = differ2-TSQUASH _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ2-TTRUNC a b diff) = differ2-TTRUNC _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(TCONST a)} {.(TCONST b)} (differ2-TCONST a b diff) = differ2-TCONST _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ2-SUBSING a b diff) = differ2-SUBSING _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(PURE)} {.(PURE)} (differ2-PURE) = differ2-PURE
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ2-DUM a b diff) = differ2-DUM _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ2-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ2-FFDEFS _ _ _ _ (→differ2-shiftNameUp v cf diff) (→differ2-shiftNameUp v cf diff₁)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ2-UNIV x) = differ2-UNIV x
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ2-LIFT a b diff) = differ2-LIFT _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ2-LOWER a b diff) = differ2-LOWER _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ2-SHRINK a b diff) = differ2-SHRINK _ _ (→differ2-shiftNameUp v cf diff)
→differ2-shiftNameUp v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ2-upd = c2
  where
    c1 : differ2 (sucIf≤ v name1) (sucIf≤ v name2) (shiftNameUp v f) (upd (sucIf≤ v name1) (shiftNameUp v f)) (upd (sucIf≤ v name2) (shiftNameUp v f))
    c1 = differ2-upd

    c2 : differ2 (sucIf≤ v name1) (sucIf≤ v name2) (shiftNameUp v f)
                (LAMBDA (LET (VAR 0)
                             (LET (IFLT (APPLY (CS (sucIf≤ v name1)) (NUM 0)) (VAR 0)
                                        (CHOOSE (NAME (sucIf≤ v name1)) (VAR 0)) AX)
                                  (APPLY (shiftNameUp v (shiftUp 0 f)) (VAR (sucIf≤ 0 0))))))
                (LAMBDA (LET (VAR 0)
                             (LET (IFLT (APPLY (CS (sucIf≤ v name2)) (NUM 0)) (VAR 0)
                                        (CHOOSE (NAME (sucIf≤ v name2)) (VAR 0)) AX)
                                  (APPLY (shiftNameUp v (shiftUp 0 f)) (VAR (sucIf≤ 0 0))))))
    c2 rewrite sym (shiftUp-shiftNameUp 0 v f)  = c1




→differ2-shiftNameUp0 : {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                   → differ2 name1 name2 f a b
                   → differ2 (suc name1) (suc name2) (shiftNameUp 0 f) (shiftNameUp 0 a) (shiftNameUp 0 b)
→differ2-shiftNameUp0 {name1} {name2} {f} cf {a} {b} dif
  rewrite suc≡sucIf≤0 name1 | suc≡sucIf≤0 name2 =
  →differ2-shiftNameUp 0 {name1} {name2} cf dif



differ2-subv : {name1 name2 : Name} {f : Term} (cf : # f) (v : Var) {a₁ a₂ b₁ b₂ : Term}
             → differ2 name1 name2 f a₁ a₂
             → differ2 name1 name2 f b₁ b₂
             → differ2 name1 name2 f (subv v b₁ a₁) (subv v b₂ a₂)
differ2-subv {name1} {name2} {f} cf v {.(VAR x)} {.(VAR x)} {b₁} {b₂} (differ2-VAR x) d₂ with x ≟ v
... | yes p = d₂ -- rewrite shiftDownUp b₁ 0 | shiftDownUp b₂ 0 = d₂
... | no p = differ2-VAR _
differ2-subv {name1} {name2} {f} cf v {.NAT} {.NAT} {b₁} {b₂} differ2-NAT d₂ = differ2-NAT
differ2-subv {name1} {name2} {f} cf v {.QNAT} {.QNAT} {b₁} {b₂} differ2-QNAT d₂ = differ2-QNAT
differ2-subv {name1} {name2} {f} cf v {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (differ2-LT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-LT _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (differ2-QLT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-QLT _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(NUM x)} {.(NUM x)} {b₁} {b₂} (differ2-NUM x) d₂ = differ2-NUM x
differ2-subv {name1} {name2} {f} cf v {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₃)} {b₁} {b₂} (differ2-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄ d₅ d₆ d₇) d₂ = differ2-IFLT _ _ _ _ _ _ _ _ (differ2-subv cf v d₄ d₂) (differ2-subv cf v d₅ d₂) (differ2-subv cf v d₆ d₂) (differ2-subv cf v d₇ d₂)
differ2-subv {name1} {name2} {f} cf v {.(SUC a)} {.(SUC b)} {b₁} {b₂} (differ2-SUC a b d₁) d₂ = differ2-SUC _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (differ2-PI a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-PI _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf (suc v) d₃ (→differ2-shiftUp 0 cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(LAMBDA a)} {.(LAMBDA b)} {b₁} {b₂} (differ2-LAMBDA a b d₁) d₂ = differ2-LAMBDA _ _ (differ2-subv cf (suc v) d₁ (→differ2-shiftUp 0 cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (differ2-APPLY a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-APPLY _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(FIX a)} {.(FIX b)} {b₁} {b₂} (differ2-FIX a b d₁) d₂ = differ2-FIX _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (differ2-LET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-LET _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf (suc v) d₃ (→differ2-shiftUp 0 cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (differ2-SUM a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-SUM _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf (suc v) d₃ (→differ2-shiftUp 0 cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (differ2-PAIR a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-PAIR _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (differ2-SPREAD a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-SPREAD _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf (suc (suc v)) d₃ (→differ2-shiftUp 0 cf (→differ2-shiftUp 0 cf d₂)))
differ2-subv {name1} {name2} {f} cf v {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (differ2-SET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-SET _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf (suc v) d₃ (→differ2-shiftUp 0 cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(ISECT a₁ b₃)} {.(ISECT a₂ b₄)} {b₁} {b₂} (differ2-ISECT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-ISECT _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (differ2-TUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-TUNION _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf (suc v) d₃ (→differ2-shiftUp 0 cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (differ2-UNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-UNION _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (differ2-QTUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-QTUNION _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(INL a)} {.(INL b)} {b₁} {b₂} (differ2-INL a b d₁) d₂ = differ2-INL _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(INR a)} {.(INR b)} {b₁} {b₂} (differ2-INR a b d₁) d₂ = differ2-INR _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (differ2-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ2-DECIDE _ _ _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf (suc v) d₃ (→differ2-shiftUp 0 cf d₂)) (differ2-subv cf (suc v) d₄ (→differ2-shiftUp 0 cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (differ2-EQ a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ2-EQ _ _ _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂) (differ2-subv cf v d₄ d₂)
differ2-subv {name1} {name2} {f} cf v {.AX} {.AX} {b₁} {b₂} differ2-AX d₂ = differ2-AX
differ2-subv {name1} {name2} {f} cf v {.FREE} {.FREE} {b₁} {b₂} differ2-FREE d₂ = differ2-FREE
differ2-subv {name1} {name2} {f} cf v {.(CS name)} {.(CS name)} {b₁} {b₂} (differ2-CS name) d₂ = differ2-CS name
differ2-subv {name1} {name2} {f} cf v {.(NAME name)} {.(NAME name)} {b₁} {b₂} (differ2-NAME name) d₂ = differ2-NAME name
differ2-subv {name1} {name2} {f} cf v {.(FRESH a)} {.(FRESH b)} {b₁} {b₂} (differ2-FRESH a b d₁) d₂ = differ2-FRESH _ _ (differ2-subv (→#shiftNameUp 0 {f} cf) v d₁ (→differ2-shiftNameUp0 {name1} {name2} cf d₂))
differ2-subv {name1} {name2} {f} cf v {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (differ2-CHOOSE a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-CHOOSE _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
--differ2-subv {name1} {name2} {f} cf v {.(IFC0 a₁ b₃ c₁)} {.(IFC0 a₂ b₄ c₂)} {b₁} {b₂} (differ2-IFC0 a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ2-IFC0 _ _ _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂) (differ2-subv cf v d₄ d₂)
differ2-subv {name1} {name2} {f} cf v {.(TSQUASH a)} {.(TSQUASH b)} {b₁} {b₂} (differ2-TSQUASH a b d₁) d₂ = differ2-TSQUASH _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(TTRUNC a)} {.(TTRUNC b)} {b₁} {b₂} (differ2-TTRUNC a b d₁) d₂ = differ2-TTRUNC _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(TCONST a)} {.(TCONST b)} {b₁} {b₂} (differ2-TCONST a b d₁) d₂ = differ2-TCONST _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(SUBSING a)} {.(SUBSING b)} {b₁} {b₂} (differ2-SUBSING a b d₁) d₂ = differ2-SUBSING _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(PURE)} {.(PURE)} {b₁} {b₂} (differ2-PURE) d₂ = differ2-PURE
differ2-subv {name1} {name2} {f} cf v {.(DUM a)} {.(DUM b)} {b₁} {b₂} (differ2-DUM a b d₁) d₂ = differ2-DUM _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(FFDEFS a₁ b₃)} {.(FFDEFS a₂ b₄)} {b₁} {b₂} (differ2-FFDEFS a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ2-FFDEFS _ _ _ _ (differ2-subv cf v d₁ d₂) (differ2-subv cf v d₃ d₂)
differ2-subv {name1} {name2} {f} cf v {.(UNIV x)} {.(UNIV x)} {b₁} {b₂} (differ2-UNIV x) d₂ = differ2-UNIV x
differ2-subv {name1} {name2} {f} cf v {.(LIFT a)} {.(LIFT b)} {b₁} {b₂} (differ2-LIFT a b d₁) d₂ = differ2-LIFT _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(LOWER a)} {.(LOWER b)} {b₁} {b₂} (differ2-LOWER a b d₁) d₂ = differ2-LOWER _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(SHRINK a)} {.(SHRINK b)} {b₁} {b₂} (differ2-SHRINK a b d₁) d₂ = differ2-SHRINK _ _ (differ2-subv cf v d₁ d₂)
differ2-subv {name1} {name2} {f} cf v {.(upd name1 f)} {.(upd name2 f)} {b₁} {b₂} differ2-upd d₂
  rewrite sucIf≤00
        | subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₁))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
        | subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₂))) (shiftUp 0 f) (→#shiftUp 0 {f} cf) = differ2-upd


→differ2-shiftDown : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                     → differ2 name1 name2 f a b
                     → differ2 name1 name2 f (shiftDown v a) (shiftDown v b)
→differ2-shiftDown v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ2-VAR x) = differ2-VAR _
→differ2-shiftDown v {name1} {name2} {f} cf {.NAT} {.NAT} differ2-NAT = differ2-NAT
→differ2-shiftDown v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ2-QNAT = differ2-QNAT
→differ2-shiftDown v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ2-LT a₁ a₂ b₁ b₂ diff diff₁) = differ2-LT _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ2-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ2-QLT _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ2-NUM x) = differ2-NUM x
→differ2-shiftDown v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ2-IFLT _ _ _ _ _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁) (→differ2-shiftDown v cf diff₂) (→differ2-shiftDown v cf diff₃)
→differ2-shiftDown v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ2-SUC a b diff) = differ2-SUC _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ2-PI a₁ a₂ b₁ b₂ diff diff₁) = differ2-PI _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown (suc v) cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ2-LAMBDA a b diff) = differ2-LAMBDA _ _ (→differ2-shiftDown (suc v) cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ2-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ2-APPLY _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ2-FIX a b diff) = differ2-FIX _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ2-LET a₁ a₂ b₁ b₂ diff diff₁) = differ2-LET _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown (suc v) cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ2-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ2-SUM _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown (suc v) cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ2-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ2-PAIR _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ2-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ2-SPREAD _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown (suc (suc v)) cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ2-SET a₁ a₂ b₁ b₂ diff diff₁) = differ2-SET _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown (suc v) cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ2-ISECT a₁ a₂ b₁ b₂ diff diff₁) = differ2-ISECT _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ2-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-TUNION _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown (suc v) cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ2-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-UNION _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ2-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ2-QTUNION _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ2-INL a b diff) = differ2-INL _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ2-INR a b diff) = differ2-INR _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-DECIDE _ _ _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown (suc v) cf diff₁) (→differ2-shiftDown (suc v) cf diff₂)
→differ2-shiftDown v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ2-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-EQ _ _ _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁) (→differ2-shiftDown v cf diff₂)
→differ2-shiftDown v {name1} {name2} {f} cf {.AX} {.AX} differ2-AX = differ2-AX
→differ2-shiftDown v {name1} {name2} {f} cf {.FREE} {.FREE} differ2-FREE = differ2-FREE
→differ2-shiftDown v {name1} {name2} {f} cf {.(CS name)} {.(CS name)} (differ2-CS name) = (differ2-CS name)
→differ2-shiftDown v {name1} {name2} {f} cf {.(NAME name)} {.(NAME name)} (differ2-NAME name) = (differ2-NAME name)
→differ2-shiftDown v {name1} {name2} {f} cf {.(FRESH a)} {.(FRESH b)} (differ2-FRESH a b diff) = differ2-FRESH _ _ (→differ2-shiftDown v (→#shiftNameUp 0 {f} cf) diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ2-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ2-CHOOSE _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
--→differ2-shiftDown v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ2-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ2-IFC0 _ _ _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁) (→differ2-shiftDown v cf diff₂)
→differ2-shiftDown v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ2-TSQUASH a b diff) = differ2-TSQUASH _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ2-TTRUNC a b diff) = differ2-TTRUNC _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(TCONST a)} {.(TCONST b)} (differ2-TCONST a b diff) = differ2-TCONST _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ2-SUBSING a b diff) = differ2-SUBSING _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(PURE)} {.(PURE)} (differ2-PURE) = differ2-PURE
→differ2-shiftDown v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ2-DUM a b diff) = differ2-DUM _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ2-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ2-FFDEFS _ _ _ _ (→differ2-shiftDown v cf diff) (→differ2-shiftDown v cf diff₁)
→differ2-shiftDown v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ2-UNIV x) = differ2-UNIV x
→differ2-shiftDown v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ2-LIFT a b diff) = differ2-LIFT _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ2-LOWER a b diff) = differ2-LOWER _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ2-SHRINK a b diff) = differ2-SHRINK _ _ (→differ2-shiftDown v cf diff)
→differ2-shiftDown v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ2-upd rewrite sucIf≤s0 v | #shiftDown (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = differ2-upd


differ2-sub : {name1 name2 : Name} {f : Term} (cf : # f) {a₁ a₂ b₁ b₂ : Term}
             → differ2 name1 name2 f a₁ a₂
             → differ2 name1 name2 f b₁ b₂
             → differ2 name1 name2 f (sub b₁ a₁) (sub b₂ a₂)
differ2-sub {name1} {name2} {f} cf {a₁} {a₂} {b₁} {b₂} d₁ d₂ =
  →differ2-shiftDown 0 cf (differ2-subv {name1} {name2} {f} cf 0 {a₁} {a₂} {shiftUp 0 b₁} {shiftUp 0 b₂} d₁ (→differ2-shiftUp 0 cf d₂))


differ2-isValue→ : {name1 name2 : Name} {f : Term} {a b : Term}
                   → differ2 name1 name2 f a b
                   → isValue a
                   → isValue b
differ2-isValue→ {name1} {name2} {f} {.NAT} {.NAT} differ2-NAT isv = tt
differ2-isValue→ {name1} {name2} {f} {.QNAT} {.QNAT} differ2-QNAT isv = tt
differ2-isValue→ {name1} {name2} {f} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ2-LT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ2-QLT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(NUM x)} {.(NUM x)} (differ2-NUM x) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ2-PI a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(LAMBDA a)} {.(LAMBDA b)} (differ2-LAMBDA a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ2-SUM a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ2-PAIR a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ2-SET a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (differ2-ISECT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ2-TUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ2-UNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ2-QTUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(INL a)} {.(INL b)} (differ2-INL a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(INR a)} {.(INR b)} (differ2-INR a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ2-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) isv = tt
differ2-isValue→ {name1} {name2} {f} {.AX} {.AX} differ2-AX isv = tt
differ2-isValue→ {name1} {name2} {f} {.FREE} {.FREE} differ2-FREE isv = tt
differ2-isValue→ {name1} {name2} {f} {.(CS name)} {.(CS name)} (differ2-CS name) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(NAME name)} {.(NAME name)} (differ2-NAME name) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(FRESH a)} {.(FRESH b)} (differ2-FRESH a b diff) ()
differ2-isValue→ {name1} {name2} {f} {.(TSQUASH a)} {.(TSQUASH b)} (differ2-TSQUASH a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(TTRUNC a)} {.(TTRUNC b)} (differ2-TTRUNC a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(TCONST a)} {.(TCONST b)} (differ2-TCONST a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(SUBSING a)} {.(SUBSING b)} (differ2-SUBSING a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(PURE)} {.(PURE)} (differ2-PURE) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(DUM a)} {.(DUM b)} (differ2-DUM a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ2-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(UNIV x)} {.(UNIV x)} (differ2-UNIV x) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(LIFT a)} {.(LIFT b)} (differ2-LIFT a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(LOWER a)} {.(LOWER b)} (differ2-LOWER a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(SHRINK a)} {.(SHRINK b)} (differ2-SHRINK a b diff) isv = tt
differ2-isValue→ {name1} {name2} {f} {.(upd name1 f)} {.(upd name2 f)} differ2-upd isv = tt


differ2-refl : {name1 name2 : Name} {f : Term} {a : Term} → differ2 name1 name2 f a a
differ2-refl {name1} {name2} {f} {VAR x} = differ2-VAR _
differ2-refl {name1} {name2} {f} {NAT} = differ2-NAT
differ2-refl {name1} {name2} {f} {QNAT} = differ2-QNAT
differ2-refl {name1} {name2} {f} {LT a a₁} = differ2-LT _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {QLT a a₁} = differ2-QLT _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {NUM x} = differ2-NUM _
differ2-refl {name1} {name2} {f} {IFLT a a₁ a₂ a₃} = differ2-IFLT _ _ _ _ _ _ _ _ differ2-refl differ2-refl differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {SUC a} = differ2-SUC _ _ differ2-refl
differ2-refl {name1} {name2} {f} {PI a a₁} = differ2-PI _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {LAMBDA a} = differ2-LAMBDA _ _ differ2-refl
differ2-refl {name1} {name2} {f} {APPLY a a₁} = differ2-APPLY _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {FIX a} = differ2-FIX _ _ differ2-refl
differ2-refl {name1} {name2} {f} {LET a a₁} = differ2-LET _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {SUM a a₁} = differ2-SUM _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {PAIR a a₁} = differ2-PAIR _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {SPREAD a a₁} = differ2-SPREAD _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {SET a a₁} = differ2-SET _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {TUNION a a₁} = differ2-TUNION _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {ISECT a a₁} = differ2-ISECT _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {UNION a a₁} = differ2-UNION _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {QTUNION a a₁} = differ2-QTUNION _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {INL a} = differ2-INL _ _ differ2-refl
differ2-refl {name1} {name2} {f} {INR a} = differ2-INR _ _ differ2-refl
differ2-refl {name1} {name2} {f} {DECIDE a a₁ a₂} = differ2-DECIDE _ _ _ _ _ _ differ2-refl differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {EQ a a₁ a₂} = differ2-EQ _ _ _ _ _ _ differ2-refl differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {AX} = differ2-AX
differ2-refl {name1} {name2} {f} {FREE} = differ2-FREE
differ2-refl {name1} {name2} {f} {CS x} = differ2-CS _
differ2-refl {name1} {name2} {f} {NAME x} = differ2-NAME _
differ2-refl {name1} {name2} {f} {FRESH a} = differ2-FRESH _ _ differ2-refl
differ2-refl {name1} {name2} {f} {CHOOSE a a₁} = differ2-CHOOSE _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {TSQUASH a} = differ2-TSQUASH _ _ differ2-refl
differ2-refl {name1} {name2} {f} {TTRUNC a} = differ2-TTRUNC _ _ differ2-refl
differ2-refl {name1} {name2} {f} {TCONST a} = differ2-TCONST _ _ differ2-refl
differ2-refl {name1} {name2} {f} {SUBSING a} = differ2-SUBSING _ _ differ2-refl
differ2-refl {name1} {name2} {f} {DUM a} = differ2-DUM _ _ differ2-refl
differ2-refl {name1} {name2} {f} {FFDEFS a a₁} = differ2-FFDEFS _ _ _ _ differ2-refl differ2-refl
differ2-refl {name1} {name2} {f} {PURE} = differ2-PURE
differ2-refl {name1} {name2} {f} {UNIV x} = differ2-UNIV _
differ2-refl {name1} {name2} {f} {LIFT a} = differ2-LIFT _ _ differ2-refl
differ2-refl {name1} {name2} {f} {LOWER a} = differ2-LOWER _ _ differ2-refl
differ2-refl {name1} {name2} {f} {SHRINK a} = differ2-SHRINK _ _ differ2-refl


\end{code}

