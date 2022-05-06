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


module terms3 {L : Level} (W : PossibleWorlds {L})
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




get0 : (name : Name) → Term
get0 name = APPLY (CS name) (NUM 0)


setT : (name : Name) (T : Term) → Term
setT name t = CHOOSE (NAME name) t


updGt : (name : Name) (t : Term) → Term
updGt name t = IFLT (get0 name) t (setT name t) AX


-- TODO: we need choose to update the world only if the number is higher than the one stored
-- This will be specified as a constraint of the 'choose' operator from getChoice.lagda
-- We throw in a CBV to reduce the argument to a number
updBody : (name : Name) (f : Term) → Term
updBody name f = LET (VAR 0) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))


upd : (name : Name) (f : Term) → Term
upd name f = LAMBDA (updBody name f)


data differ (name1 name2 : Name) (f : Term) : Term → Term → Set where
  differ-VAR     : (x : Var) → differ name1 name2 f (VAR x) (VAR x)
  differ-NAT     : differ name1 name2 f NAT NAT
  differ-QNAT    : differ name1 name2 f QNAT QNAT
  differ-LT      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (LT a₁ b₁) (LT a₂ b₂)
  differ-QLT     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (QLT a₁ b₁) (QLT a₂ b₂)
  differ-NUM     : (x : ℕ) → differ name1 name2 f (NUM x) (NUM x)
  differ-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f d₁ d₂ → differ name1 name2 f (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  differ-SUC     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SUC a) (SUC b)
  differ-PI      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (PI a₁ b₁) (PI a₂ b₂)
  differ-LAMBDA  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LAMBDA a) (LAMBDA b)
  differ-APPLY   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (APPLY a₁ b₁) (APPLY a₂ b₂)
  differ-FIX     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (FIX a) (FIX b)
  differ-LET     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (LET a₁ b₁) (LET a₂ b₂)
  differ-SUM     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SUM a₁ b₁) (SUM a₂ b₂)
  differ-PAIR    : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (PAIR a₁ b₁) (PAIR a₂ b₂)
  differ-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  differ-SET     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (SET a₁ b₁) (SET a₂ b₂)
  differ-TUNION  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (TUNION a₁ b₁) (TUNION a₂ b₂)
  differ-UNION   : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (UNION a₁ b₁) (UNION a₂ b₂)
  differ-QTUNION : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  differ-INL     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (INL a) (INL b)
  differ-INR     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (INR a) (INR b)
  differ-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  differ-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  differ-AX      : differ name1 name2 f AX AX
  differ-FREE    : differ name1 name2 f FREE FREE
  --differ-CS      : differ name1 name2 f (CS name1) (CS name2)
  --differ-CS      : differ name1 name2 f (CS name1) (CS name2)
  --differ-NAME    : differ name1 name2 f (NAME name1) (NAME name2)
  --differ-FRESH   : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (FRESH a) (FRESH b)
  differ-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  differ-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  differ-TSQUASH : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TSQUASH a) (TSQUASH b)
  differ-TTRUNC  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TTRUNC a) (TTRUNC b)
  differ-TCONST  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (TCONST a) (TCONST b)
  differ-SUBSING : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SUBSING a) (SUBSING b)
  differ-DUM     : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (DUM a) (DUM b)
  differ-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  differ-UNIV    : (x : ℕ) → differ name1 name2 f (UNIV x) (UNIV x)
  differ-LIFT    : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LIFT a) (LIFT b)
  differ-LOWER   : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (LOWER a) (LOWER b)
  differ-SHRINK  : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (SHRINK a) (SHRINK b)
  differ-upd     : differ name1 name2 f (upd name1 f) (upd name2 f)



∈ℕ : (w : 𝕎·) (t : Term) → Set(lsuc(L))
∈ℕ w t = Σ ℕ (λ n → t ⇛ (NUM n) at w)



differ-NUM→ : {name1 name2 : Name} {f t : Term} {m : ℕ}
               → differ name1 name2 f (NUM m) t
               → t ≡ NUM m
differ-NUM→ {name1} {name2} {f} {.(NUM m)} {m} (differ-NUM .m) = refl



differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (CS name) t
differ-CSₗ→ {name1} {name2} {name} {f} {t} ()


differ-NAMEₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (NAME name) t
differ-NAMEₗ→ {name1} {name2} {name} {f} {t} ()


differ-LAMBDAₗ→ : {name1 name2 : Name} {f g t : Term}
                  → differ name1 name2 f (LAMBDA g) t
                  → Σ Term (λ g' → t ≡ LAMBDA g' × differ name1 name2 f g g')
                    ⊎ (g ≡ updBody name1 f × t ≡ upd name2 f)
differ-LAMBDAₗ→ {name1} {name2} {f} {g} {.(LAMBDA b)} (differ-LAMBDA .g b d) = inj₁ (b , refl , d)
differ-LAMBDAₗ→ {name1} {name2} {f} {.(updBody name1 f)} {.(upd name2 f)} differ-upd = inj₂ (refl , refl)


differ-PAIRₗ→ : {name1 name2 : Name} {f a b t : Term}
                  → differ name1 name2 f (PAIR a b) t
                  → Σ Term (λ a' → Σ Term (λ b' → t ≡ PAIR a' b' × differ name1 name2 f a a' × differ name1 name2 f b b'))
differ-PAIRₗ→ {name1} {name2} {f} {a} {b} {.(PAIR a₂ b₂)} (differ-PAIR .a a₂ .b b₂ diff diff₁) = a₂ , b₂ , refl , diff , diff₁


differ-INLₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ name1 name2 f (INL a) t
                → Σ Term (λ a' → t ≡ INL a' × differ name1 name2 f a a')
differ-INLₗ→ {name1} {name2} {f} {a} {.(INL a₂)} (differ-INL .a a₂ diff) = a₂ , refl , diff


differ-INRₗ→ : {name1 name2 : Name} {f a t : Term}
                → differ name1 name2 f (INR a) t
                → Σ Term (λ a' → t ≡ INR a' × differ name1 name2 f a a')
differ-INRₗ→ {name1} {name2} {f} {a} {.(INR a₂)} (differ-INR .a a₂ diff) = a₂ , refl , diff



→differ-shiftUp : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                   → differ name1 name2 f a b
                   → differ name1 name2 f (shiftUp v a) (shiftUp v b)
→differ-shiftUp v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ-VAR x) = differ-VAR _
→differ-shiftUp v {name1} {name2} {f} cf {.NAT} {.NAT} differ-NAT = differ-NAT
→differ-shiftUp v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ-QNAT = differ-QNAT
→differ-shiftUp v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) = differ-LT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ-QLT _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ-NUM x) = differ-NUM x
→differ-shiftUp v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFLT _ _ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂) (→differ-shiftUp v cf diff₃)
→differ-shiftUp v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ-SUC a b diff) = differ-SUC _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) = differ-PI _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) = differ-LAMBDA _ _ (→differ-shiftUp (suc v) cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ-APPLY _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ-FIX a b diff) = differ-FIX _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ-LET a₁ a₂ b₁ b₂ diff diff₁) = differ-LET _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ-SUM _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ-PAIR _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ-SPREAD _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc (suc v)) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) = differ-SET _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-TUNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ-UNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-QTUNION _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ-INL a b diff) = differ-INL _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ-INR a b diff) = differ-INR _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-DECIDE _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp (suc v) cf diff₁) (→differ-shiftUp (suc v) cf diff₂)
→differ-shiftUp v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-EQ _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂)
→differ-shiftUp v {name1} {name2} {f} cf {.AX} {.AX} differ-AX = differ-AX
→differ-shiftUp v {name1} {name2} {f} cf {.FREE} {.FREE} differ-FREE = differ-FREE
--→differ-shiftUp v {name1} {name2} {f} cf {.(CS name1)} {.(CS name2)} differ-CS = differ-CS
→differ-shiftUp v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ-CHOOSE _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
--→differ-shiftUp v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-IFC0 _ _ _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁) (→differ-shiftUp v cf diff₂)
→differ-shiftUp v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) = differ-TSQUASH _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) = differ-TTRUNC _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(TCONST a)} {.(TCONST b)} (differ-TCONST a b diff) = differ-TCONST _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) = differ-SUBSING _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) = differ-DUM _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ-FFDEFS _ _ _ _ (→differ-shiftUp v cf diff) (→differ-shiftUp v cf diff₁)
→differ-shiftUp v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) = differ-UNIV x
→differ-shiftUp v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) = differ-LIFT _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) = differ-LOWER _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) = differ-SHRINK _ _ (→differ-shiftUp v cf diff)
→differ-shiftUp v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ-upd rewrite sucIf≤s0 v | #shiftUp (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = differ-upd



differ-subv : {name1 name2 : Name} {f : Term} (cf : # f) (v : Var) {a₁ a₂ b₁ b₂ : Term}
             → differ name1 name2 f a₁ a₂
             → differ name1 name2 f b₁ b₂
             → differ name1 name2 f (subv v b₁ a₁) (subv v b₂ a₂)
differ-subv {name1} {name2} {f} cf v {.(VAR x)} {.(VAR x)} {b₁} {b₂} (differ-VAR x) d₂ with x ≟ v
... | yes p = d₂ -- rewrite shiftDownUp b₁ 0 | shiftDownUp b₂ 0 = d₂
... | no p = differ-VAR _
differ-subv {name1} {name2} {f} cf v {.NAT} {.NAT} {b₁} {b₂} differ-NAT d₂ = differ-NAT
differ-subv {name1} {name2} {f} cf v {.QNAT} {.QNAT} {b₁} {b₂} differ-QNAT d₂ = differ-QNAT
differ-subv {name1} {name2} {f} cf v {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (differ-LT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-LT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (differ-QLT a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-QLT _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(NUM x)} {.(NUM x)} {b₁} {b₂} (differ-NUM x) d₂ = differ-NUM x
differ-subv {name1} {name2} {f} cf v {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₃)} {b₁} {b₂} (differ-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄ d₅ d₆ d₇) d₂ = differ-IFLT _ _ _ _ _ _ _ _ (differ-subv cf v d₄ d₂) (differ-subv cf v d₅ d₂) (differ-subv cf v d₆ d₂) (differ-subv cf v d₇ d₂)
differ-subv {name1} {name2} {f} cf v {.(SUC a)} {.(SUC b)} {b₁} {b₂} (differ-SUC a b d₁) d₂ = differ-SUC _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (differ-PI a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-PI _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(LAMBDA a)} {.(LAMBDA b)} {b₁} {b₂} (differ-LAMBDA a b d₁) d₂ = differ-LAMBDA _ _ (differ-subv cf (suc v) d₁ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (differ-APPLY a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-APPLY _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(FIX a)} {.(FIX b)} {b₁} {b₂} (differ-FIX a b d₁) d₂ = differ-FIX _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (differ-LET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-LET _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (differ-SUM a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SUM _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (differ-PAIR a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-PAIR _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (differ-SPREAD a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SPREAD _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc (suc v)) d₃ (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf d₂)))
differ-subv {name1} {name2} {f} cf v {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (differ-SET a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-SET _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (differ-TUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-TUNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (differ-UNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-UNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (differ-QTUNION a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-QTUNION _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(INL a)} {.(INL b)} {b₁} {b₂} (differ-INL a b d₁) d₂ = differ-INL _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(INR a)} {.(INR b)} {b₁} {b₂} (differ-INR a b d₁) d₂ = differ-INR _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (differ-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-DECIDE _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf (suc v) d₃ (→differ-shiftUp 0 cf d₂)) (differ-subv cf (suc v) d₄ (→differ-shiftUp 0 cf d₂))
differ-subv {name1} {name2} {f} cf v {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (differ-EQ a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-EQ _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂) (differ-subv cf v d₄ d₂)
differ-subv {name1} {name2} {f} cf v {.AX} {.AX} {b₁} {b₂} differ-AX d₂ = differ-AX
differ-subv {name1} {name2} {f} cf v {.FREE} {.FREE} {b₁} {b₂} differ-FREE d₂ = differ-FREE
--differ-subv {name1} {name2} {f} cf v {.(CS name1)} {.(CS name2)} {b₁} {b₂} differ-CS d₂ = differ-CS
differ-subv {name1} {name2} {f} cf v {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (differ-CHOOSE a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-CHOOSE _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
--differ-subv {name1} {name2} {f} cf v {.(IFC0 a₁ b₃ c₁)} {.(IFC0 a₂ b₄ c₂)} {b₁} {b₂} (differ-IFC0 a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₃ d₄) d₂ = differ-IFC0 _ _ _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂) (differ-subv cf v d₄ d₂)
differ-subv {name1} {name2} {f} cf v {.(TSQUASH a)} {.(TSQUASH b)} {b₁} {b₂} (differ-TSQUASH a b d₁) d₂ = differ-TSQUASH _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(TTRUNC a)} {.(TTRUNC b)} {b₁} {b₂} (differ-TTRUNC a b d₁) d₂ = differ-TTRUNC _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(TCONST a)} {.(TCONST b)} {b₁} {b₂} (differ-TCONST a b d₁) d₂ = differ-TCONST _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(SUBSING a)} {.(SUBSING b)} {b₁} {b₂} (differ-SUBSING a b d₁) d₂ = differ-SUBSING _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(DUM a)} {.(DUM b)} {b₁} {b₂} (differ-DUM a b d₁) d₂ = differ-DUM _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(FFDEFS a₁ b₃)} {.(FFDEFS a₂ b₄)} {b₁} {b₂} (differ-FFDEFS a₁ a₂ b₃ b₄ d₁ d₃) d₂ = differ-FFDEFS _ _ _ _ (differ-subv cf v d₁ d₂) (differ-subv cf v d₃ d₂)
differ-subv {name1} {name2} {f} cf v {.(UNIV x)} {.(UNIV x)} {b₁} {b₂} (differ-UNIV x) d₂ = differ-UNIV x
differ-subv {name1} {name2} {f} cf v {.(LIFT a)} {.(LIFT b)} {b₁} {b₂} (differ-LIFT a b d₁) d₂ = differ-LIFT _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(LOWER a)} {.(LOWER b)} {b₁} {b₂} (differ-LOWER a b d₁) d₂ = differ-LOWER _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(SHRINK a)} {.(SHRINK b)} {b₁} {b₂} (differ-SHRINK a b d₁) d₂ = differ-SHRINK _ _ (differ-subv cf v d₁ d₂)
differ-subv {name1} {name2} {f} cf v {.(upd name1 f)} {.(upd name2 f)} {b₁} {b₂} differ-upd d₂
  rewrite sucIf≤00
        | subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₁))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
        | subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₂))) (shiftUp 0 f) (→#shiftUp 0 {f} cf) = differ-upd


→differ-shiftDown : (v : Var) {name1 name2 : Name} {f : Term} (cf : # f) {a b : Term}
                     → differ name1 name2 f a b
                     → differ name1 name2 f (shiftDown v a) (shiftDown v b)
→differ-shiftDown v {name1} {name2} {f} cf {.(VAR x)} {.(VAR x)} (differ-VAR x) = differ-VAR _
→differ-shiftDown v {name1} {name2} {f} cf {.NAT} {.NAT} differ-NAT = differ-NAT
→differ-shiftDown v {name1} {name2} {f} cf {.QNAT} {.QNAT} differ-QNAT = differ-QNAT
→differ-shiftDown v {name1} {name2} {f} cf {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) = differ-LT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) = differ-QLT _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(NUM x)} {.(NUM x)} (differ-NUM x) = differ-NUM x
→differ-shiftDown v {name1} {name2} {f} cf {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (differ-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) = differ-IFLT _ _ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂) (→differ-shiftDown v cf diff₃)
→differ-shiftDown v {name1} {name2} {f} cf {.(SUC a)} {.(SUC b)} (differ-SUC a b diff) = differ-SUC _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) = differ-PI _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) = differ-LAMBDA _ _ (→differ-shiftDown (suc v) cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) = differ-APPLY _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(FIX a)} {.(FIX b)} (differ-FIX a b diff) = differ-FIX _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(LET a₁ b₁)} {.(LET a₂ b₂)} (differ-LET a₁ a₂ b₁ b₂ diff diff₁) = differ-LET _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) = differ-SUM _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) = differ-PAIR _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) = differ-SPREAD _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc (suc v)) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) = differ-SET _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-TUNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) = differ-UNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) = differ-QTUNION _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(INL a)} {.(INL b)} (differ-INL a b diff) = differ-INL _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(INR a)} {.(INR b)} (differ-INR a b diff) = differ-INR _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (differ-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-DECIDE _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown (suc v) cf diff₁) (→differ-shiftDown (suc v) cf diff₂)
→differ-shiftDown v {name1} {name2} {f} cf {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-EQ _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂)
→differ-shiftDown v {name1} {name2} {f} cf {.AX} {.AX} differ-AX = differ-AX
→differ-shiftDown v {name1} {name2} {f} cf {.FREE} {.FREE} differ-FREE = differ-FREE
--→differ-shiftDown v {name1} {name2} {f} cf {.(CS name1)} {.(CS name2)} differ-CS = differ-CS
→differ-shiftDown v {name1} {name2} {f} cf {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) = differ-CHOOSE _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
--→differ-shiftDown v {name1} {name2} {f} cf {.(IFC0 a₁ b₁ c₁)} {.(IFC0 a₂ b₂ c₂)} (differ-IFC0 a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) = differ-IFC0 _ _ _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁) (→differ-shiftDown v cf diff₂)
→differ-shiftDown v {name1} {name2} {f} cf {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) = differ-TSQUASH _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) = differ-TTRUNC _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(TCONST a)} {.(TCONST b)} (differ-TCONST a b diff) = differ-TCONST _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) = differ-SUBSING _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) = differ-DUM _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) = differ-FFDEFS _ _ _ _ (→differ-shiftDown v cf diff) (→differ-shiftDown v cf diff₁)
→differ-shiftDown v {name1} {name2} {f} cf {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) = differ-UNIV x
→differ-shiftDown v {name1} {name2} {f} cf {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) = differ-LIFT _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) = differ-LOWER _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) = differ-SHRINK _ _ (→differ-shiftDown v cf diff)
→differ-shiftDown v {name1} {name2} {f} cf {.(upd name1 f)} {.(upd name2 f)} differ-upd rewrite sucIf≤s0 v | #shiftDown (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = differ-upd


differ-sub : {name1 name2 : Name} {f : Term} (cf : # f) {a₁ a₂ b₁ b₂ : Term}
             → differ name1 name2 f a₁ a₂
             → differ name1 name2 f b₁ b₂
             → differ name1 name2 f (sub b₁ a₁) (sub b₂ a₂)
differ-sub {name1} {name2} {f} cf {a₁} {a₂} {b₁} {b₂} d₁ d₂ =
  →differ-shiftDown 0 cf (differ-subv {name1} {name2} {f} cf 0 {a₁} {a₂} {shiftUp 0 b₁} {shiftUp 0 b₂} d₁ (→differ-shiftUp 0 cf d₂))


differ-isValue→ : {name1 name2 : Name} {f : Term} {a b : Term}
                   → differ name1 name2 f a b
                   → isValue a
                   → isValue b
differ-isValue→ {name1} {name2} {f} {.NAT} {.NAT} differ-NAT isv = tt
differ-isValue→ {name1} {name2} {f} {.QNAT} {.QNAT} differ-QNAT isv = tt
differ-isValue→ {name1} {name2} {f} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (differ-LT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(NUM x)} {.(NUM x)} (differ-NUM x) isv = tt
differ-isValue→ {name1} {name2} {f} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (differ-PI a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(LAMBDA a)} {.(LAMBDA b)} (differ-LAMBDA a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (differ-SET a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(INL a)} {.(INL b)} (differ-INL a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(INR a)} {.(INR b)} (differ-INR a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (differ-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) isv = tt
differ-isValue→ {name1} {name2} {f} {.AX} {.AX} differ-AX isv = tt
differ-isValue→ {name1} {name2} {f} {.FREE} {.FREE} differ-FREE isv = tt
--differ-isValue→ {name1} {name2} {f} {.(CS name1)} {.(CS name2)} differ-CS isv = tt
differ-isValue→ {name1} {name2} {f} {.(TSQUASH a)} {.(TSQUASH b)} (differ-TSQUASH a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(TTRUNC a)} {.(TTRUNC b)} (differ-TTRUNC a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(TCONST a)} {.(TCONST b)} (differ-TCONST a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SUBSING a)} {.(SUBSING b)} (differ-SUBSING a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(DUM a)} {.(DUM b)} (differ-DUM a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) isv = tt
differ-isValue→ {name1} {name2} {f} {.(UNIV x)} {.(UNIV x)} (differ-UNIV x) isv = tt
differ-isValue→ {name1} {name2} {f} {.(LIFT a)} {.(LIFT b)} (differ-LIFT a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(LOWER a)} {.(LOWER b)} (differ-LOWER a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(SHRINK a)} {.(SHRINK b)} (differ-SHRINK a b diff) isv = tt
differ-isValue→ {name1} {name2} {f} {.(upd name1 f)} {.(upd name2 f)} differ-upd isv = tt



sub-upd : (name : Name) (f : Term) (a : Term) (cf : # f)
          → sub a (updBody name f) ≡ LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))
sub-upd name f a cf
  rewrite #shiftUp 0 (ct f cf)
        | shiftDownUp a 0
        | #subv 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 a))) f cf
        | #shiftDown 2 (ct f cf) = refl


sub-SEQ-updGt : (u : Term) (name : Name) (f : Term) (cf : # f)
                → sub u (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))
                   ≡ LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))
sub-SEQ-updGt u name f cf
  rewrite #shiftUp 0 (ct f cf)
        | shiftDownUp u 0
        | #subv 1 (shiftUp 0 (shiftUp 0 u)) f cf
        | #shiftDown 1 (ct f cf) = refl


getT⊎ : (n : ℕ) (cs : Name) (w : 𝕎·) → (Σ Term (λ t → getT n cs w ≡ just t) ⊎ getT n cs w ≡ nothing)
getT⊎ n cs w with getT n cs w
... | just t = inj₁ (t , refl)
... | nothing = inj₂ refl



steps-get0 : (k : ℕ) (name : Name) (w w' : 𝕎·) (v : Term)
             → isValue v
             → steps k (get0 name , w) ≡ (v , w')
             → Σ Term (λ u → Σ ℕ (λ k' → k' < k × getT 0 name w ≡ just u × steps k' (u , w) ≡ (v , w')))
steps-get0 0 name w w' t isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
steps-get0 (suc k) name w w' t isv comp with getT⊎ 0 name w
... | inj₁ (u , z) rewrite z = u , k , ≤-refl , refl , comp
... | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



≡Term→≡steps : (k : ℕ) {a b : Term} (w : 𝕎·) → a ≡ b → steps k (a , w) ≡ steps k (b , w)
≡Term→≡steps k {a} {b} w e rewrite e = refl

\end{code}

