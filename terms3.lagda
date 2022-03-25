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
upd : (name : Name) (f : Term) → Term
upd name f = LAMBDA (LET (VAR 0) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))))


data differ (name1 name2 : Name) (f : Term) : Term → Term → Set where
  differ-VAR     : (x : Var) → differ name1 name2 f (VAR x) (VAR x)
  differ-NAT     : differ name1 name2 f NAT NAT
  differ-QNAT    : differ name1 name2 f QNAT QNAT
  differ-LT      : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (LT a₁ b₁) (LT a₂ b₂)
  differ-QLT     : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (QLT a₁ b₁) (QLT a₂ b₂)
  differ-NUM     : (x : ℕ) → differ name1 name2 f (NUM x) (NUM x)
  differ-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f d₁ d₂ → differ name1 name2 f (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
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
  --differ-NAME    : differ name1 name2 f (NAME name1) (NAME name2)
  --differ-FRESH   : (a b : Term) → differ name1 name2 f a b → differ name1 name2 f (FRESH a) (FRESH b)
  differ-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
  differ-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → differ name1 name2 f a₁ a₂ → differ name1 name2 f b₁ b₂ → differ name1 name2 f c₁ c₂ → differ name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
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


⇓PresDiff : (f : Term) (name1 name2 : Name) (n : ℕ) → Set(lsuc(L))
⇓PresDiff f name1 name2 n =
  (w1 w2 w1' : 𝕎·) (k : ℕ) (a b : Term)
  → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
  → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
  → differ name1 name2 f a b
  → getT 0 name1 w1 ≡ getT 0 name2 w1'
  → steps n (a , w1) ≡ (NUM k , w2)
  → Σ 𝕎· (λ w2' → steps n (b , w1') ≡ (NUM k , w2') × getT 0 name1 w2 ≡ getT 0 name2 w2')


⇓from-to-refl : (T : Term) (w : 𝕎·) → T ⇓ T from w to w
⇓from-to-refl T w = (0 , refl)


differ-NUM→ : {name1 name2 : Name} {f t : Term} {m : ℕ}
               → differ name1 name2 f (NUM m) t
               → t ≡ NUM m
differ-NUM→ {name1} {name2} {f} {.(NUM m)} {m} (differ-NUM .m) = refl


IFLT-NUM<⇓ : {n m : ℕ} (p : n < m) (a b : Term) (w : 𝕎·) → IFLT (NUM n) (NUM m) a b ⇓ a from w to w
IFLT-NUM<⇓ {n} {m} p a b w = 1 , c
  where
    c : steps 1 (IFLT (NUM n) (NUM m) a b , w) ≡ (a , w)
    c with n <? m
    ... | yes r = refl
    ... | no r = ⊥-elim (r p)


IFLT-NUM¬<⇓ : {n m : ℕ} (p : ¬ n < m) (a b : Term) (w : 𝕎·) → IFLT (NUM n) (NUM m) a b ⇓ b from w to w
IFLT-NUM¬<⇓ {n} {m} p a b w = 1 , c
  where
    c : steps 1 (IFLT (NUM n) (NUM m) a b , w) ≡ (b , w)
    c with n <? m
    ... | yes r = ⊥-elim (p r)
    ... | no r = refl --


IFLT-NUM-2nd⇓steps : (k : ℕ) (n : ℕ) {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
                → steps k (a , w1) ≡ (a' , w2)
                → IFLT (NUM n) a b c ⇓ IFLT (NUM n) a' b c from w1 to w2
IFLT-NUM-2nd⇓steps 0 n {a} {a'} b c {w1} {w2} comp rewrite pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
IFLT-NUM-2nd⇓steps (suc k) n {a} {a'} b c {w1} {w2} comp with step⊎ a w1
... | inj₁ (a'' , w1' , z) rewrite z with is-NUM a
... |    inj₁ (m , q) rewrite q | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) | stepsVal (NUM m) w1 k tt | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _
... |    inj₂ q = step-⇓-from-to-trans s ind
  where
    ind : IFLT (NUM n) a'' b c ⇓ IFLT (NUM n) a' b c from w1' to w2
    ind = IFLT-NUM-2nd⇓steps k n b c comp

    s : step (IFLT (NUM n) a b c) w1 ≡ just (IFLT (NUM n) a'' b c , w1')
    s with is-NUM a
    ... | inj₁ (m , q') = ⊥-elim (q _ q')
    ... | inj₂ q' rewrite z = refl
IFLT-NUM-2nd⇓steps (suc k) n {a} {a'} b c {w1} {w2} comp | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = ⇓from-to-refl _ _


IFLT-NUM-2nd⇓ : (n : ℕ) {a a' : Term} (b c : Term) {w1 w2 : 𝕎·}
                → a ⇓ a' from w1 to w2
                → IFLT (NUM n) a b c ⇓ IFLT (NUM n) a' b c from w1 to w2
IFLT-NUM-2nd⇓ n {a} {a'} b c {w1} {w2} comp = IFLT-NUM-2nd⇓steps (fst comp) n b c (snd comp)


differ⇓-aux2 : (f : Term) (name1 name2 : Name) (w1 w2 w1' : 𝕎·) (a b a' : Term)
               → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
               → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
               → differ name1 name2 f a b
               → getT 0 name1 w1 ≡ getT 0 name2 w1'
               → step a w1 ≡ just (a' , w2)
               → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   a' ⇓ a'' from w2 to w3 × b ⇓ b'' from w1' to w3' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
differ⇓-aux2 f name1 name2 w1 w2 w1' .NAT .NAT a' c₁ c₂ differ-NAT g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NAT , NAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .QNAT .QNAT a' c₁ c₂ differ-QNAT g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QNAT , QNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(LT a₁ b₁) .(LT a₂ b₂) a' c₁ c₂ (differ-LT a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LT a₁ b₁ , LT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(QLT a₁ b₁) .(QLT a₂ b₂) a' c₁ c₂ (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QLT a₁ b₁ , QLT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(NUM x) .(NUM x) a' c₁ c₂ (differ-NUM x) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM x , NUM x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
-- IFLT
differ⇓-aux2 f name1 name2 w1 w2 w1' .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' c₁ c₂ (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s with is-NUM a₁
... | inj₁ (n , p) rewrite p | differ-NUM→ diff with is-NUM b₁
... |    inj₁ (m , q) rewrite q | differ-NUM→ diff₁ with n <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = c₃ , c₄ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM<⇓ r c₄ d₂ w1' , g0
... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = d₁ , d₂ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM¬<⇓ r c₄ d₂ w1' , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' c₁ c₂ (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s | inj₁ (n , p) | inj₂ q with step⊎ b₁ w1
... | inj₁ (b₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  IFLT (NUM n) (fst ind) c₃ d₁ ,
  IFLT (NUM n) (fst (snd ind)) c₄ d₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  IFLT-NUM-2nd⇓ n c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
  IFLT-NUM-2nd⇓ n c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  snd (snd (snd (snd (snd (snd ind)))))
  where
    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            b₁' ⇓ a'' from w1'' to w3 × b₂ ⇓ b'' from w1' to w3' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f name1 name2 w1 w1'' w1' b₁ b₂ b₁' c₁ c₂ diff₁ g0 z
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
differ⇓-aux2 f name1 name2 w1 w2 w1' .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' c₁ c₂ (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s | inj₂ p with step⊎ a₁ w1
... | inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = {!!} -- as above, go by induction
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- PI
differ⇓-aux2 f name1 name2 w1 w2 w1' .(PI a₁ b₁) .(PI a₂ b₂) a' c₁ c₂ (differ-PI a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PI a₁ b₁ , PI a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(LAMBDA a) .(LAMBDA b) a' c₁ c₂ (differ-LAMBDA a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LAMBDA a , LAMBDA b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(APPLY a₁ b₁) .(APPLY a₂ b₂) a' c₁ c₂ (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) g0 s = {!!}
differ⇓-aux2 f name1 name2 w1 w2 w1' .(FIX a) .(FIX b) a' c₁ c₂ (differ-FIX a b diff) g0 s = {!!}
differ⇓-aux2 f name1 name2 w1 w2 w1' .(LET a₁ b₁) .(LET a₂ b₂) a' c₁ c₂ (differ-LET a₁ a₂ b₁ b₂ diff diff₁) g0 s = {!!}
differ⇓-aux2 f name1 name2 w1 w2 w1' .(SUM a₁ b₁) .(SUM a₂ b₂) a' c₁ c₂ (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUM a₁ b₁ , SUM a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(PAIR a₁ b₁) .(PAIR a₂ b₂) a' c₁ c₂ (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) a' c₁ c₂ (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) g0 s = {!!}
differ⇓-aux2 f name1 name2 w1 w2 w1' .(SET a₁ b₁) .(SET a₂ b₂) a' c₁ c₂ (differ-SET a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SET a₁ b₁ , SET a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(TUNION a₁ b₁) .(TUNION a₂ b₂) a' c₁ c₂ (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(UNION a₁ b₁) .(UNION a₂ b₂) a' c₁ c₂ (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNION a₁ b₁ , UNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(QTUNION a₁ b₁) .(QTUNION a₂ b₂) a' c₁ c₂ (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(INL a) .(INL b) a' c₁ c₂ (differ-INL a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INL a , INL b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(INR a) .(INR b) a' c₁ c₂ (differ-INR a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INR a , INR b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(DECIDE a₁ b₁ c₃) .(DECIDE a₂ b₂ c₄) a' c₁ c₂ (differ-DECIDE a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s = {!!}
differ⇓-aux2 f name1 name2 w1 w2 w1' .(EQ a₁ b₁ c₃) .(EQ a₂ b₂ c₄) a' c₁ c₂ (differ-EQ a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQ a₁ b₁ c₃ , EQ a₂ b₂ c₄ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .AX .AX a' c₁ c₂ differ-AX g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = AX , AX , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .FREE .FREE a' c₁ c₂ differ-FREE g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FREE , FREE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) a' c₁ c₂ (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) g0 s = {!!}
differ⇓-aux2 f name1 name2 w1 w2 w1' .(IFC0 a₁ b₁ c₃) .(IFC0 a₂ b₂ c₄) a' c₁ c₂ (differ-IFC0 a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s = {!!}
differ⇓-aux2 f name1 name2 w1 w2 w1' .(TSQUASH a) .(TSQUASH b) a' c₁ c₂ (differ-TSQUASH a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TSQUASH a , TSQUASH b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(TTRUNC a) .(TTRUNC b) a' c₁ c₂ (differ-TTRUNC a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TTRUNC a , TTRUNC b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(TCONST a) .(TCONST b) a' c₁ c₂ (differ-TCONST a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TCONST a , TCONST b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(SUBSING a) .(SUBSING b) a' c₁ c₂ (differ-SUBSING a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUBSING a , SUBSING b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(DUM a) .(DUM b) a' c₁ c₂ (differ-DUM a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = DUM a , DUM b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) a' c₁ c₂ (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(UNIV x) .(UNIV x) a' c₁ c₂ (differ-UNIV x) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNIV x , UNIV x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(LIFT a) .(LIFT b) a' c₁ c₂ (differ-LIFT a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LIFT a , LIFT b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(LOWER a) .(LOWER b) a' c₁ c₂ (differ-LOWER a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LOWER a , LOWER b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(SHRINK a) .(SHRINK b) a' c₁ c₂ (differ-SHRINK a b diff) g0 s rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SHRINK a , SHRINK b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , g0
differ⇓-aux2 f name1 name2 w1 w2 w1' .(upd name1 f) .(upd name2 f) a' c₁ c₂ differ-upd g0 s = {!!}


differ⇓-aux : (f : Term) (name1 name2 : Name) (n : ℕ) (ind : (n' : ℕ) → n' < n → ⇓PresDiff f name1 name2 n') → ⇓PresDiff f name1 name2 n
differ⇓-aux f name1 name2 n ind = {!!}


differ⇓ : (f : Term) (name1 name2 : Name) (n : ℕ) → ⇓PresDiff f name1 name2 n
differ⇓ f name1 name2 = <ℕind _ (differ⇓-aux f name1 name2)


\end{code}

