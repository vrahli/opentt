\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --experimental-lossy-unification #-}


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
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import choiceExt
open import newChoice
open import encode


module terms6 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
              (N : NewChoice W C M G)
              (EC : Encode)
       where

open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import encodeDef(EC)

open import computation(W)(C)(M)(G)(E)(N)(EC)
open import terms2(W)(C)(M)(G)(E)(N)(EC)
open import terms3(W)(C)(M)(G)(E)(N)(EC)
open import terms4(W)(C)(M)(G)(E)(N)(EC)
open import terms5(W)(C)(M)(G)(E)(N)(EC)

open import continuity-conds(W)(C)(M)(G)(E)(N)(EC)



abstract

  differ-refl : (name1 name2 : Name) (f t : Term)
                → ¬names t ≡ true
                → differ name1 name2 f t t
  differ-refl name1 name2 f (VAR x) nn = differ-VAR x
--  differ-refl name1 name2 f NAT nn = differ-NAT
  differ-refl name1 name2 f QNAT nn = differ-QNAT
--  differ-refl name1 name2 f TNAT nn = differ-TNAT
  differ-refl name1 name2 f (LT t t₁) nn = differ-LT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (QLT t t₁) nn = differ-QLT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (NUM x) nn = differ-NUM x
  differ-refl name1 name2 f (IFLT t t₁ t₂ t₃) nn = differ-IFLT _ _ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₃ (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn))
  differ-refl name1 name2 f (IFEQ t t₁ t₂ t₃) nn = differ-IFEQ _ _ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₃ (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn))
  differ-refl name1 name2 f (SUC t) nn = differ-SUC _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (PI t t₁) nn = differ-PI _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (LAMBDA t) nn = differ-LAMBDA _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (APPLY t t₁) nn = differ-APPLY _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (FIX t) nn = differ-FIX _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (LET t t₁) nn = differ-LET _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (WT t t₁) nn = differ-WT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (SUP t t₁) nn = differ-SUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  --differ-refl name1 name2 f (DSUP t t₁) nn = differ-DSUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (WREC t t₁) nn = differ-WREC _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (MT t t₁) nn = differ-MT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  --differ-refl name1 name2 f (MSUP t t₁) nn = differ-MSUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  --differ-refl name1 name2 f (DMSUP t t₁) nn = differ-DMSUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (SUM t t₁) nn = differ-SUM _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (PAIR t t₁) nn = differ-PAIR _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (SPREAD t t₁) nn = differ-SPREAD _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (SET t t₁) nn = differ-SET _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (ISECT t t₁) nn = differ-ISECT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (TUNION t t₁) nn = differ-TUNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (UNION t t₁) nn = differ-UNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
--  differ-refl name1 name2 f (QTUNION t t₁) nn = differ-QTUNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (INL t) nn = differ-INL _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (INR t) nn = differ-INR _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (DECIDE t t₁ t₂) nn = differ-DECIDE _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
  differ-refl name1 name2 f (EQ t t₁ t₂) nn = differ-EQ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
--  differ-refl name1 name2 f (EQB t t₁ t₂ t₃) nn = differ-EQB _ _ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₃ (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn))
  differ-refl name1 name2 f AX nn = differ-AX
  differ-refl name1 name2 f FREE nn = differ-FREE
  differ-refl name1 name2 f (MSEQ x) nn = differ-MSEQ x
  differ-refl name1 name2 f (MAPP s t) nn = differ-MAPP _ _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (CHOOSE t t₁) nn = differ-CHOOSE _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (TSQUASH t) nn = differ-TSQUASH _ _ (differ-refl name1 name2 f t nn)
--  differ-refl name1 name2 f (TTRUNC t) nn = differ-TTRUNC _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f NOWRITE nn = differ-NOWRITE
  differ-refl name1 name2 f NOREAD  nn = differ-NOREAD
  differ-refl name1 name2 f (SUBSING t) nn = differ-SUBSING _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (PURE) nn = differ-PURE
  differ-refl name1 name2 f (NOSEQ) nn = differ-NOSEQ
  differ-refl name1 name2 f (TERM t) nn = differ-TERM _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (ENC t) nn = differ-ENC _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (DUM t) nn = differ-DUM _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (FFDEFS t t₁) nn = differ-FFDEFS _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
  differ-refl name1 name2 f (UNIV x) nn = differ-UNIV x
  differ-refl name1 name2 f (LIFT t) nn = differ-LIFT _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (LOWER t) nn = differ-LOWER _ _ (differ-refl name1 name2 f t nn)
  differ-refl name1 name2 f (SHRINK t) nn = differ-SHRINK _ _ (differ-refl name1 name2 f t nn)


differ-WRECr : {name1 name2 : Name} {f : Term} {r1 r2 f1 f2 : Term} (cf : # f)
               → differ name1 name2 f r1 r2
               → differ name1 name2 f f1 f2
               → differ name1 name2 f (WRECr r1 f1) (WRECr r2 f2)
differ-WRECr {name1} {name2} {f} {r1} {r2} {f1} {f2} cf dr df =
  differ-LAMBDA
    _ _
    (differ-WREC
      _ _ _ _
      (differ-APPLY _ _ _ _ (→differ-shiftUp 0 cf df) (differ-VAR 0))
      (→differ-shiftUp 3 cf dr))


→differ-ID : (name1 name2 : Name) (f : Term)
               → differ name1 name2 f ID ID
→differ-ID name1 name2 f = differ-LAMBDA (VAR 0) (VAR 0) (differ-VAR 0)


→differ-BOT : (name1 name2 : Name) (f : Term)
               → differ name1 name2 f BOT BOT
→differ-BOT name1 name2 f = differ-FIX ID ID (→differ-ID name1 name2 f)


→differ-ENCr : {name1 name2 : Name} {f a : Term}
                → differ name1 name2 f a a
                → differ name1 name2 f (ENCr a) (ENCr a)
→differ-ENCr {name1} {name2} {f} {a} diff =
  differ-IFEQ
    (APPLY a (NUM (encode· (ENC a))))
    (APPLY a (NUM (encode· (ENC a))))
    N0 N0 BOT BOT N0 N0
    (differ-APPLY a a (NUM (encode· (ENC a))) (NUM (encode· (ENC a))) diff (differ-NUM _))
    (differ-NUM _)
    (→differ-BOT name1 name2 f)
    (differ-NUM _)


abstract

  differ⇓-aux2 : (gc0 : get-choose-ℕ)
                 (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name) (w1 w2 w1' w0 : 𝕎·) (a b a' v : Term) (k : ℕ)
                 → compatible· name1 w1 Res⊤
                 → compatible· name2 w1' Res⊤
                 → ∀𝕎-get0-NUM w1 name1
  --               → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
  --               → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
                   → differ name1 name2 f a b
                   → getT 0 name1 w1 ≡ getT 0 name2 w1'
                   → step a w1 ≡ just (a' , w2)
                   → steps k (a' , w2) ≡ (v , w0)
                   → isValue v
                   → ((k' : ℕ) → k' < k → ⇓PresDiff f name1 name2 k')
                   → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       a' ⇓ a'' from w2 to w3
                       × b ⇓ b'' from w1' to w3'
                       × differ name1 name2 f a'' b''
                       × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
--  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .NAT .NAT a' v k compat1 compat2 agtn differ-NAT g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NAT , NAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NAT , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .QNAT .QNAT a' v k compat1 compat2 agtn differ-QNAT g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QNAT , QNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QNAT , g0
--  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .TNAT .TNAT a' v k compat1 compat2 agtn differ-TNAT g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TNAT , TNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TNAT , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(LT a₁ b₁) .(LT a₂ b₂) a' v k compat1 compat2 agtn (differ-LT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LT a₁ b₁ , LT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LT _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(QLT a₁ b₁) .(QLT a₂ b₂) a' v k compat1 compat2 agtn (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QLT a₁ b₁ , QLT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QLT _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(NUM x) .(NUM x) a' v k compat1 compat2 agtn (differ-NUM x) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM x , NUM x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NUM x , g0
  -- IFLT
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' v k compat1 compat2 agtn (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p) rewrite p | differ-NUM→ diff with is-NUM b₁
  ... |    inj₁ (m , q) rewrite q | differ-NUM→ diff₁ with n <? m
  ... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = c₃ , c₄ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM<⇓ r c₄ d₂ w1' , diff₂ , g0
  ... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = d₁ , d₂ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM¬<⇓ r c₄ d₂ w1' , diff₃ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' v k compat1 compat2 agtn (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd | inj₁ (n , p) | inj₂ q with step⊎ b₁ w1
  ... | inj₁ (b₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFLT (NUM n) (fst ind) c₃ d₁ ,
    IFLT (NUM n) (fst (snd ind)) c₄ d₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    IFLT-NUM-2nd⇓ n c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
    IFLT-NUM-2nd⇓ n c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-IFLT _ _ _ _ _ _ _ _ (differ-NUM n) (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₂ diff₃ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k b₁' w1''
      hv0 = IFLT-NUM→hasValue k n b₁' c₃ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              b₁' ⇓ a'' from w1'' to w3 × b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) b₁ b₂ b₁' (fst hv0) k compat1 compat2 agtn diff₁ g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFLT-NUM→ n b₁' c₃ d₁ w1'' {k} hv) pd
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' v k compat1 compat2 agtn (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd | inj₂ p with step⊎ a₁ w1
  ... | inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFLT (fst ind) b₁ c₃ d₁ ,
    IFLT (fst (snd ind)) b₂ c₄ d₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    IFLT-NUM-1st⇓ b₁ c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
    IFLT-NUM-1st⇓ b₂ c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-IFLT _ _ _ _ _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ diff₂ diff₃ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = IFLT→hasValue k a₁' b₁ c₃ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFLT→ a₁' b₁ c₃ d₁ w1'' {k} hv) pd
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- IFEQ
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(IFEQ a₁ b₁ c₃ d₁) .(IFEQ a₂ b₂ c₄ d₂) a' v k compat1 compat2 agtn (differ-IFEQ a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p) rewrite p | differ-NUM→ diff with is-NUM b₁
  ... |    inj₁ (m , q) rewrite q | differ-NUM→ diff₁ with n ≟ m
  ... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = c₃ , c₄ , w1 , w1' , ⇓from-to-refl _ _ , IFEQ-NUM=⇓ r c₄ d₂ w1' , diff₂ , g0
  ... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = d₁ , d₂ , w1 , w1' , ⇓from-to-refl _ _ , IFEQ-NUM¬=⇓ r c₄ d₂ w1' , diff₃ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(IFEQ a₁ b₁ c₃ d₁) .(IFEQ a₂ b₂ c₄ d₂) a' v k compat1 compat2 agtn (differ-IFEQ a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd | inj₁ (n , p) | inj₂ q with step⊎ b₁ w1
  ... | inj₁ (b₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFEQ (NUM n) (fst ind) c₃ d₁ ,
    IFEQ (NUM n) (fst (snd ind)) c₄ d₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    IFEQ-NUM-2nd⇓ n c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
    IFEQ-NUM-2nd⇓ n c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-IFEQ _ _ _ _ _ _ _ _ (differ-NUM n) (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₂ diff₃ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k b₁' w1''
      hv0 = IFEQ-NUM→hasValue k n b₁' c₃ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              b₁' ⇓ a'' from w1'' to w3 × b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) b₁ b₂ b₁' (fst hv0) k compat1 compat2 agtn diff₁ g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFEQ-NUM→ n b₁' c₃ d₁ w1'' {k} hv) pd
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(IFEQ a₁ b₁ c₃ d₁) .(IFEQ a₂ b₂ c₄ d₂) a' v k compat1 compat2 agtn (differ-IFEQ a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd | inj₂ p with step⊎ a₁ w1
  ... | inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFEQ (fst ind) b₁ c₃ d₁ ,
    IFEQ (fst (snd ind)) b₂ c₄ d₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    IFEQ-NUM-1st⇓ b₁ c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
    IFEQ-NUM-1st⇓ b₂ c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-IFEQ _ _ _ _ _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ diff₂ diff₃ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = IFEQ→hasValue k a₁' b₁ c₃ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFEQ→ a₁' b₁ c₃ d₁ w1'' {k} hv) pd
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- SUC
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(SUC a₁) .(SUC a₂) a' v k compat1 compat2 agtn (differ-SUC a₁ a₂ diff) g0 s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p) rewrite p | differ-NUM→ diff | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM (suc n) , NUM (suc n) , w1 , w1' , (0 , refl) , (1 , refl) , differ-NUM (suc n) , g0
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    SUC (fst ind) ,
    SUC (fst (snd ind)) ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    SUC⇓ (fst (snd (snd (snd (snd ind))))) ,
    SUC⇓ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-SUC _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = SUC→hasValue k a₁' v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- PI
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(PI a₁ b₁) .(PI a₂ b₂) a' v k compat1 compat2 agtn (differ-PI a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PI a₁ b₁ , PI a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PI _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(LAMBDA a) .(LAMBDA b) a' v k compat1 compat2 agtn (differ-LAMBDA a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LAMBDA a , LAMBDA b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LAMBDA _ _ diff , g0
  -- APPLY
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(APPLY a₁ b₁) .(APPLY a₂ b₂) a' v k compat1 compat2 agtn (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-LAM a₁
  ... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d
    where
      d : Σ Term (λ g' → a₂ ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × a₂ ≡ upd name2 f)
      d = differ-LAMBDAₗ→ diff

      concl : Σ Term (λ g' → a₂ ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × a₂ ≡ upd name2 f)
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub b₁ t ⇓ a'' from w1 to w3 × APPLY a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (inj₁ (g' , e₁ , e₂)) rewrite e₁ =
        sub b₁ t ,
        sub b₂ g' ,
        w1 , w1' ,
        ⇓from-to-refl _ _ , APPLY-LAMBDA⇓ w1' g' b₂ ,
        differ-sub cf e₂ diff₁ ,
        g0
      concl (inj₂ (e₁ , e₂)) rewrite e₁ | e₂ | sub-upd name1 f b₁ cf =
        v , v , w0 , fst hv2 , (k , hv1) , fst (snd hv2) , differ-refl name1 name2 f v (snd (snd (snd hv2))) , fst (snd (snd hv2))
        where
          hv0 : steps k (sub b₁ (updBody name1 f) , w1) ≡ (v , w0)
          hv0 rewrite e₁ = hv

          hv1 : steps k (LET b₁ (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w0)
          hv1 rewrite sym (sub-upd name1 f b₁ cf) = hv0

          hv2 : Σ 𝕎· (λ w2' → APPLY (upd name2 f) b₂ ⇓ v from w1' to w2' × getT 0 name1 w0 ≡ getT 0 name2 w2' × ¬Names v)
          hv2 = upd⇓names gc0 k f name1 name2 w1 w1' w0 b₁ b₂ v cf nnf agtn compat1 compat2 isvv pd g0 diff₁ hv1
  ... | inj₂ x with is-CS a₁
  ... |    inj₁ (name , p) rewrite p = ⊥-elim (differ-CSₗ→ diff) {-- | differ-CSₗ→ diff with is-NUM b₁
  ... |       inj₁ (n₁ , q) rewrite q | differ-NUM→ diff₁ | map-getT-just→ n₁ name w1 a' w2 s = a' , a' , w1 , w1' , (0 , refl) , (1 , step-APPLY-CS a' w1' n₁ name {!!}) , {!!} , g0
  -- | map-getT-just→ n₁ name w1 a' w2 s = a' , a' , w1 , w1' , (0 , refl) , {!(1 , step-APPLY-CS a' w1' n₁) , ?!} --⊥-elim (differ-CSₗ→ diff)
  ... |       inj₂ q = {!!}--}
  --
  {-- | fst (differ-CSₗ→ diff) | snd (differ-CSₗ→ diff) with is-NUM b₁
  ... |       inj₁ (n₁ , q) rewrite q | differ-NUM→ diff₁ | map-getT-just→ n₁ name1 w1 a' w2 s = a' , a' , w1 , w1' , (0 , refl) , {!(1 , step-APPLY-CS a' w1' n₁) , ?!} --⊥-elim (differ-CSₗ→ diff)
  ... |       inj₂ q = {!!} --}
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(APPLY a₁ b₁) .(APPLY a₂ b₂) a' v k compat1 compat2 agtn (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd | inj₂ x | inj₂ name with is-MSEQ a₁
  ... | inj₁ (sq , r) rewrite r | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) | differ-MSEQ→ diff =
    MAPP sq b₁ , MAPP sq b₂ , w1 , w1' , (0 , refl) , (1 , refl) , differ-MAPP sq b₁ b₂ diff₁ , g0
  ... | inj₂ r with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    APPLY (fst ind) b₁ ,
    APPLY (fst (snd ind)) b₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    APPLY⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    APPLY⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-APPLY _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = APPLY→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-APPLY→ a₁' b₁ w1'' {k} hv) pd
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- FIX
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(FIX a) .(FIX b) a' v k compat1 compat2 agtn (differ-FIX a b diff) g0 s hv isvv pd with is-LAM a
  ... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d --ret (sub (FIX (LAMBDA t)) t) w
    where
      d : Σ Term (λ g' → b ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × b ≡ upd name2 f)
      d = differ-LAMBDAₗ→ diff

      concl : Σ Term (λ g' → b ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × b ≡ upd name2 f)
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub (FIX (LAMBDA t)) t ⇓ a'' from w1 to w3 × FIX b ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (inj₁ (g' , e₁ , e₂)) rewrite e₁ =
        sub (FIX (LAMBDA t)) t ,
        sub (FIX (LAMBDA g')) g' ,
        w1 , w1' ,
        ⇓from-to-refl _ _ ,
        FIX-LAMBDA⇓ w1' g' ,
        differ-sub cf e₂ (differ-FIX _ _ (differ-LAMBDA _ _ e₂)) ,
        g0
      concl (inj₂ (e₁ , e₂)) rewrite e₁ | e₂ | sub-upd name1 f (FIX (upd name1 f)) cf =
        v , v , w0 , fst hv2 , (k , hv1) , (⇓-trans₂ (FIX-LAMBDA⇓ w1' (updBody name2 f)) cs) , differ-refl name1 name2 f v (snd (snd (snd hv2))) , fst (snd (snd hv2))
  --  (fst (snd hv2))
           where
           hv0 : steps k (sub (FIX (upd name1 f)) (updBody name1 f) , w1) ≡ (v , w0)
           hv0 rewrite e₁ = hv

           hv1 : steps k (LET (FIX (upd name1 f)) (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w0)
           hv1 rewrite sym (sub-upd name1 f (FIX (upd name1 f)) cf) = hv0

           df : differ name1 name2 f (FIX (upd name1 f)) (FIX (upd name2 f))
           df = differ-FIX _ _ differ-upd

           hv2 : Σ 𝕎· (λ w2' → APPLY (upd name2 f) (FIX (upd name2 f)) ⇓ v from w1' to w2' × getT 0 name1 w0 ≡ getT 0 name2 w2' × ¬Names v)
           hv2 = upd⇓names gc0 k f name1 name2 w1 w1' w0 (FIX (upd name1 f)) (FIX (upd name2 f)) v cf nnf agtn compat1 compat2 isvv pd g0 df hv1

           cs : sub (FIX (upd name2 f)) (updBody name2 f) ⇓ v from w1' to (fst hv2)
           cs = APPLY-LAMBDA⇓→ (fst (fst (snd hv2))) isvv (snd (fst (snd hv2)))
  ... | inj₂ x with step⊎ a w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    FIX (fst ind) ,
    FIX (fst (snd ind)) ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    FIX⇓ (fst (snd (snd (snd (snd ind))))) ,
    FIX⇓ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-FIX _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = FIX→hasValue k a₁' v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × b ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a b a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-FIX→ a₁' w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- LET
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(LET a₁ b₁) .(LET a₂ b₂) a' v k compat1 compat2 agtn (differ-LET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with isValue⊎ a₁
  ... | inj₁ x rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    sub a₁ b₁ , sub a₂ b₂ , w1 , w1' ,
    ⇓from-to-refl _ _ , LET-val⇓ w1' a₂ b₂ isv , differ-sub cf diff₁ diff , g0
    where
      isv : isValue a₂
      isv = differ-isValue→ diff x
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    LET (fst ind) b₁ ,
    LET (fst (snd ind)) b₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    LET⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    LET⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-LET _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = LET→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-LET→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- WT
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(WT a₁ b₁) .(WT a₂ b₂) a' v k compat1 compat2 agtn (differ-WT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = WT a₁ b₁ , WT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-WT _ _ _ _ diff diff₁ , g0
  -- SUP
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(SUP a₁ b₁) .(SUP a₂ b₂) a' v k compat1 compat2 agtn (differ-SUP a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUP a₁ b₁ , SUP a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUP _ _ _ _ diff diff₁ , g0
  -- DSUP
  {--differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(DSUP a₁ b₁) .(DSUP a₂ b₂) a' v k compat1 compat2 agtn (differ-DSUP a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-SUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ SUP u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
      d = differ-SUPₗ→ diff

      concl : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ SUP u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u₂ (sub u₁ b₁) ⇓ a'' from w1 to w3 × DSUP a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (u' , v' , e , d1 , d2) rewrite e =
        sub u₂ (sub u₁ b₁) , sub v' (sub u' b₂) , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DSUP-SUP⇓ w1' u' v' b₂ ,
        differ-sub cf (differ-sub cf diff₁ d1) d2 ,
        g0
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    DSUP (fst ind) b₁ ,
    DSUP (fst (snd ind)) b₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    DSUP⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    DSUP⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-DSUP _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = DSUP→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
  -- WREC
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(WREC a₁ b₁) .(WREC a₂ b₂) a' v k compat1 compat2 agtn (differ-WREC a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-SUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ SUP u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
      d = differ-SUPₗ→ diff

      concl : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ SUP u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub (WRECr b₁ u₂) (sub u₂ (sub u₁ b₁)) ⇓ a'' from w1 to w3 × WREC a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (u' , v' , e , d1 , d2) rewrite e =
        sub (WRECr b₁ u₂) (sub u₂ (sub u₁ b₁)) , sub (WRECr b₂ v') (sub v' (sub u' b₂)) , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        WREC-SUP⇓ w1' u' v' b₂ ,
        differ-sub cf (differ-sub cf (differ-sub cf diff₁ d1) d2) (differ-WRECr cf diff₁ d2) ,
        g0
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    WREC (fst ind) b₁ ,
    WREC (fst (snd ind)) b₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    WREC⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    WREC⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-WREC _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = WREC→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- MT
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(MT a₁ b₁) .(MT a₂ b₂) a' v k compat1 compat2 agtn (differ-MT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = MT a₁ b₁ , MT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-MT _ _ _ _ diff diff₁ , g0
  -- MSUP
  --differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(MSUP a₁ b₁) .(MSUP a₂ b₂) a' v k compat1 compat2 agtn (differ-MSUP a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = MSUP a₁ b₁ , MSUP a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-MSUP _ _ _ _ diff diff₁ , g0
  -- DMSUP
  {--differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(DMSUP a₁ b₁) .(DMSUP a₂ b₂) a' v k compat1 compat2 agtn (differ-DMSUP a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-MSUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ MSUP u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
      d = differ-MSUPₗ→ diff

      concl : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ MSUP u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u₂ (sub u₁ b₁) ⇓ a'' from w1 to w3 × DMSUP a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (u' , v' , e , d1 , d2) rewrite e =
        sub u₂ (sub u₁ b₁) , sub v' (sub u' b₂) , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DMSUP-MSUP⇓ w1' u' v' b₂ ,
        differ-sub cf (differ-sub cf diff₁ d1) d2 ,
        g0
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    DMSUP (fst ind) b₁ ,
    DMSUP (fst (snd ind)) b₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    DMSUP⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    DMSUP⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-DMSUP _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = DMSUP→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
  -- SUM
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(SUM a₁ b₁) .(SUM a₂ b₂) a' v k compat1 compat2 agtn (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUM a₁ b₁ , SUM a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUM _ _ _ _ diff diff₁ , g0
  -- PAIR
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(PAIR a₁ b₁) .(PAIR a₂ b₂) a' v k compat1 compat2 agtn (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PAIR _ _ _ _ diff diff₁ , g0
  -- SPREAD
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) a' v k compat1 compat2 agtn (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-PAIR a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ PAIR u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
      d = differ-PAIRₗ→ diff

      concl : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ PAIR u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u₂ (sub u₁ b₁) ⇓ a'' from w1 to w3 × SPREAD a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (u' , v' , e , d1 , d2) rewrite e =
        sub u₂ (sub u₁ b₁) , sub v' (sub u' b₂) , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        SPREAD-PAIR⇓ w1' u' v' b₂ ,
        differ-sub cf (differ-sub cf diff₁ d1) d2 ,
        g0
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    SPREAD (fst ind) b₁ ,
    SPREAD (fst (snd ind)) b₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    SPREAD⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    SPREAD⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-SPREAD _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = SPREAD→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- SET
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(SET a₁ b₁) .(SET a₂ b₂) a' v k compat1 compat2 agtn (differ-SET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SET a₁ b₁ , SET a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SET _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(ISECT a₁ b₁) .(ISECT a₂ b₂) a' v k compat1 compat2 agtn (differ-ISECT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-ISECT _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(TUNION a₁ b₁) .(TUNION a₂ b₂) a' v k compat1 compat2 agtn (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TUNION _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(UNION a₁ b₁) .(UNION a₂ b₂) a' v k compat1 compat2 agtn (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNION a₁ b₁ , UNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNION _ _ _ _ diff diff₁ , g0
--  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(QTUNION a₁ b₁) .(QTUNION a₂ b₂) a' v k compat1 compat2 agtn (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QTUNION _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(INL a) .(INL b) a' v k compat1 compat2 agtn (differ-INL a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INL a , INL b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INL _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(INR a) .(INR b) a' v k compat1 compat2 agtn (differ-INR a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INR a , INR b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INR _ _ diff , g0
  -- DECIDE
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(DECIDE a₁ b₁ c₃) .(DECIDE a₂ b₂ c₄) a' v k compat1 compat2 agtn (differ-DECIDE a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv isvv pd with is-INL a₁
  ... | inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : Σ Term (λ u' → a₂ ≡ INL u' × differ name1 name2 f u u')
      d = differ-INLₗ→ diff

      concl : Σ Term (λ u' → a₂ ≡ INL u' × differ name1 name2 f u u')
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u b₁ ⇓ a'' from w1 to w3 × DECIDE a₂ b₂ c₄ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (u' , e , d1) rewrite e =
        sub u b₁ , sub u' b₂ , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DECIDE-INL⇓ w1' u' _ _ ,
        differ-sub cf diff₁ d1 ,
        g0
  ... | inj₂ x with is-INR a₁
  ... |    inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : Σ Term (λ u' → a₂ ≡ INR u' × differ name1 name2 f u u')
      d = differ-INRₗ→ diff

      concl : Σ Term (λ u' → a₂ ≡ INR u' × differ name1 name2 f u u')
              → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u c₃ ⇓ a'' from w1 to w3 × DECIDE a₂ b₂ c₄ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      concl (u' , e , d1) rewrite e =
        sub u c₃ , sub u' c₄ , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DECIDE-INR⇓ w1' u' _ _ ,
        differ-sub cf diff₂ d1 ,
        g0
  ... |    inj₂ y with step⊎ a₁ w1
  ... |       inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    DECIDE (fst ind) b₁ c₃ ,
    DECIDE (fst (snd ind)) b₂ c₄ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    DECIDE⇓ b₁ c₃ (fst (snd (snd (snd (snd ind))))) ,
    DECIDE⇓ b₂ c₄ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-DECIDE _ _ _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ diff₂ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = DECIDE→hasValue k a₁' b₁ c₃ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-DECIDE→ a₁' b₁ c₃ w1'' {k} hv) pd
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- EQ
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(EQ a₁ b₁ c₃) .(EQ a₂ b₂ c₄) a' v k compat1 compat2 agtn (differ-EQ a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQ a₁ b₁ c₃ , EQ a₂ b₂ c₄ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-EQ _ _ _ _ _ _ diff diff₁ diff₂ , g0
--  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(EQB a₁ b₁ c₃ d₁) .(EQB a₂ b₂ c₄ d₂) a' v k compat1 compat2 agtn (differ-EQB a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQB a₁ b₁ c₃ d₁ , EQB a₂ b₂ c₄ d₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-EQB _ _ _ _ _ _ _ _ diff diff₁ diff₂ diff₃ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .AX .AX a' v k compat1 compat2 agtn differ-AX g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = AX , AX , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-AX , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .FREE .FREE a' v k compat1 compat2 agtn differ-FREE g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FREE , FREE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FREE , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(MSEQ x) .(MSEQ x) a' v k compat1 compat2 agtn (differ-MSEQ x) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = MSEQ x , MSEQ x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-MSEQ x , g0
  -- MAPP
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(MAPP x a₁) .(MAPP x a₂) a' v k compat1 compat2 agtn (differ-MAPP x a₁ a₂ diff) g0 s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p)
    rewrite p
            | sym (pair-inj₁ (just-inj s))
            | sym (pair-inj₂ (just-inj s))
            | differ-NUM→ diff
            | stepsVal (NUM (x n)) w1 k tt
            | sym (pair-inj₁ hv)
            | sym (pair-inj₂ hv) =
    NUM (x n) , NUM (x n) , w1 , w1' , (0 , refl) , (1 , refl) , differ-NUM (x n) , g0
  ... | inj₂ y with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    MAPP x (fst ind) ,
    MAPP x (fst (snd ind)) ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    MAPP⇓ x (fst (snd (snd (snd (snd ind))))) ,
    MAPP⇓ x (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-MAPP _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = MAPP→hasValue k x a₁' v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-APPLY→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  --differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(CS name1) .(CS name2) a' v k compat1 compat2 agtn differ-CS g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = CS name1 , CS name2 , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-CS , g0
  -- CHOOSE
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) a' v k compat1 compat2 agtn (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-NAME a₁
  ... | inj₁ (name , p) rewrite p = ⊥-elim (differ-NAMEₗ→ diff)
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    CHOOSE (fst ind) b₁ ,
    CHOOSE (fst (snd ind)) b₂ ,
    fst (snd (snd ind)) ,
    fst (snd (snd (snd ind))) ,
    CHOOSE⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    CHOOSE⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
    differ-CHOOSE _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
    snd (snd (snd (snd (snd (snd (snd ind))))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = CHOOSE→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
      ind = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-CHOOSE→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  -- IFC0
  --differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(IFC0 a₁ b₁ c₃) .(IFC0 a₂ b₂ c₄) a' v k compat1 compat2 agtn (differ-IFC0 a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv isvv pd = {!!}
  -- TSQUASH
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(TSQUASH a) .(TSQUASH b) a' v k compat1 compat2 agtn (differ-TSQUASH a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TSQUASH a , TSQUASH b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TSQUASH _ _ diff , g0
--  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(TTRUNC a) .(TTRUNC b) a' v k compat1 compat2 agtn (differ-TTRUNC a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TTRUNC a , TTRUNC b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TTRUNC _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(NOWRITE) .(NOWRITE) a' v k compat1 compat2 agtn differ-NOWRITE g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NOWRITE , NOWRITE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NOWRITE , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(NOREAD) .(NOREAD) a' v k compat1 compat2 agtn differ-NOREAD g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NOREAD , NOREAD , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NOREAD , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(SUBSING a) .(SUBSING b) a' v k compat1 compat2 agtn (differ-SUBSING a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUBSING a , SUBSING b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUBSING _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(PURE) .(PURE) a' v k compat1 compat2 agtn (differ-PURE) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PURE , PURE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PURE , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(NOSEQ) .(NOSEQ) a' v k compat1 compat2 agtn (differ-NOSEQ) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NOSEQ , NOSEQ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NOSEQ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(TERM a) .(TERM b) a' v k compat1 compat2 agtn (differ-TERM a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TERM a , TERM b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TERM _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(ENC a) .(ENC a) a' v k compat1 compat2 agtn (differ-ENC a diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    ENCr a , ENCr a , w1 , w1' , ⇓from-to-refl _ _ , (1 , refl) , →differ-ENCr diff , g0
  --NUM (Term→ℕ a) , {!!} --ENC a , ENC b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-ENC _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(DUM a) .(DUM b) a' v k compat1 compat2 agtn (differ-DUM a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = DUM a , DUM b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-DUM _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) a' v k compat1 compat2 agtn (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FFDEFS _ _ _ _ diff diff₁ , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(UNIV x) .(UNIV x) a' v k compat1 compat2 agtn (differ-UNIV x) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNIV x , UNIV x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNIV x , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(LIFT a) .(LIFT b) a' v k compat1 compat2 agtn (differ-LIFT a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LIFT a , LIFT b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LIFT _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(LOWER a) .(LOWER b) a' v k compat1 compat2 agtn (differ-LOWER a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LOWER a , LOWER b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LOWER _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(SHRINK a) .(SHRINK b) a' v k compat1 compat2 agtn (differ-SHRINK a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SHRINK a , SHRINK b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SHRINK _ _ diff , g0
  differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w2 w1' w0 .(upd name1 f) .(upd name2 f) a' v k compat1 compat2 agtn differ-upd g0 s hv isvv pd
    rewrite stepVal (upd name1 f) w1 tt | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    upd name1 f , upd name2 f , w1 , w1' , (0 , refl) , (0 , refl) , differ-upd , g0


steps-val-suc : (k : ℕ) (a v : Term) (w1 w2 : 𝕎·)
                → isValue v
                → steps k (a , w1) ≡ (v , w2)
                → steps (suc k) (a , w1) ≡ (v , w2)
steps-val-suc 0 a v w1 w2 isv s
  rewrite sym (pair-inj₁ s)
        | sym (pair-inj₂ s) = stepsVal a w1 1 isv
steps-val-suc (suc k) a v w1 w2 isv s with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z = steps-val-suc k a' v w1' w2 isv s
... | inj₂ z rewrite z = s


steps⇓-decomp : (k k' : ℕ) (a b v : Term) (w1 w2 w3 : 𝕎·)
                → steps k (a , w1) ≡ (v , w2)
                → steps k' (a , w1) ≡ (b , w3)
                → isValue v
                → steps k (b , w3) ≡ (v , w2)
steps⇓-decomp 0 k' a b v w1 w2 w3 s comp isv
  rewrite sym (pair-inj₁ s)
        | sym (pair-inj₂ s)
        | stepsVal a w1 k' isv
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = refl
steps⇓-decomp (suc k) 0 a b v w1 w2 w3 s comp isv
  rewrite sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = s
steps⇓-decomp (suc k) (suc k') a b v w1 w2 w3 s comp isv with step⊎ a w1
... | inj₁ (a' , w1' , z)
  rewrite z = steps-val-suc k b v w3 w2 isv c
  where
    c : steps k (b , w3) ≡ (v , w2)
    c = steps⇓-decomp k k' a' b v w1' w2 w3 s comp isv
... | inj₂ z
  rewrite z
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp)
        | sym (pair-inj₁ s)
        | sym (pair-inj₂ s) = stepsVal a w1 (suc k) isv



⇓→⊑ : (a b : Term) {w w' : 𝕎·} → a ⇓ b from w to w' → w ⊑· w'
⇓→⊑ a b {w} {w'} (n , comp) = steps→⊑ n a b comp


step→⇓ : {a b : Term} {w1 w2 : 𝕎·}
              → step a w1 ≡ just (b , w2)
              → a ⇓ b from w1 to w2
step→⇓ {a} {b} {w1} {w2} comp = 1 , c
  where
    c : steps 1 (a , w1) ≡ (b , w2)
    c rewrite comp = refl


differ⇓-aux : (gc0 : get-choose-ℕ) (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name) (n : ℕ)
              (ind : (n' : ℕ) → n' < n → ⇓PresDiff f name1 name2 n')
              → ⇓PresDiff f name1 name2 n
differ⇓-aux gc0 f cf nnf name1 name2 0 ind w1 w2 w1' a b v isv compat1 compat2 gt0 diff g0 comp rewrite pair-inj₁ comp | pair-inj₂ comp =
  w1' , b , (0 , refl) , diff , g0
differ⇓-aux gc0 f cf nnf name1 name2 (suc n) ind w1 w2 w1' a b v isv compat1 compat2 gt0 diff g0 comp with step⊎ a w1
... | inj₁ (a' , w1'' , z) rewrite z =
  fst e , fst (snd e) , (⇓-trans₂ (fst (snd (snd (snd (snd (snd c)))))) (fst (snd (snd e)))) ,
  fst (snd (snd (snd e))) , snd (snd (snd (snd e)))
  where
    c : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   a' ⇓ a'' from w1'' to w3
                   × b ⇓ b'' from w1' to w3'
                   × differ name1 name2 f a'' b''
                   × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    c = differ⇓-aux2 gc0 f cf nnf name1 name2 w1 w1'' w1' w2 a b a' v n compat1 compat2 gt0 diff g0 z comp isv λ k i → ind k (<-trans i (n<1+n n))

    d : steps n (fst c , fst (snd (snd c))) ≡ (v , w2)
    d = steps⇓-decomp
          n (proj₁ (proj₁ (snd (snd (snd (snd c)))))) a'
          (proj₁ c) v w1'' w2 (proj₁ (snd (snd c))) comp
          (snd (fst (snd (snd (snd (snd c)))))) isv

    e₁ : w1 ⊑· fst (snd (snd c))
    e₁ = ⇓→⊑ a (fst c) (step-⇓-from-to-trans z (fst (snd (snd (snd (snd c))))))

    e₂ : w1' ⊑· fst (snd (snd (snd c)))
    e₂ = ⇓→⊑ b (fst (snd c)) (fst (snd (snd (snd (snd (snd c))))))

    e : Σ 𝕎· (λ w2' → Σ Term (λ v' →
          fst (snd c) ⇓ v' from fst (snd (snd (snd c))) to w2' × differ name1 name2 f v v' × getT 0 name1 w2 ≡ getT 0 name2 w2'))
    e = ind n ≤-refl (fst (snd (snd c))) w2 (fst (snd (snd (snd c)))) (fst c) (fst (snd c)) v isv
            (⊑-compatible· e₁ compat1) (⊑-compatible· e₂ compat2)
            (∀𝕎-mon (⇓→⊑ a (proj₁ c) {w1} {proj₁ (snd (snd c))} (⇓-trans₂ (step→⇓ z) (fst (snd (snd (snd (snd c))))))) gt0) (fst (snd (snd (snd (snd (snd (snd c))))))) (snd (snd (snd (snd (snd (snd (snd c))))))) d
... | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = w1' , b , (0 , refl) , diff , g0


differ⇓ : (gc0 : get-choose-ℕ) (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name) (n : ℕ)
          → ⇓PresDiff f name1 name2 n
differ⇓ gc0 f cf nnf name1 name2 = <ℕind _ (differ⇓-aux gc0 f cf nnf name1 name2)



sub-SEQ : (a b c : Term) → # a → #[ [ 0 ] ] c → sub a (SEQ b c) ≡ SEQ (sub a b) (sub a c)
sub-SEQ a b c ca cc
  rewrite #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | #shiftDown 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftUp 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
  = →≡LET refl refl


→sub-SEQ : {a b c b' c' : Term} → # a → #[ [ 0 ] ] c
            → sub a b ≡ b'
            → sub a c ≡ c'
            → sub a (SEQ b c) ≡ SEQ b' c'
→sub-SEQ {a} {b} {c} {b'} {c'} ca cc eb ec rewrite sym eb | sym ec = sub-SEQ a b c ca cc


sub-ITE : (a b c d : Term) → # a → #[ [ 0 ] ] c → #[ [ 0 ] ] d
          → sub a (ITE b c d) ≡ ITE (sub a b) (sub a c) (sub a d)
sub-ITE a b c d ca cc cd
  rewrite #shiftUp 0 (ct a ca) | #shiftUp 0 (ct a ca)
        | shiftDown1-subv1-shiftUp0 0 a c ca
        | shiftDown1-subv1-shiftUp0 0 a d ca
        | #shiftDown 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftUp 0 (ct (subv 0 a c) (#subv-CTerm (ct a ca) (ct0 c cc)))
        | #shiftDown 0 (ct (subv 0 a d) (#subv-CTerm (ct a ca) (ct0 d cd)))
        | #shiftUp 0 (ct (subv 0 a d) (#subv-CTerm (ct a ca) (ct0 d cd)))
  = refl


sub-IF-THEN : (a b c : Term) → # a → #[ [ 0 ] ] c
              → sub a (IF-THEN b c) ≡ IF-THEN (sub a b) (sub a c)
sub-IF-THEN a b c ca cc = sub-ITE a b c AX ca cc refl


→sub-IF-THEN : {a b c b' c' : Term} → # a → #[ [ 0 ] ] c
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a (IF-THEN b c) ≡ IF-THEN b' c'
→sub-IF-THEN {a} {b} {c} {b'} {c'} ca cc eb ec rewrite sym eb | sym ec = sub-IF-THEN a b c ca cc




sub-IFLE : (a b c d e : Term)
           → sub a (IFLE b c d e) ≡ IFLE (sub a b) (sub a c) (sub a d) (sub a e)
sub-IFLE a b c d e = refl


→sub-IFLE : {a b c d e b' c' d' e' : Term}
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a d ≡ d'
                → sub a e ≡ e'
                → sub a (IFLE b c d e) ≡ IFLE b' c' d' e'
→sub-IFLE {a} {b} {c} {d} {e} {b'} {c'} {d'} {e'} eb ec ed ee
  rewrite sym eb | sym ec | sym ed | sym ee =
  refl


sub-LE : (a b c : Term) → sub a (LE b c) ≡ LE (sub a b) (sub a c)
sub-LE a b c = refl


→sub-LE : {a b c b' c' : Term}
           → sub a b ≡ b'
           → sub a c ≡ c'
           → sub a (LE b c) ≡ LE b' c'
→sub-LE {a} {b} {c} {b'} {c'} eb ec rewrite sym eb | sym ec = sub-LE a b c


→sub-APPLY : {a b c b' c' : Term}
           → sub a b ≡ b'
           → sub a c ≡ c'
           → sub a (APPLY b c) ≡ APPLY b' c'
→sub-APPLY {a} {b} {c} {b'} {c'} eb ec rewrite sym eb | sym ec = sub-APPLY a b c


{--
sub-IFC0 : (a b c d : Term)
           → sub a (IFC0 b c d) ≡ IFC0 (sub a b) (sub a c) (sub a d)
sub-IFC0 a b c d = refl
--}


{--
→sub-IFC0 : {a b c d b' c' d' : Term}
                → sub a b ≡ b'
                → sub a c ≡ c'
                → sub a d ≡ d'
                → sub a (IFC0 b c d) ≡ IFC0 b' c' d'
→sub-IFC0 {a} {b} {c} {d} {b'} {c'} {d'} eb ec ed
  rewrite sym eb | sym ec | sym ed =
  refl
--}


IFLT-steps₁ : {k : ℕ} {w w' : 𝕎·} {n m a u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLT n a u v , w) ≡ (IFLT m a u v , w'))
IFLT-steps₁ {0} {w} {w'} {n} {m} {a} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLT-steps₁ {suc k} {w} {w'} {n} {m} {a} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT n a u v , w) ≡ (IFLT m a u v , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLT-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl

IFLT⇓₁ : {w w' : 𝕎·} {n m a u v : Term}
         → n ⇓ m from w to w'
         → IFLT n a u v ⇓ IFLT m a u v from w to w'
IFLT⇓₁ {w} {w'} {n} {m} {a} {u} {v} (k , comp) = IFLT-steps₁ {k} {w} {w'} {n} {m} {a} {u} {v} comp


IFLT⇛₁ : {w : 𝕎·} {n m a u v : Term}
         → n ⇛ m at w
         → IFLT n a u v ⇛ IFLT m a u v at w
IFLT⇛₁ {w} {n} {m} {a} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLT⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLT-steps₂ : {k : ℕ} {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLT (NUM i) n u v , w) ≡ (IFLT (NUM i) m u v , w'))
IFLT-steps₂ {0} {w} {w'} {i} {n} {m} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLT-steps₂ {suc k} {w} {w'} {i} {n} {m} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT (NUM i) n u v , w) ≡ (IFLT (NUM i) m u v , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLT-steps₂ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFLT⇓₂ : {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇓ m from w to w'
         → IFLT (NUM i) n u v ⇓ IFLT (NUM i) m u v from w to w'
IFLT⇓₂ {w} {w'} {i} {n} {m} {u} {v} (k , comp) = IFLT-steps₂ {k} {w} {w'} {i} {n} {m} {u} {v} comp


IFLT⇓₃ : {w w1 w2 : 𝕎·} {i j : ℕ} {a b u v : Term}
         → a ⇓ NUM i from w to w1
         → b ⇓ NUM j from w1 to w2
         → IFLT a b u v ⇓ IFLT (NUM i) (NUM j) u v from w to w2
IFLT⇓₃ {w} {w1} {w2} {i} {j} {a} {b} {u} {v} c1 c2 =
  ⇓-trans₂
    {w} {w1} {w2}
    {IFLT a b u v}
    {IFLT (NUM i) b u v}
    {IFLT (NUM i) (NUM j) u v}
    (IFLT⇓₁ {w} {w1} {a} {NUM i} {b} {u} {v} c1)
    (IFLT⇓₂ {w1} {w2} {i} {b} {NUM j} {u} {v} c2)


IFLT⇛₂ : {w : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇛ m at w
         → IFLT (NUM i) n u v ⇛ IFLT (NUM i) m u v at w
IFLT⇛₂ {w} {i} {n} {m} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLT⇓₂ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLT⇛< : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → j < k
          → IFLT (NUM j) (NUM k) a b ⇛ a at w
IFLT⇛< {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLT (NUM j) (NUM k) a b) w1 ≡ a
    c with j <? k
    ... | yes p = refl --⊥-elim (1+n≰n (≤-trans p lekj))
    ... | no p = ⊥-elim (1+n≰n (≤-trans (≰⇒> p) lekj)) --refl


IFLT⇛¬< : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → ¬ j < k
          → IFLT (NUM j) (NUM k) a b ⇛ b at w
IFLT⇛¬< {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLT (NUM j) (NUM k) a b) w1 ≡ b
    c with j <? k
    ... | yes p = ⊥-elim (⊥-elim (n≮n j (<-transˡ p (sucLeInj (≰⇒> lekj)))))
    ... | no p = refl


IFEQ-steps₁ : {k : ℕ} {w w' : 𝕎·} {n m a u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFEQ n a u v , w) ≡ (IFEQ m a u v , w'))
IFEQ-steps₁ {0} {w} {w'} {n} {m} {a} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFEQ-steps₁ {suc k} {w} {w'} {n} {m} {a} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFEQ n a u v , w) ≡ (IFEQ m a u v , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFEQ-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFEQ⇓₁ : {w w' : 𝕎·} {n m a u v : Term}
         → n ⇓ m from w to w'
         → IFEQ n a u v ⇓ IFEQ m a u v from w to w'
IFEQ⇓₁ {w} {w'} {n} {m} {a} {u} {v} (k , comp) = IFEQ-steps₁ {k} {w} {w'} {n} {m} {a} {u} {v} comp


IFEQ⇛₁ : {w : 𝕎·} {n m a u v : Term}
         → n ⇛ m at w
         → IFEQ n a u v ⇛ IFEQ m a u v at w
IFEQ⇛₁ {w} {n} {m} {a} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFEQ⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFEQ-steps₂ : {k : ℕ} {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFEQ (NUM i) n u v , w) ≡ (IFEQ (NUM i) m u v , w'))
IFEQ-steps₂ {0} {w} {w'} {i} {n} {m} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFEQ-steps₂ {suc k} {w} {w'} {i} {n} {m} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFEQ (NUM i) n u v , w) ≡ (IFEQ (NUM i) m u v , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFEQ-steps₂ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFEQ⇓₂ : {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇓ m from w to w'
         → IFEQ (NUM i) n u v ⇓ IFEQ (NUM i) m u v from w to w'
IFEQ⇓₂ {w} {w'} {i} {n} {m} {u} {v} (k , comp) = IFEQ-steps₂ {k} {w} {w'} {i} {n} {m} {u} {v} comp


IFEQ⇓₃ : {w w1 w2 : 𝕎·} {i j : ℕ} {a b u v : Term}
         → a ⇓ NUM i from w to w1
         → b ⇓ NUM j from w1 to w2
         → IFEQ a b u v ⇓ IFEQ (NUM i) (NUM j) u v from w to w2
IFEQ⇓₃ {w} {w1} {w2} {i} {j} {a} {b} {u} {v} c1 c2 =
  ⇓-trans₂
    {w} {w1} {w2}
    {IFEQ a b u v}
    {IFEQ (NUM i) b u v}
    {IFEQ (NUM i) (NUM j) u v}
    (IFEQ⇓₁ {w} {w1} {a} {NUM i} {b} {u} {v} c1)
    (IFEQ⇓₂ {w1} {w2} {i} {b} {NUM j} {u} {v} c2)


IFEQ⇛₂ : {w : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇛ m at w
         → IFEQ (NUM i) n u v ⇛ IFEQ (NUM i) m u v at w
IFEQ⇛₂ {w} {i} {n} {m} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFEQ⇓₂ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFEQ⇛= : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → j ≡ k
          → IFEQ (NUM j) (NUM k) a b ⇛ a at w
IFEQ⇛= {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFEQ (NUM j) (NUM k) a b) w1 ≡ a
    c with j ≟ k
    ... | yes p = refl
    ... | no p = ⊥-elim (p lekj)


IFEQ⇛¬= : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → j ≢ k
          → IFEQ (NUM j) (NUM k) a b ⇛ b at w
IFEQ⇛¬= {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFEQ (NUM j) (NUM k) a b) w1 ≡ b
    c with j ≟ k
    ... | yes p = ⊥-elim (⊥-elim (lekj p))
    ... | no p = refl


IFLE-steps₁ : {k : ℕ} {w w' : 𝕎·} {n m a u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLE a n u v , w) ≡ (IFLE a m u v , w'))
IFLE-steps₁ {0} {w} {w'} {n} {m} {a} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLE-steps₁ {suc k} {w} {w'} {n} {m} {a} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT n a v u , w) ≡ (IFLT m a v u , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLE-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFLE⇓₁ : {w w' : 𝕎·} {n m a u v : Term}
         → n ⇓ m from w to w'
         → IFLE a n u v ⇓ IFLE a m u v from w to w'
IFLE⇓₁ {w} {w'} {n} {m} {a} {u} {v} (k , comp) = IFLE-steps₁ {k} {w} {w'} {n} {m} {a} {u} {v} comp


IFLE⇛₁ : {w : 𝕎·} {n m a u v : Term}
         → n ⇛ m at w
         → IFLE a n u v ⇛ IFLE a m u v at w
IFLE⇛₁ {w} {n} {m} {a} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLE⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLE-steps₂ : {k : ℕ} {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
              → steps k (n , w) ≡ (m , w')
              → Σ ℕ (λ k → steps k (IFLE n (NUM i) u v , w) ≡ (IFLE m (NUM i) u v , w'))
IFLE-steps₂ {0} {w} {w'} {i} {n} {m} {u} {v} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
IFLE-steps₂ {suc k} {w} {w'} {i} {n} {m} {u} {v} comp with is-NUM n
... | inj₁ (x , p) rewrite p | stepsVal (NUM x) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ p with step⊎ n w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (IFLT (NUM i) n v u , w) ≡ (IFLT (NUM i) m v u , w'))
    c with is-NUM n
    ... | inj₁ (x' , p') rewrite p' = ⊥-elim (p x' refl)
    ... | inj₂ p' rewrite q = IFLE-steps₂ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


IFLE⇓₂ : {w w' : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇓ m from w to w'
         → IFLE n (NUM i) u v ⇓ IFLE m (NUM i) u v from w to w'
IFLE⇓₂ {w} {w'} {i} {n} {m} {u} {v} (k , comp) = IFLE-steps₂ {k} {w} {w'} {i} {n} {m} {u} {v} comp


IFLE⇛₂ : {w : 𝕎·} {i : ℕ} {n m u v : Term}
         → n ⇛ m at w
         → IFLE n (NUM i) u v ⇛ IFLE m (NUM i) u v at w
IFLE⇛₂ {w} {i} {n} {m} {u} {v} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (IFLE⇓₂ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → n ⇓ m from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


IFLE⇛≤ : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → k ≤ j
          → IFLE (NUM k) (NUM j) a b ⇛ a at w
IFLE⇛≤ {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLE (NUM k) (NUM j) a b) w1 ≡ a
    c with j <? k
    ... | yes p = ⊥-elim (1+n≰n (≤-trans p lekj))
    ... | no p = refl


IFLE⇛¬≤ : {k j : ℕ} {w : 𝕎·} {a b : Term}
          → ¬ k ≤ j
          → IFLE (NUM k) (NUM j) a b ⇛ b at w
IFLE⇛¬≤ {k} {j} {w} {a} {b} lekj w1 e1 = lift (1 , c)
  where
    c : stepsT 1 (IFLE (NUM k) (NUM j) a b) w1 ≡ b
    c with j <? k
    ... | yes p = refl
    ... | no p = ⊥-elim (n≮n j z4)
      where
        z1 : k < suc j
        z1 = ≰⇒> p

        z2 : j < k
        z2 = ≰⇒> lekj

        z3 : k ≡ j
        z3 = <s→¬<→≡ z1 (≤⇒≯ (<⇒≤ z2))

        z4 : j < j
        z4 = <-transˡ z2 (≤-reflexive z3)


CHOOSE-NAME⇛AX : {w : 𝕎·} {name : Name} {t : Term} → CHOOSE (NAME name) t ⇛ AX at w
CHOOSE-NAME⇛AX {w} {name} {t} w1 e1 = lift (1 , refl)


#CHOOSE : CTerm → CTerm → CTerm
#CHOOSE a b = ct (CHOOSE ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # CHOOSE ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#CHOOSE-NAME⇛AX : {w : 𝕎·} {name : Name} {t : CTerm} → #CHOOSE (#NAME name) t #⇛ #AX at w
#CHOOSE-NAME⇛AX {w} {name} {t} w1 e1 = CHOOSE-NAME⇛AX w1 e1


-- MOVE to computation
IFLE-CHOOSE⇛AX : {w : 𝕎·} {n a : Term} {k j : ℕ} {name : Name} {t : Term}
                  → n ⇛ NUM k at w
                  → a ⇛ NUM j at w
                  → IFLE n a (CHOOSE (NAME name) t) AX ⇛ AX at w
IFLE-CHOOSE⇛AX {w} {n} {a} {k} {j} {name} {t} c d =
  ⇛-trans (IFLE⇛₁ d) (⇛-trans (IFLE⇛₂ c) concl)
  where
    concl : IFLE (NUM k) (NUM j) (CHOOSE (NAME name) t) AX ⇛ AX at w
    concl with k ≤? j
    ... | yes p = ⇛-trans (IFLE⇛≤ p) CHOOSE-NAME⇛AX
    ... | no p = IFLE⇛¬≤ p


SEQ-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (SEQ a t , w) ≡ (SEQ b t , w'))
SEQ-steps₁ {0} {w} {w'} {a} {b} {t} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
SEQ-steps₁ {suc k} {w} {w'} {a} {b} {t} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w (suc k) x | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (SEQ a t , w) ≡ (SEQ b t , w'))
    c with isValue⊎ a
    ... | inj₁ x' = ⊥-elim (x x')
    ... | inj₂ x' rewrite q = SEQ-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


SEQ⇓₁ : {w w' : 𝕎·} {a b t : Term}
         → a ⇓ b from w to w'
         → SEQ a t ⇓ SEQ b t from w to w'
SEQ⇓₁ {w} {w'} {a} {b} {t} (k , comp) = SEQ-steps₁ {k} {w} {w'} {a} {b} {t} comp



SEQ⇛₁ : {w : 𝕎·} {a a' b : Term}
           → a ⇛ a' at w
           → SEQ a b ⇛ SEQ a' b at w
SEQ⇛₁ {w} {a} {a'} {b} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (SEQ⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))



SEQ-val⇓₁from-to : {w : 𝕎·} {a t : Term} → # t → isValue a → SEQ a t ⇓ t from w to w
SEQ-val⇓₁from-to {w} {a} {t} tc isv = 1 , c
  where
    c : steps 1 (SEQ a t , w) ≡ (t , w)
    c with isValue⊎ a
    ... | inj₁ x rewrite #shiftUp 0 (ct t tc) | subNotIn a t tc = refl
    ... | inj₂ x = ⊥-elim (x isv)


SEQ-AX⇓₁from-to : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇓ t from w to w
SEQ-AX⇓₁from-to {w} {t} tc = SEQ-val⇓₁from-to {w} {AX} {t} tc tt


SEQ-AX⇓₁ : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇓ t at w
SEQ-AX⇓₁ {w} {t} tc = 1 , c
  where
    c : sub AX (shiftUp 0 t) ≡ t
    c rewrite #shiftUp 0 (ct t tc) | subNotIn AX t tc = refl


SEQ-AX⇛₁ : {w : 𝕎·} {t : Term} → # t → SEQ AX t ⇛ t at w
SEQ-AX⇛₁ {w} {t} tc w1 e1 = lift (SEQ-AX⇓₁ tc)


SEQ-AX⇛ : {w : 𝕎·} {a b : Term}
           → # b
           → a ⇛ AX at w
           → SEQ a b ⇛ b at w
SEQ-AX⇛ {w} {a} {b} cb comp = ⇛-trans (SEQ⇛₁ comp) (SEQ-AX⇛₁ cb)



LET-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (LET a t , w) ≡ (LET b t , w'))
LET-steps₁ {0} {w} {w'} {a} {b} {t} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
LET-steps₁ {suc k} {w} {w'} {a} {b} {t} comp with isValue⊎ a
... | inj₁ x rewrite stepsVal a w (suc k) x | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (LET a t , w) ≡ (LET b t , w'))
    c with isValue⊎ a
    ... | inj₁ x' = ⊥-elim (x x')
    ... | inj₂ x' rewrite q = LET-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


LET⇓₁ : {w w' : 𝕎·} {a b t : Term}
         → a ⇓ b from w to w'
         → LET a t ⇓ LET b t from w to w'
LET⇓₁ {w} {w'} {a} {b} {t} (k , comp) = LET-steps₁ {k} {w} {w'} {a} {b} {t} comp



LET⇛₁ : {w : 𝕎·} {a a' b : Term}
           → a ⇛ a' at w
           → LET a b ⇛ LET a' b at w
LET⇛₁ {w} {a} {a'} {b} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (LET⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


isValue→LET⇓from-to : {v t : Term} {w : 𝕎·}
                       → isValue v
                       → LET v t ⇓ sub v t from w to w
isValue→LET⇓from-to {v} {t} {w} isv = 1 , c
  where
    c : steps 1 (LET v t , w) ≡ (sub v t , w)
    c with isValue⊎ v
    ... | inj₁ x = refl
    ... | inj₂ x = ⊥-elim (x isv)


isValue→LET⇛ : {v t : Term} {w : 𝕎·}
                 → isValue v
                 → LET v t ⇛ sub v t at w
isValue→LET⇛ {v} {t} {w} isv w1 e1 = lift (⇓-from-to→⇓ {w1} {w1} {LET v t} {sub v t} (isValue→LET⇓from-to isv))


SPREAD-steps₁ : {k : ℕ} {w w' : 𝕎·} {a b t : Term}
              → steps k (a , w) ≡ (b , w')
              → Σ ℕ (λ k → steps k (SPREAD a t , w) ≡ (SPREAD b t , w'))
SPREAD-steps₁ {0} {w} {w'} {a} {b} {t} comp rewrite pair-inj₁ comp | pair-inj₂ comp = 0 , refl
SPREAD-steps₁ {suc k} {w} {w'} {a} {b} {t} comp with is-PAIR a
... | inj₁ (u , v , p) rewrite p | stepsVal (PAIR u v ) w k tt | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl
... | inj₂ x with step⊎ a w
... |    inj₁ (y , w'' , q) rewrite q = suc (fst c) , snd c
  where
    c : Σ ℕ (λ k₁ → steps (suc k₁) (SPREAD a t , w) ≡ (SPREAD b t , w'))
    c with is-PAIR a
    ... | inj₁ (u' , v' , p') rewrite p' = ⊥-elim (x u' v' refl)
    ... | inj₂ x' rewrite q = SPREAD-steps₁ {k} comp
... |    inj₂ q rewrite q | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl


SPREAD⇓₁ : {w w' : 𝕎·} {a b t : Term}
         → a ⇓ b from w to w'
         → SPREAD a t ⇓ SPREAD b t from w to w'
SPREAD⇓₁ {w} {w'} {a} {b} {t} (k , comp) = SPREAD-steps₁ {k} {w} {w'} {a} {b} {t} comp



SPREAD⇛₁ : {w : 𝕎·} {a a' b : Term}
           → a ⇛ a' at w
           → SPREAD a b ⇛ SPREAD a' b at w
SPREAD⇛₁ {w} {a} {a'} {b} comp w1 e1 = lift (⇓-from-to→⇓ {w1} {fst c} (SPREAD⇓₁ (snd c)))
  where
    c : Σ 𝕎· (λ w2 → a ⇓ a' from w1 to w2)
    c = ⇓→from-to (lower (comp w1 e1))


{-
isValue→SPREAD⇓from-to : {v t : Term} {w : 𝕎·}
                       → isValue v
                       → SPREAD v t ⇓ sub v t from w to w
isValue→SPREAD⇓from-to {v} {t} {w} isv = 1 , c
  where
    c : steps 1 (SPREAD v t , w) ≡ (sub v t , w)
    c with is-PAIR v
    ... | inj₁ (u1 , u2 , p) rewrite p = {!!} --refl
    ... | inj₂ x = {!!} --⊥-elim (x isv)


isValue→SPREAD⇛ : {v t : Term} {w : 𝕎·}
                 → isValue v
                 → SPREAD v t ⇛ sub v t at w
isValue→SPREAD⇛ {v} {t} {w} isv w1 e1 = lift (⇓-from-to→⇓ {w1} {w1} {SPREAD v t} {sub v t} (isValue→SPREAD⇓from-to isv))
--}


≡ₗ→⇓from-to : {a b c : Term} {w1 w2 : 𝕎·}
              → c ≡ a
              → c ⇓ b from w1 to w2
              → a ⇓ b from w1 to w2
≡ₗ→⇓from-to {a} {b} {c} {w1} {w2} e comp rewrite e = comp



IFLT-NUM⇓< : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → n < m
              → step (IFLT (NUM n) (NUM m) a b) w ≡ just (a , w)
IFLT-NUM⇓< n m w a b ltnm with n <? m
... | yes r = refl
... | no r = ⊥-elim (r ltnm)


IFLT-NUM⇓¬< : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → ¬ (n < m)
              → step (IFLT (NUM n) (NUM m) a b) w ≡ just (b , w)
IFLT-NUM⇓¬< n m w a b ltnm with n <? m
... | yes r = ⊥-elim (ltnm r)
... | no r = refl


IFLT-NUM⇓ : (n m : ℕ) (w : 𝕎·) (a b c : Term)
              → a ⇓ c at w
              → b ⇓ c at w
              → IFLT (NUM n) (NUM m) a b ⇓ c at w
IFLT-NUM⇓ n m w a b c c₁ c₂ with n <? m
... | yes r = step-⇓-trans (IFLT-NUM⇓< n m w a b r) c₁
... | no r = step-⇓-trans (IFLT-NUM⇓¬< n m w a b r) c₂



IFEQ-NUM⇓= : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → n ≡ m
              → step (IFEQ (NUM n) (NUM m) a b) w ≡ just (a , w)
IFEQ-NUM⇓= n m w a b ltnm with n ≟ m
... | yes r = refl
... | no r = ⊥-elim (r ltnm)


IFEQ-NUM⇓¬= : (n m : ℕ) (w : 𝕎·) (a b : Term)
              → ¬ (n ≡ m)
              → step (IFEQ (NUM n) (NUM m) a b) w ≡ just (b , w)
IFEQ-NUM⇓¬= n m w a b ltnm with n ≟ m
... | yes r = ⊥-elim (ltnm r)
... | no r = refl


IFEQ-NUM⇓ : (n m : ℕ) (w : 𝕎·) (a b c : Term)
              → a ⇓ c at w
              → b ⇓ c at w
              → IFEQ (NUM n) (NUM m) a b ⇓ c at w
IFEQ-NUM⇓ n m w a b c c₁ c₂ with n ≟ m
... | yes r = step-⇓-trans (IFEQ-NUM⇓= n m w a b r) c₁
... | no r = step-⇓-trans (IFEQ-NUM⇓¬= n m w a b r) c₂



≡ᵣ→⇓from-to : {w1 w2 : 𝕎·} {a b c : Term}
              → b ≡ c
              → a ⇓ b from w1 to w2
              → a ⇓ c from w1 to w2
≡ᵣ→⇓from-to {w1} {w2} {a} {b} {c} e comp rewrite e = comp



abstract

  ¬Names→shiftNameUp≡ : (t : Term) (n : ℕ) → ¬names t ≡ true → shiftNameUp n t ≡ t
  ¬Names→shiftNameUp≡ (VAR x) n nnt = refl
--  ¬Names→shiftNameUp≡ NAT n nnt = refl
  ¬Names→shiftNameUp≡ QNAT n nnt = refl
--  ¬Names→shiftNameUp≡ TNAT n nnt = refl
  ¬Names→shiftNameUp≡ (LT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (QLT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (NUM x) n nnt = refl
  ¬Names→shiftNameUp≡ (IFLT t t₁ t₂ t₃) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₃ n (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) = refl
  ¬Names→shiftNameUp≡ (IFEQ t t₁ t₂ t₃) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₃ n (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) = refl
  ¬Names→shiftNameUp≡ (SUC t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (PI t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (LAMBDA t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (APPLY t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (FIX t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (LET t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (WT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (SUP t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  --¬Names→shiftNameUp≡ (DSUP t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (WREC t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (MT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  --¬Names→shiftNameUp≡ (MSUP t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  --¬Names→shiftNameUp≡ (DMSUP t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (SUM t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (PAIR t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (SPREAD t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (SET t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (ISECT t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (TUNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (UNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
--  ¬Names→shiftNameUp≡ (QTUNION t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (INL t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (INR t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (DECIDE t t₁ t₂) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nnt) = refl
  ¬Names→shiftNameUp≡ (EQ t t₁ t₂) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nnt) = refl
--  ¬Names→shiftNameUp≡ (EQB t t₁ t₂ t₃) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₂ n (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) | ¬Names→shiftNameUp≡ t₃ n (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nnt) = refl
  ¬Names→shiftNameUp≡ AX n nnt = refl
  ¬Names→shiftNameUp≡ FREE n nnt = refl
  ¬Names→shiftNameUp≡ (MSEQ x) n nnt = refl
  ¬Names→shiftNameUp≡ (MAPP s t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (CHOOSE t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (TSQUASH t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
--  ¬Names→shiftNameUp≡ (TTRUNC t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ NOWRITE n nnt = refl
  ¬Names→shiftNameUp≡ NOREAD  n nnt = refl
  ¬Names→shiftNameUp≡ (SUBSING t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (PURE) n nnt = refl
  ¬Names→shiftNameUp≡ (NOSEQ) n nnt = refl
  ¬Names→shiftNameUp≡ (TERM t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (ENC t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (DUM t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (FFDEFS t t₁) n nnt rewrite ¬Names→shiftNameUp≡ t n (∧≡true→ₗ (¬names t) (¬names t₁) nnt) | ¬Names→shiftNameUp≡ t₁ n (∧≡true→ᵣ (¬names t) (¬names t₁) nnt) = refl
  ¬Names→shiftNameUp≡ (UNIV x) n nnt = refl
  ¬Names→shiftNameUp≡ (LIFT t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (LOWER t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl
  ¬Names→shiftNameUp≡ (SHRINK t) n nnt rewrite ¬Names→shiftNameUp≡ t n nnt = refl

\end{code}
