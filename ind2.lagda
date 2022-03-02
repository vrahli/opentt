\begin{code}

-- This is similar to ind.lagda, but instead of breaking the □· abstraction, here we use a bar operator.
-- However, one problem is that Agda does not recognize now that the function terminates, and I'm therefore
-- using the {-# TERMINATING #-} pragma.


open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
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
open import compatible
open import progress
open import getChoice
open import mod

module ind2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
            (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
            (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where

open import worldDef(W)
open import computation(W)(C)(K)(G)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(E)
open import props0(W)(M)(C)(K)(P)(G)(E)
\end{code}




\begin{code}[hide]

-- add the missing cases & make it transitive
data <TypeStep : {u1 : 𝕌} {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : ≡Types u1 w1 T1 U1)
                 {u2 : 𝕌} {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : ≡Types u2 w2 T2 U2) → Set(lsuc(L))
data <TypeStep where
  <TypePIa : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
             (c₁ : T1 #⇛ (#PI A1 B1) at w)
             (c₂ : T2 #⇛ (#PI A2 B2) at w)
             (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
             (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → ≡∈Type u w' (eqta w' e) a1 a2
                                    → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
             (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
             (w' : 𝕎·) (e' : w ⊑· w')
             → <TypeStep {u} {w'} {A1} {A2} (eqta w' e') {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypePIb : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
             (c₁ : T1 #⇛ (#PI A1 B1) at w)
             (c₂ : T2 #⇛ (#PI A2 B2) at w)
             (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
             (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → ≡∈Type u w' (eqta w' e) a1 a2
                                    → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
             (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
             (w' : 𝕎·) (e' : w ⊑· w') (a1 a2 : CTerm) (eqa : ≡∈Type u w' (eqta w' e') a1 a2)
             → <TypeStep {u} {w'} {sub0 a1 B1} {sub0 a2 B2} (eqtb w' e' a1 a2 eqa) {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSUMa : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SUM A1 B1) at w)
              (c₂ : T2 #⇛ (#SUM A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → ≡∈Type u w' (eqta w' e) a1 a2
                                     → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w')
              → <TypeStep {u} {w'} {A1} {A2} (eqta w' e') {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSUMb : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SUM A1 B1) at w)
              (c₂ : T2 #⇛ (#SUM A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → ≡∈Type u w' (eqta w' e) a1 a2
                                     → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w') (a1 a2 : CTerm) (eqa : ≡∈Type u w' (eqta w' e') a1 a2)
              → <TypeStep {u} (eqtb w' e' a1 a2 eqa) {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSETa : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SET A1 B1) at w)
              (c₂ : T2 #⇛ (#SET A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → ≡∈Type u w' (eqta w' e) a1 a2
                                     → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w')
              → <TypeStep {u} {w'} {A1} {A2} (eqta w' e') {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSETb : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SET A1 B1) at w)
              (c₂ : T2 #⇛ (#SET A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → ≡∈Type u w' (eqta w' e) a1 a2
                                     → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w') (a1 a2 : CTerm) (eqa : ≡∈Type u w' (eqta w' e') a1 a2)
              → <TypeStep {u} (eqtb w' e' a1 a2 eqa) {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeEQ : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (a1 b1 a2 b2 A B : CTerm)
            (c₁ : T1 #⇛ (#EQ a1 a2 A) at w)
            (c₂ : T2 #⇛ (#EQ b1 b2 B) at w)
            (eqtA : ∀𝕎 w (λ w' _ → ≡Types u w' A B))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtA w e) a b))
            (eqt1 : ∀𝕎 w (λ w' e → ≡∈Type u w' (eqtA w' e) a1 b1))
            (eqt2 : ∀𝕎 w (λ w' e → ≡∈Type u w' (eqtA w' e) a2 b2))
            (w' : 𝕎·) (e' : w ⊑· w')
            → <TypeStep {u} {w'} {A} {B} (eqtA w' e') {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B c₁ c₂ eqtA exta eqt1 eqt2)
  <TypeUNIONl : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 B1 A2 B2 : CTerm)
                (c₁ : T1 #⇛ (#UNION A1 B1) at w)
                (c₂ : T2 #⇛ (#UNION A2 B2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                (eqtB : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtA w e) a b))
                (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtB w e) a b))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep {u} (eqtA w' e') {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 c₁ c₂ eqtA eqtB exta extb)
  <TypeUNIONr : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 B1 A2 B2 : CTerm)
                (c₁ : T1 #⇛ (#UNION A1 B1) at w)
                (c₂ : T2 #⇛ (#UNION A2 B2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                (eqtB : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtA w e) a b))
                (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtB w e) a b))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep {u} (eqtB w' e') {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 c₁ c₂ eqtA eqtB exta extb)
  <TypeSQUASH : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 : CTerm)
                (c₁ : T1 #⇛ (#TSQUASH A1) at w)
                (c₂ : T2 #⇛ (#TSQUASH A2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtA w e) a b))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep {u} (eqtA w' e') {u} {w} {T1} {T2} (EQTSQUASH A1 A2 c₁ c₂ eqtA exta)
  <TypeTCONST : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 : CTerm)
                (c₁ : T1 #⇛ (#TCONST A1) at w)
                (c₂ : T2 #⇛ (#TCONST A2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtA w e) a b))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep {u} (eqtA w' e') {u} {w} {T1} {T2} (EQTCONST A1 A2 c₁ c₂ eqtA exta)
{--  <TypeDUM : (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 : CTerm)
             (c₁ : T1 ⇛ (DUM A1) at w)
             (c₂ : T2 ⇛ (DUM A2) at w)
             (eqtA : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtA w e) a b))
             (w' : 𝕎·) (e' : w ⊑· w')
             → <TypeStep u (eqtA w' e') (EQTDUM A1 A2 c₁ c₂ eqtA exta)--}
  <TypeFFDEFS : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 x1 x2 : CTerm)
                (c₁ : T1 #⇛ (#FFDEFS A1 x1) at w)
                (c₂ : T2 #⇛ (#FFDEFS A2 x2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtA w e) a b))
                (eqx : ∀𝕎 w (λ w' e → ≡∈Type u w' (eqtA w' e) x1 x2))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep {u} (eqtA w' e') {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 c₁ c₂ eqtA exta eqx)
  <TypeLIFT : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 : CTerm)
              (c₁ : T1 #⇛ (#LIFT A1) at w)
              (c₂ : T2 #⇛ (#LIFT A2) at w)
              (eqtA : ∀𝕎 w (λ w' _ → ≡Types (↓𝕌 u) w' A1 A2))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type (↓𝕌 u) w (eqtA w e) a b))
              (w' : 𝕎·) (e' : w ⊑· w')
              → <TypeStep {↓𝕌 u} (eqtA w' e') {u} {w} {T1} {T2} (EQTLIFT A1 A2 c₁ c₂ eqtA exta)
  <TypeBAR : (u : 𝕌) (w : 𝕎·) (T1 T2 : CTerm) (i : □· w (λ w' _ → ≡Types u w' T1 T2))
             (w' : 𝕎·) (e' : w ⊑· w') (p : ≡Types u w' T1 T2) {--(a : atbar i w' e' p)--}
             → <TypeStep {u} p {u} (EQTBAR i)



data <Type : {u1 : 𝕌} {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : ≡Types u1 w1 T1 U1)
             {u2 : 𝕌} {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : ≡Types u2 w2 T2 U2) → Set(lsuc(lsuc(L)))
data <Type where
  <Type1 : {u1 : 𝕌} {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : ≡Types u1 w1 T1 U1)
           {u2 : 𝕌} {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : ≡Types u2 w2 T2 U2)
           → <TypeStep {u1} eqt1 {u2} eqt2 → <Type {u1} eqt1 {u2} eqt2
  <TypeS : {u1 : 𝕌} {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : ≡Types u1 w1 T1 U1)
           {u2 : 𝕌} {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : ≡Types u2 w2 T2 U2)
           {u3 : 𝕌} {w3 : 𝕎·} {T3 U3 : CTerm} (eqt3 : ≡Types u3 w3 T3 U3)
           → <Type {u1} eqt1 {u2} eqt2 → <TypeStep {u2} eqt2 {u3} eqt3 → <Type {u1} eqt1 {u3} eqt3



data ≤Type : {u1 : 𝕌} {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : ≡Types u1 w1 T1 U1)
             {u2 : 𝕌} {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : ≡Types u2 w2 T2 U2) → Set(lsuc(lsuc(L)))
data ≤Type where
  ≤Type0 : {u : 𝕌} {w : 𝕎·} {T U : CTerm} (eqt : ≡Types u w T U) → ≤Type {u} eqt {u} eqt
  ≤TypeS : {u1 : 𝕌} {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : ≡Types u1 w1 T1 U1)
           {u2 : 𝕌} {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : ≡Types u2 w2 T2 U2)
           → <Type {u1} eqt1 {u2} eqt2 → ≤Type {u1} eqt1 {u2} eqt2



<Type-NAT : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} {eqt : ≡Types u w T1 T2}
            {u' : 𝕌} {w' : 𝕎·} {U1 U2 : CTerm} {x₁ : U1 #⇛ #NAT at w'} {x₂ : U2 #⇛ #NAT at w'}
            → <Type {u} {w} {T1} {T2} eqt {u'} {w'} {U1} {U2} (EQTNAT x₁ x₂) → ⊥
<Type-NAT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTNAT x₁ x₂) ())
<Type-NAT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTNAT x₁ x₂) ltt ())



<Type-QNAT : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} {eqt : ≡Types u w T1 T2}
             {u' : 𝕌} {w' : 𝕎·} {U1 U2 : CTerm} {x₁ : U1 #⇛ #QNAT at w'} {x₂ : U2 #⇛ #QNAT at w'}
             → <Type {u} {w} {T1} {T2} eqt {u'} {w'} {U1} {U2} (EQTQNAT x₁ x₂) → ⊥
<Type-QNAT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTQNAT x₁ x₂) ())
<Type-QNAT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTQNAT x₁ x₂) ltt ())



<Type-LT : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} {eqt : ≡Types u w T1 T2}
           {u' : 𝕌} {w' : 𝕎·} {U1 U2 a1 b1 a2 b2 : CTerm} {x₁ : U1 #⇛ #LT a1 b1 at w'} {x₂ : U2 #⇛ #LT a2 b2 at w'}
           {s₁ : #strongMonEq w' a1 a2} {s₂ : #strongMonEq w' b1 b2}
           → <Type {u} {w} {T1} {T2} eqt {u'} {w'} {U1} {U2} (EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) → ⊥
<Type-LT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<Type1 .eqt .(EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ())
<Type-LT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<TypeS .eqt eqt2 .(EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ltt ())



<Type-QLT : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} {eqt : ≡Types u w T1 T2}
            {u' : 𝕌} {w' : 𝕎·} {U1 U2 a1 b1 a2 b2 : CTerm} {x₁ : U1 #⇛ #QLT a1 b1 at w'} {x₂ : U2 #⇛ #QLT a2 b2 at w'}
            {s₁ : #weakMonEq w' a1 a2} {s₂ : #weakMonEq w' b1 b2}
           → <Type {u} {w} {T1} {T2} eqt {u'} {w'} {U1} {U2} (EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) → ⊥
<Type-QLT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<Type1 .eqt .(EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ())
<Type-QLT {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<TypeS .eqt eqt2 .(EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ltt ())



<Type-FREE : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} {eqt : ≡Types u w T1 T2}
             {u' : 𝕌} {w' : 𝕎·} {U1 U2 : CTerm} {x₁ : U1 #⇛ #FREE at w'} {x₂ : U2 #⇛ #FREE at w'}
             → <Type {u} {w} {T1} {T2} eqt {u'} {w'} {U1} {U2} (EQTFREE x₁ x₂) → ⊥
<Type-FREE {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTFREE x₁ x₂) ())
<Type-FREE {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTFREE x₁ x₂) ltt ())



<Type-UNIV : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} {eqt : ≡Types u w T1 T2}
             {u' : 𝕌} {w' : 𝕎·} {U1 U2 : CTerm}
             {i : ℕ} {p : i < u' ·ₙ} {c₁ : U1 #⇛ #UNIV i at w'} {c₂ : U2 #⇛ #UNIV i at w'}
--{x : proj₁ (proj₂ u) w' U1 U2}
             → <Type {u} {w} {T1} {T2} eqt {u'} {w'} {U1} {U2} (EQTUNIV i p c₁ c₂) → ⊥
<Type-UNIV {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {i} {p} {c₁} {c₂} (<Type1 .eqt .(EQTUNIV i p c₁ c₂) ())
<Type-UNIV {u} {w} {T1} {T2} {eqt} {u'} {w'} {U1} {U2} {i} {p} {c₁} {c₂} (<TypeS .eqt eqt2 .(EQTUNIV i p c₁ c₂) ltt ())



#⇛-refl : (w : 𝕎·) (T : CTerm) → T #⇛ T at w
#⇛-refl w T w' e' = lift (⇓-refl ⌜ T ⌝ w')



PIeq-ext : {u : 𝕌} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0}
           {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
           {eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                  → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2))}
           {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
           → PIeq (≡∈Type u w' (eqta w' e1)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e1 a₁ a₂ eqa)) a b
           → PIeq (≡∈Type u w' (eqta w' e2)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e2 a₁ a₂ eqa)) a b
PIeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb h a₁ a₂ eqa =
  extb a₁ a₂ (#APPLY a a₁) (#APPLY b a₂) w' e1 e2 eqa1 eqa (h a₁ a₂ eqa1)
  where
    eqa1 : ≡∈Type u w' (eqta w' e1) a₁ a₂
    eqa1 = exta a₁ a₂ w' e2 e1 eqa





SUMeq-ext : {u : 𝕌} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0}
            {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
            {eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2))}
            {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
            → SUMeq (≡∈Type u w' (eqta w' e1)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e1 a₁ a₂ eqa)) w' a b
            → SUMeq (≡∈Type u w' (eqta w' e2)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e2 a₁ a₂ eqa)) w' a b
SUMeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) =
  a₁ , a₂ , b₁ , b₂ , exta a₁ a₂ w' e1 e2 ea , c₁ , c₂ , extb a₁ a₂ b₁ b₂ w' e1 e2 ea (exta a₁ a₂ w' e1 e2 ea) eb




SETeq-ext : {u : 𝕌} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0}
            {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
            {eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → ≡∈Type u w' (eqta w' e) a1 a2
                                   → ≡Types u w' (sub0 a1 B1) (sub0 a2 B2))}
            {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → ≡∈Type u w (eqtb w e a b x) c d))
            → SETeq (≡∈Type u w' (eqta w' e1)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e1 a₁ a₂ eqa)) a b
            → SETeq (≡∈Type u w' (eqta w' e2)) (λ a₁ a₂ eqa → ≡∈Type u w' (eqtb w' e2 a₁ a₂ eqa)) a b
SETeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (t , ea , eb) =
  t , exta a b w' e1 e2 ea , extb a b t t w' e1 e2 ea (exta a b w' e1 e2 ea) eb




EQeq-ext : {u : 𝕌} {w : 𝕎·} {A B a1 a2 : CTerm}
           {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A B)}
           {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
           (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
           → EQeq a1 a2 (≡∈Type u w' (eqta w' e1)) w' a b
           → EQeq a1 a2 (≡∈Type u w' (eqta w' e2)) w' a b
EQeq-ext {u} {w} {A} {B} {a1} {a2} {eqta} {w'} {e1} {e2} {a} {b} exta h = exta a1 a2 w' e1 e2 h




UNIONeq-ext : {u : 𝕌} {w : 𝕎·} {A1 B1 A2 B2 : CTerm}
              {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
              {eqtb : ∀𝕎 w (λ w' _ → ≡Types u w' B1 B2)}
              {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
              (extb : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqtb w e) a b))
              → UNIONeq (≡∈Type u w' (eqta w' e1)) (≡∈Type u w' (eqtb w' e1)) w' a b
              → UNIONeq (≡∈Type u w' (eqta w' e2)) (≡∈Type u w' (eqtb w' e2)) w' a b
UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (a1 , a2 , inj₁ (c₁ , c₂ , h)) =
  a1 , a2 , inj₁ (c₁ , c₂ , exta a1 a2 w' e1 e2 h)
UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (a1 , a2 , inj₂ (c₁ , c₂ , h)) =
  a1 , a2 , inj₂ (c₁ , c₂ , extb a1 a2 w' e1 e2 h)




TSQUASHeq-ext : {u : 𝕌} {w : 𝕎·} {A1 A2 : CTerm}
                {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
                {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
                → TSQUASHeq (≡∈Type u w' (eqta w' e1)) w' a b
                → TSQUASHeq (≡∈Type u w' (eqta w' e2)) w' a b
TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {w'} {e1} {e2} {a} {b} exta h =
  irr-TSQUASHeq eqta exta e1 e2 h
{--(c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , h) =
  (c₃ , a₁ , a₂ , isv₁ , isv₂ , c₁ , c₂ , exta a₁ a₂ w' e1 e2 h)--}



TCONSTeq-ext : {u : 𝕌} {w : 𝕎·} {A1 A2 : CTerm}
               {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
               {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
               (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
               → TCONSTeq (≡∈Type u w' (eqta w' e1)) w' a b
               → TCONSTeq (≡∈Type u w' (eqta w' e2)) w' a b
TCONSTeq-ext {u} {w} {A1} {A2} {eqta} {w'} {e1} {e2} {a} {b} exta h =
  irr-TCONSTeq eqta exta e1 e2 h



-- where u will be (↓𝕌 u)
LIFTeq-ext : {u : 𝕌} {w : 𝕎·} {A1 A2 : CTerm}
             {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
             {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
             → ≡∈Type u w' (eqta w' e1) a b
             → ≡∈Type u w' (eqta w' e2) a b
LIFTeq-ext {u} {w} {A1} {A2} {eqta} {w'} {e1} {e2} {a} {b} exta h =
  exta a b w' e1 e2 h




FFDEFSeq-ext : {u : 𝕌} {w : 𝕎·} {A1 A2 : CTerm} {x1 : CTerm}
               {eqta : ∀𝕎 w (λ w' _ → ≡Types u w' A1 A2)}
               {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
               (exta : (a b : CTerm) → wPredExtIrr (λ w e → ≡∈Type u w (eqta w e) a b))
               → FFDEFSeq x1 (≡∈Type u w' (eqta w' e1)) w' a b
               → FFDEFSeq x1 (≡∈Type u w' (eqta w' e2)) w' a b
FFDEFSeq-ext {u} {w} {A1} {A2} {x1} {eqta} {w'} {e1} {e2} {a} {b} exta (x , h , nd) =
  (x , exta x1 x w' e1 e2 h , nd)




ind<Type : (P : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} → ≡Types u w T1 T2 → Set(lsuc(L)))
           → ({u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
               → ({u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' {u} eqt → P {u'} eqt')
               → P {u} eqt)
           → {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2) → P eqt
{-# TERMINATING #-}
ind<Type P ind {u} {w0} {X1} {X2} eqt =
  -- just pick something larger
  indLtt
    {u} (EQTBAR i)
    {u} eqt
--    (<Type1 eqt (EQTBAR i) (<TypeBAR w0 X1 X2 i w0 (⊑-refl· w0) (aw w0 (⊑-refl· w0)) j))
    (<Type1 {u} eqt {u} (EQTBAR i) (<TypeBAR u w0 X1 X2 i w0 (⊑-refl· w0) eqt {--j--}))
  where
    aw : ∀𝕎 w0 (λ w' _ → ≡Types u w' X1 X2)
    aw = eqTypes-mon (u ·ᵤ) eqt

    i : □· w0 (λ w' _ → ≡Types u w' X1 X2)
    i = Mod.∀𝕎-□ M aw

{--
--    j : atbar i w0 (⊑-refl· w0) (aw w0 (⊑-refl· w0))
    j : atbar i w0 (⊑-refl· w0) eqt
    j = Bar.atBar-refl barI i eqt --ATOPENBAR w0 (⊑-refl· w0) w0 (⊑-refl· w0) (⊑-refl· w0)
--}

    indLtt : {u : 𝕌} {w : 𝕎·} {T1 T2 : CTerm} (eqt : ≡Types u w T1 T2)
             {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2')
             → <Type {u'} eqt' {u} eqt → P eqt'
    indLtt {u} {w} {T1} {T2} (EQTNAT x x₁) {u'} {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-NAT ltt)
    indLtt {u} {w} {T1} {T2} (EQTQNAT x x₁) {u'} {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-QNAT ltt)
    indLtt {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {u'} {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-LT ltt)
    indLtt {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {u'} {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-QLT ltt)
    indLtt {u} {w} {T1} {T2} (EQTFREE x x₁) {u'} {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-FREE ltt)

    indLtt {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {.u} {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypePIa .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e')) =
      ind {u} (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' {u} (eqta w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {.u} {w'} {.(sub0 a1 B1)} {.(sub0 a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypePIb .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e' a1 a2 eqa)) =
      ind {u} (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : ≡∈Type u w1 (eqta w1 e1) a1 a2) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta _ e') .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) x₂ (<TypePIa .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e')) =
      ind' w2 e' eqt' x₂
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb _ e' a1 a2 eqa) .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) x₂ (<TypePIb .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' x₂
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : ≡∈Type u w1 (eqta w1 e1) a1 a2) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSUMa .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {.(sub0 a1 B1)} {.(sub0 a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSUMb .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : ≡∈Type u w1 (eqta w1 e1) a1 a2) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta w2 e') .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSUMa .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb w2 e' a1 a2 eqa) .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSUMb .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : ≡∈Type u w1 (eqta w1 e1) a1 a2) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSETa .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {.(sub0 a1 B1)} {.(sub0 a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSETb .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : ≡∈Type u w1 (eqta w1 e1) a1 a2) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta w2 e') .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSETa .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb w2 e' a1 a2 eqa) .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSETb .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : ≡∈Type u w1 (eqta w1 e1) a1 a2) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) {u'} {w'} {.A} {.B} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) (<TypeEQ .u .w .T1 .T2 .a1 .b1 .a2 .b2 .A .B .x .x₁ .eqtA .exta .eqt1 .eqt2 .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) ltt (<TypeEQ .u .w .T1 .T2 .a1 .b1 .a2 .b2 .A .B .x .x₁ .eqtA .exta .eqt1 .eqt2 w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {u'} {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) (<TypeUNIONl .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {u'} {w'} {.B1} {.B2} .(eqtB w' e') (<Type1 .(eqtB w' e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) (<TypeUNIONr .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb .w' e')) =
      ind (eqtB w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtB w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtB w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ltt (<TypeUNIONl .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtB w2 e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ltt (<TypeUNIONr .u .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtB w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtB w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {u'} {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTSQUASH A1 A2 x x₁ eqtA exta) (<TypeSQUASH .u .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA .exta .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTSQUASH A1 A2 x x₁ eqtA exta) ltt (<TypeSQUASH .u .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA .exta w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {u'} {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTCONST A1 A2 x x₁ eqtA exta) (<TypeTCONST .u .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA .exta .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTCONST A1 A2 x x₁ eqtA exta) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTCONST A1 A2 x x₁ eqtA exta) ltt (<TypeTCONST .u .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA .exta w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

--    indLtt {u} {w} {T1} {T2} (EQTDUM A1 A2 x x₁ eqtA ext) {w'} {A1'} {A2'} eqtA' ltt = {!!}

    indLtt {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {u'} {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) (<TypeFFDEFS .u .w .T1 .T2 .A1 .A2 .x1 .x2 .x .x₁ .eqtA .exta .eqx .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ltt (<TypeFFDEFS .u .w .T1 .T2 .A1 .A2 .x1 .x2 .x .x₁ .eqtA .exta .eqx w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) {u'} {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-UNIV ltt)

    indLtt {u} {w} {T1} {T2} (EQTLIFT A1 A2 c₁ c₂ eqtA exta) {.(↓𝕌 u)} {.w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTLIFT A1 A2 c₁ c₂ eqtA exta) (<TypeLIFT .u .w .T1 .T2 .A1 .A2 .c₁ .c₂ .eqtA .exta w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTLIFT A1 A2 c₁ c₂ eqtA exta) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTLIFT A1 A2 c₁ c₂ eqtA exta) ltt (<TypeLIFT .u .w .T1 .T2 .A1 .A2 .c₁ .c₂ .eqtA .exta w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2') → <Type {u'} eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTBAR i) {u'} {w'} {.T1} {.T2} eqt' (<Type1 .eqt' .(EQTBAR i) (<TypeBAR .u .w .T1 .T2 .i .w' e' .eqt' {--a--})) =
      ind eqt' (ind' w' e' eqt' {--a--})
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (p : ≡Types u w1 T1 T2) {--(a : Bar.atBar barI i w1 e1 p)--}
               {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2')
               → <Type {u'} eqt' p → P eqt'
        ind' w1 e1 p {--a--} {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt p eqt' ltt

    indLtt {u} {w} {T1} {T2} (EQTBAR i) {u'} {w'} {T1'} {T2'} eqt' (<TypeS .eqt' eqt2 .(EQTBAR i) ltt (<TypeBAR .u .w .T1 .T2 .i w2 e' .eqt2 {--a--})) =
      ind' w2 e' eqt2 {--a--} eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (p : ≡Types u w1 T1 T2) {--(a : Bar.atBar barI i w1 e1 p)--}
               {u' : 𝕌} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : ≡Types u' w' T1' T2')
               → <Type {u'} eqt' p → P eqt'
        ind' w1 e1 p {--a--} {u'} {w'} {T1'} {T2'} eqt' ltt = indLtt p eqt' ltt




≤Type-EQTBAR-eqInTypeExt : {u : 𝕌} {w : 𝕎·} {A B : CTerm}
                           {i : □· w (λ w' _ → ≡Types u w' A B)}
                           {w1 : 𝕎·} (e1 : w ⊑· w1) {z : ≡Types u w1 A B}
                           {--(a : atbar i w1 e1 z)--}
                           (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} (EQTBAR i) → eqInTypeExt eqt')
                           → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} z → eqInTypeExt eqt')
≤Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} e1 {.eqt'} {--a--} ext {.u} {.w1} {.A} {.B} eqt' (≤Type0 {.u} .eqt') =
  ext eqt' (≤TypeS _ _ (<Type1 _ _ (<TypeBAR _ _ _ _ i w1 e1 eqt' {--a--})))
≤Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} e1 {z} {--a--} ext {u'} {w'} {A'} {B'} eqt' (≤TypeS .eqt' .z x) =
  ext eqt' (≤TypeS _ _ (<TypeS _ _ _ x (<TypeBAR _ _ _ _ i w1 e1 z {--a--})))



<Type-EQTBAR-eqInTypeExt : {u : 𝕌} {w : 𝕎·} {A B : CTerm}
                           {i : □· w (λ w' _ → ≡Types u w' A B)}
                           {w1 : 𝕎·} (e1 : w ⊑· w1) {z : ≡Types u w1 A B}
                           {--(a : atbar i w1 e1 z)--}
                           (ext : {u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → <Type {u'} eqt' {u} (EQTBAR i) → eqInTypeExt eqt')
                           → ({u' : 𝕌} {w' : 𝕎·} {A' B' : CTerm} (eqt' : ≡Types u' w' A' B') → ≤Type {u'} eqt' {u} z → eqInTypeExt eqt')
<Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} e1 {.eqt'} {--a--} ext {.u} {.w1} {.A} {.B} eqt' (≤Type0 .eqt') =
  ext eqt' (<Type1 _ _ (<TypeBAR _ _ _ _ i w1 e1 eqt' {--a--}))
<Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} e1 {z} {--a--} ext {u'} {w'} {A'} {B'} eqt' (≤TypeS .eqt' .z x) =
  ext eqt' (<TypeS _ _ _ x (<TypeBAR _ _ _ _ i w1 e1 z {--a--}))

\end{code}
