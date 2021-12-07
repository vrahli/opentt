\begin{code}

-- This is similar to ind.lagda, but instead of breaking the inbar abstraction, here we use a bar operator.
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

open import calculus
open import world
open import choice

module ind2 (W : PossibleWorlds) (C : Choice W) where -- (bar : Bar) where
open import worldDef(W)
open import choiceDef(W)(C)
open import computation(W)(C)
--open import theory (bar)
open import bar(W)
open import theory(W)(C)
open import props0(W)(C)
\end{code}




\begin{code}[hide]

-- add the missing cases & make it transitive
data <TypeStep (u : univs) : {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : eqTypes u w1 T1 U1)
                             {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : eqTypes u w2 T2 U2) → Set₁
data <TypeStep u where
  <TypePIa : (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
             (c₁ : T1 #⇛ (#PI A1 B1) at w)
             (c₂ : T2 #⇛ (#PI A2 B2) at w)
             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
             (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
             (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
             (w' : 𝕎·) (e' : w ⊑· w')
             → <TypeStep u {w'} {A1} {A2} (eqta w' e') {w} {T1} {T2} (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypePIb : (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
             (c₁ : T1 #⇛ (#PI A1 B1) at w)
             (c₂ : T2 #⇛ (#PI A2 B2) at w)
             (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
             (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
             (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
             (w' : 𝕎·) (e' : w ⊑· w') (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2)
             → <TypeStep u {w'} {sub0 a1 B1} {sub0 a2 B2} (eqtb w' e' a1 a2 eqa) {w} {T1} {T2} (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSUMa : (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SUM A1 B1) at w)
              (c₂ : T2 #⇛ (#SUM A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w')
              → <TypeStep u {w'} {A1} {A2} (eqta w' e') {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSUMb : (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SUM A1 B1) at w)
              (c₂ : T2 #⇛ (#SUM A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w') (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2)
              → <TypeStep u (eqtb w' e' a1 a2 eqa) {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSETa : (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SET A1 B1) at w)
              (c₂ : T2 #⇛ (#SET A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w')
              → <TypeStep u {w'} {A1} {A2} (eqta w' e') {w} {T1} {T2} (EQTSET A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeSETb : (w : 𝕎·) (T1 T2 : CTerm) (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
              (c₁ : T1 #⇛ (#SET A1 B1) at w)
              (c₂ : T2 #⇛ (#SET A2 B2) at w)
              (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : ∀𝕎 w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
              (w' : 𝕎·) (e' : w ⊑· w') (a1 a2 : CTerm) (eqa : eqInType u w' (eqta w' e') a1 a2)
              → <TypeStep u (eqtb w' e' a1 a2 eqa) {w} {T1} {T2} (EQTSET A1 B1 A2 B2 c₁ c₂ eqta eqtb exta extb)
  <TypeEQ : (w : 𝕎·) (T1 T2 : CTerm) (a1 b1 a2 b2 A B : CTerm)
            (c₁ : T1 #⇛ (#EQ a1 a2 A) at w)
            (c₂ : T2 #⇛ (#EQ b1 b2 B) at w)
            (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A B))
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
            (eqt1 : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) a1 b1))
            (eqt2 : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) a2 b2))
            (w' : 𝕎·) (e' : w ⊑· w')
            → <TypeStep u {w'} {A} {B} (eqtA w' e') {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B c₁ c₂ eqtA exta eqt1 eqt2)
  <TypeUNIONl : (w : 𝕎·) (T1 T2 : CTerm) (A1 B1 A2 B2 : CTerm)
                (c₁ : T1 #⇛ (#UNION A1 B1) at w)
                (c₂ : T2 #⇛ (#UNION A2 B2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                (eqtB : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
                (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtB w e) a b))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep u (eqtA w' e') {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 c₁ c₂ eqtA eqtB exta extb)
  <TypeUNIONr : (w : 𝕎·) (T1 T2 : CTerm) (A1 B1 A2 B2 : CTerm)
                (c₁ : T1 #⇛ (#UNION A1 B1) at w)
                (c₂ : T2 #⇛ (#UNION A2 B2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                (eqtB : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
                (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtB w e) a b))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep u (eqtB w' e') {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 c₁ c₂ eqtA eqtB exta extb)
  <TypeSQUASH : (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 : CTerm)
                (c₁ : T1 #⇛ (#TSQUASH A1) at w)
                (c₂ : T2 #⇛ (#TSQUASH A2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep u (eqtA w' e') {w} {T1} {T2} (EQTSQUASH A1 A2 c₁ c₂ eqtA exta)
{--  <TypeDUM : (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 : CTerm)
             (c₁ : T1 ⇛ (DUM A1) at w)
             (c₂ : T2 ⇛ (DUM A2) at w)
             (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
             (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
             (w' : 𝕎·) (e' : w ⊑· w')
             → <TypeStep u (eqtA w' e') (EQTDUM A1 A2 c₁ c₂ eqtA exta)--}
  <TypeFFDEFS : (w : 𝕎·) (T1 T2 : CTerm) (A1 A2 x1 x2 : CTerm)
                (c₁ : T1 #⇛ (#FFDEFS A1 x1) at w)
                (c₂ : T2 #⇛ (#FFDEFS A2 x2) at w)
                (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
                (eqx : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) x1 x2))
                (w' : 𝕎·) (e' : w ⊑· w')
                → <TypeStep u (eqtA w' e') {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 c₁ c₂ eqtA exta eqx)
  <TypeBAR : (w : 𝕎·) (T1 T2 : CTerm) (i : inbar w (λ w' _ → eqTypes u w' T1 T2))
             (w' : 𝕎·) (e' : w ⊑· w') (p : eqTypes u w' T1 T2) (a : atbar i w' e' p)
             → <TypeStep u p (EQTBAR i)



data <Type (u : univs) : {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : eqTypes u w1 T1 U1)
                         {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : eqTypes u w2 T2 U2) → Set₁
data <Type u where
  <Type1 : {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : eqTypes u w1 T1 U1)
           {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : eqTypes u w2 T2 U2)
           → <TypeStep u eqt1 eqt2 → <Type u eqt1 eqt2
  <TypeS : {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : eqTypes u w1 T1 U1)
           {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : eqTypes u w2 T2 U2)
           {w3 : 𝕎·} {T3 U3 : CTerm} (eqt3 : eqTypes u w3 T3 U3)
           → <Type u eqt1 eqt2 → <TypeStep u eqt2 eqt3 → <Type u eqt1 eqt3



data ≤Type (u : univs) : {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : eqTypes u w1 T1 U1)
                         {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : eqTypes u w2 T2 U2) → Set₁
data ≤Type u where
  ≤Type0 : {w : 𝕎·} {T U : CTerm} (eqt : eqTypes u w T U) → ≤Type u eqt eqt
  ≤TypeS : {w1 : 𝕎·} {T1 U1 : CTerm} (eqt1 : eqTypes u w1 T1 U1)
           {w2 : 𝕎·} {T2 U2 : CTerm} (eqt2 : eqTypes u w2 T2 U2)
           → <Type u eqt1 eqt2 → ≤Type u eqt1 eqt2



<Type-NAT : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} {eqt : eqTypes u w T1 T2}
            {w' : 𝕎·} {U1 U2 : CTerm} {x₁ : U1 #⇛ #NAT at w'} {x₂ : U2 #⇛ #NAT at w'}
            → <Type u {w} {T1} {T2} eqt {w'} {U1} {U2} (EQTNAT x₁ x₂) → ⊥
<Type-NAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTNAT x₁ x₂) ())
<Type-NAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTNAT x₁ x₂) ltt ())



<Type-QNAT : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} {eqt : eqTypes u w T1 T2}
             {w' : 𝕎·} {U1 U2 : CTerm} {x₁ : U1 #⇛ #QNAT at w'} {x₂ : U2 #⇛ #QNAT at w'}
             → <Type u {w} {T1} {T2} eqt {w'} {U1} {U2} (EQTQNAT x₁ x₂) → ⊥
<Type-QNAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTQNAT x₁ x₂) ())
<Type-QNAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTQNAT x₁ x₂) ltt ())



<Type-LT : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} {eqt : eqTypes u w T1 T2}
           {w' : 𝕎·} {U1 U2 a1 b1 a2 b2 : CTerm} {x₁ : U1 #⇛ #LT a1 b1 at w'} {x₂ : U2 #⇛ #LT a2 b2 at w'}
           {s₁ : #strongMonEq w' a1 a2} {s₂ : #strongMonEq w' b1 b2}
           → <Type u {w} {T1} {T2} eqt {w'} {U1} {U2} (EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) → ⊥
<Type-LT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<Type1 .eqt .(EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ())
<Type-LT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<TypeS .eqt eqt2 .(EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ltt ())



<Type-QLT : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} {eqt : eqTypes u w T1 T2}
            {w' : 𝕎·} {U1 U2 a1 b1 a2 b2 : CTerm} {x₁ : U1 #⇛ #QLT a1 b1 at w'} {x₂ : U2 #⇛ #QLT a2 b2 at w'}
            {s₁ : #weakMonEq w' a1 a2} {s₂ : #weakMonEq w' b1 b2}
           → <Type u {w} {T1} {T2} eqt {w'} {U1} {U2} (EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) → ⊥
<Type-QLT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<Type1 .eqt .(EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ())
<Type-QLT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<TypeS .eqt eqt2 .(EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ltt ())



<Type-FREE : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} {eqt : eqTypes u w T1 T2}
             {w' : 𝕎·} {U1 U2 : CTerm} {x₁ : U1 #⇛ #FREE at w'} {x₂ : U2 #⇛ #FREE at w'}
             → <Type u {w} {T1} {T2} eqt {w'} {U1} {U2} (EQTFREE x₁ x₂) → ⊥
<Type-FREE {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTFREE x₁ x₂) ())
<Type-FREE {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTFREE x₁ x₂) ltt ())



<Type-UNIV : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} {eqt : eqTypes u w T1 T2}
             {w' : 𝕎·} {U1 U2 : CTerm} {x : proj₁ (proj₂ u) w' U1 U2}
             → <Type u eqt (EQTUNIV x) → ⊥
<Type-UNIV {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x} (<Type1 .eqt .(EQTUNIV x) ())
<Type-UNIV {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x} (<TypeS .eqt eqt2 .(EQTUNIV x) ltt ())



#⇛-refl : (w : 𝕎·) (T : CTerm) → T #⇛ T at w
#⇛-refl w T w' e' = lift (⇓-refl ⌜ T ⌝ w')



eqTypes-mon2 : (u : univs) → mon (proj₁ (proj₂ u)) → {w : 𝕎·} {T1 T2 : CTerm} → eqTypes u w T1 T2
               → ∀𝕎 w (λ w' e' → eqTypes u w' T1 T2)
--eqTypes-mon2 u m {.w'} {T1} {T2} eqt w' (⊑-refl· .w') = eqt
eqTypes-mon2 u m {w} {T1} {T2} eqt w' e' = eqTypes-mon u m eqt w' e'





PIeq-ext : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0}
           {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2)}
           {eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                  → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2))}
           {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
           → PIeq (eqInType u w' (eqta w' e1)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e1 a₁ a₂ eqa)) a b
           → PIeq (eqInType u w' (eqta w' e2)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e2 a₁ a₂ eqa)) a b
PIeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb h a₁ a₂ eqa =
  extb a₁ a₂ (#APPLY a a₁) (#APPLY b a₂) w' e1 e2 eqa1 eqa (h a₁ a₂ eqa1)
  where
    eqa1 : eqInType u w' (eqta w' e1) a₁ a₂
    eqa1 = exta a₁ a₂ w' e2 e1 eqa





SUMeq-ext : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0}
            {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2)}
            {eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2))}
            {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            → SUMeq (eqInType u w' (eqta w' e1)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e1 a₁ a₂ eqa)) w' a b
            → SUMeq (eqInType u w' (eqta w' e2)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e2 a₁ a₂ eqa)) w' a b
SUMeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (a₁ , a₂ , b₁ , b₂ , ea , c₁ , c₂ , eb) =
  a₁ , a₂ , b₁ , b₂ , exta a₁ a₂ w' e1 e2 ea , c₁ , c₂ , extb a₁ a₂ b₁ b₂ w' e1 e2 ea (exta a₁ a₂ w' e1 e2 ea) eb




SETeq-ext : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {B1 B2 : CTerm0}
            {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2)}
            {eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                                   → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2))}
            {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
            (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
            (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
            → SETeq (eqInType u w' (eqta w' e1)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e1 a₁ a₂ eqa)) a b
            → SETeq (eqInType u w' (eqta w' e2)) (λ a₁ a₂ eqa → eqInType u w' (eqtb w' e2 a₁ a₂ eqa)) a b
SETeq-ext {u} {w} {A1} {A2} {B1} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (t , ea , eb) =
  t , exta a b w' e1 e2 ea , extb a b t t w' e1 e2 ea (exta a b w' e1 e2 ea) eb




EQeq-ext : {u : univs} {w : 𝕎·} {A B a1 a2 : CTerm}
           {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A B)}
           {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
           (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
           → EQeq a1 a2 (eqInType u w' (eqta w' e1)) w' a b
           → EQeq a1 a2 (eqInType u w' (eqta w' e2)) w' a b
EQeq-ext {u} {w} {A} {B} {a1} {a2} {eqta} {w'} {e1} {e2} {a} {b} exta (c₁ , c₂ , h) = (c₁ , c₂ , exta a1 a2 w' e1 e2 h)




UNIONeq-ext : {u : univs} {w : 𝕎·} {A1 B1 A2 B2 : CTerm}
              {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2)}
              {eqtb : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2)}
              {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
              (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
              (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtb w e) a b))
              → UNIONeq (eqInType u w' (eqta w' e1)) (eqInType u w' (eqtb w' e1)) w' a b
              → UNIONeq (eqInType u w' (eqta w' e2)) (eqInType u w' (eqtb w' e2)) w' a b
UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (a1 , a2 , inj₁ (c₁ , c₂ , h)) =
  a1 , a2 , inj₁ (c₁ , c₂ , exta a1 a2 w' e1 e2 h)
UNIONeq-ext {u} {w} {A1} {B1} {A2} {B2} {eqta} {eqtb} {w'} {e1} {e2} {a} {b} exta extb (a1 , a2 , inj₂ (c₁ , c₂ , h)) =
  a1 , a2 , inj₂ (c₁ , c₂ , extb a1 a2 w' e1 e2 h)




TSQUASHeq-ext : {u : univs} {w : 𝕎·} {A1 A2 : CTerm}
                {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2)}
                {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
                (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
                → TSQUASHeq (eqInType u w' (eqta w' e1)) w' a b
                → TSQUASHeq (eqInType u w' (eqta w' e2)) w' a b
TSQUASHeq-ext {u} {w} {A1} {A2} {eqta} {w'} {e1} {e2} {a} {b} exta (a₁ , a₂ , c₁ , c₂ , c₃ , h) =
  (a₁ , a₂ , c₁ , c₂ , c₃ , exta a₁ a₂ w' e1 e2 h)




FFDEFSeq-ext : {u : univs} {w : 𝕎·} {A1 A2 : CTerm} {x1 : CTerm}
               {eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2)}
               {w' : 𝕎·} {e1 e2 : w ⊑· w'} {a b : CTerm}
               (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
               → FFDEFSeq x1 (eqInType u w' (eqta w' e1)) w' a b
               → FFDEFSeq x1 (eqInType u w' (eqta w' e2)) w' a b
FFDEFSeq-ext {u} {w} {A1} {A2} {x1} {eqta} {w'} {e1} {e2} {a} {b} exta (x , c₁ , c₂ , h , nd) =
  (x , c₁ , c₂ , exta x1 x w' e1 e2 h , nd)




ind<Type : {u : univs} (umon : mon (proj₁ (proj₂ u))) (P : {w : 𝕎·} {T1 T2 : CTerm} → eqTypes u w T1 T2 → Set₁)
           → ({w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
               → ({w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' eqt → P eqt')
               → P eqt)
           → {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2) → P eqt
{-# TERMINATING #-}
ind<Type {u} umon P ind {w0} {X1} {X2} eqt =
  -- just pick something larger
  indLtt
    (EQTBAR i)
    eqt
--    (<Type1 eqt (EQTBAR i) (<TypeBAR w0 X1 X2 i w0 (⊑-refl· w0) (aw w0 (⊑-refl· w0)) j))
    (<Type1 eqt (EQTBAR i) (<TypeBAR w0 X1 X2 i w0 (⊑-refl· w0) eqt j))
  where
    aw : ∀𝕎 w0 (λ w' _ → eqTypes u w' X1 X2)
    aw = eqTypes-mon2 u umon eqt

    i : inbar w0 (λ w' _ → eqTypes u w' X1 X2)
    i = Bar.∀𝕎-inBar inOpenBar-Bar aw

--    j : atbar i w0 (⊑-refl· w0) (aw w0 (⊑-refl· w0))
    j : atbar i w0 (⊑-refl· w0) eqt
    j = ATOPENBAR-R eqt --ATOPENBAR w0 (⊑-refl· w0) w0 (⊑-refl· w0) (⊑-refl· w0)

    indLtt : {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
             {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2')
             → <Type u eqt' eqt → P eqt'
    indLtt {w} {T1} {T2} (EQTNAT x x₁) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-NAT ltt)
    indLtt {w} {T1} {T2} (EQTQNAT x x₁) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-QNAT ltt)
    indLtt {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-LT ltt)
    indLtt {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-QLT ltt)
    indLtt {w} {T1} {T2} (EQTFREE x x₁) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-FREE ltt)


    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypePIa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {.(sub0 a1 B1)} {.(sub0 a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypePIb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta _ e') .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) x₂ (<TypePIa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e')) =
      ind' w2 e' eqt' x₂
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb _ e' a1 a2 eqa) .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) x₂ (<TypePIb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' x₂
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSUMa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {.(sub0 a1 B1)} {.(sub0 a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSUMb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta w2 e') .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSUMa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb w2 e' a1 a2 eqa) .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSUMb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSETa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {.(sub0 a1 B1)} {.(sub0 a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) (<TypeSETb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta w2 e') .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSETa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb w2 e' a1 a2 eqa) .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) ltt (<TypeSETb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .exta .extb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (a1 a2 : CTerm) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) {w'} {.A} {.B} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) (<TypeEQ .w .T1 .T2 .a1 .b1 .a2 .b2 .A .B .x .x₁ .eqtA .exta .eqt1 .eqt2 .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) ltt (<TypeEQ .w .T1 .T2 .a1 .b1 .a2 .b2 .A .B .x .x₁ .eqtA .exta .eqt1 .eqt2 w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) (<TypeUNIONl .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {w'} {.B1} {.B2} .(eqtB w' e') (<Type1 .(eqtB w' e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) (<TypeUNIONr .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb .w' e')) =
      ind (eqtB w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtB w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtB w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ltt (<TypeUNIONl .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtB w2 e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) ltt (<TypeUNIONr .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .exta .extb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtB w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtB w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTSQUASH A1 A2 x x₁ eqtA exta) (<TypeSQUASH .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA .exta .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTSQUASH A1 A2 x x₁ eqtA exta) ltt (<TypeSQUASH .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA .exta w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

--    indLtt {w} {T1} {T2} (EQTDUM A1 A2 x x₁ eqtA ext) {w'} {A1'} {A2'} eqtA' ltt = {!!}

    indLtt {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) (<TypeFFDEFS .w .T1 .T2 .A1 .A2 .x1 .x2 .x .x₁ .eqtA .exta .eqx .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) ltt (<TypeFFDEFS .w .T1 .T2 .A1 .A2 .x1 .x2 .x .x₁ .eqtA .exta .eqx w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNIV x) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-UNIV ltt)

    indLtt {w} {T1} {T2} (EQTBAR i) {w'} {.T1} {.T2} eqt' (<Type1 .eqt' .(EQTBAR i) (<TypeBAR .w .T1 .T2 .i .w' e' .eqt' a)) =
      ind eqt' (ind' w' e' eqt' a)
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (p : eqTypes u w1 T1 T2) (a : Bar.atBar inOpenBar-Bar i w1 e1 p)
               {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2')
               → <Type u eqt' p → P eqt'
        ind' w1 e1 p a {w'} {T1'} {T2'} eqt' ltt = indLtt p eqt' ltt

    indLtt {w} {T1} {T2} (EQTBAR i) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' eqt2 .(EQTBAR i) ltt (<TypeBAR .w .T1 .T2 .i w2 e' .eqt2 a)) =
      ind' w2 e' eqt2 a eqt' ltt
      where
        ind' : (w1 : 𝕎·) (e1 : w ⊑· w1) (p : eqTypes u w1 T1 T2) (a : Bar.atBar inOpenBar-Bar i w1 e1 p)
               {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : eqTypes u w' T1' T2')
               → <Type u eqt' p → P eqt'
        ind' w1 e1 p a {w'} {T1'} {T2'} eqt' ltt = indLtt p eqt' ltt




≤Type-EQTBAR-eqInTypeExt : {u : univs} {w : 𝕎·} {A B : CTerm}
                           {i : inbar w (λ w' _ → eqTypes u w' A B)}
                           {w1 : 𝕎·} {e1 : w ⊑· w1} {z : eqTypes u w1 A B}
                           (a : atbar i w1 e1 z)
                           (ext : {w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' (EQTBAR i) → eqInTypeExt eqt')
                           → ({w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' z → eqInTypeExt eqt')
≤Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} {e1} {.eqt'} a ext {.w1} {.A} {.B} eqt' (≤Type0 .eqt') =
  ext eqt' (≤TypeS _ _ (<Type1 _ _ (<TypeBAR _ _ _ i w1 e1 eqt' a)))
≤Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} {e1} {z} a ext {w'} {A'} {B'} eqt' (≤TypeS .eqt' .z x) =
  ext eqt' (≤TypeS _ _ (<TypeS _ _ _ x (<TypeBAR _ _ _ i w1 e1 z a)))



<Type-EQTBAR-eqInTypeExt : {u : univs} {w : 𝕎·} {A B : CTerm}
                           {i : inbar w (λ w' _ → eqTypes u w' A B)}
                           {w1 : 𝕎·} {e1 : w ⊑· w1} {z : eqTypes u w1 A B}
                           (a : atbar i w1 e1 z)
                           (ext : {w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u w' A' B') → <Type u eqt' (EQTBAR i) → eqInTypeExt eqt')
                           → ({w' : 𝕎·} {A' B' : CTerm} (eqt' : eqTypes u w' A' B') → ≤Type u eqt' z → eqInTypeExt eqt')
<Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} {e1} {.eqt'} a ext {.w1} {.A} {.B} eqt' (≤Type0 .eqt') =
  ext eqt' (<Type1 _ _ (<TypeBAR _ _ _ i w1 e1 eqt' a))
<Type-EQTBAR-eqInTypeExt {u} {w} {A} {B} {i} {w1} {e1} {z} a ext {w'} {A'} {B'} eqt' (≤TypeS .eqt' .z x) =
  ext eqt' (<TypeS _ _ _ x (<TypeBAR _ _ _ i w1 e1 z a))

\end{code}
