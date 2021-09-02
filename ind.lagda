\begin{code}

open import bar

module ind (bar : Bar) where

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
open import theory (bar)
open import props0 (bar)
\end{code}




\begin{code}[hide]

-- add the missing cases & make it transitive
data <TypeStep (u : univs) : {w1 : world} {T1 U1 : Term} (eqt1 : eqTypes u w1 T1 U1)
                             {w2 : world} {T2 U2 : Term} (eqt2 : eqTypes u w2 T2 U2) → Set₁
data <TypeStep u where
  <TypePIa : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
             (c₁ : T1 ⇛ (PI A1 B1) at w)
             (c₂ : T2 ⇛ (PI A2 B2) at w)
             (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
             (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub a1 B1) (sub a2 B2)))
             (w' : world) (e' : w' ≽ w)
             → <TypeStep u (eqta w' e') (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  <TypePIb : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
             (c₁ : T1 ⇛ (PI A1 B1) at w)
             (c₂ : T2 ⇛ (PI A2 B2) at w)
             (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
             (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                    → eqTypes u w' (sub a1 B1) (sub a2 B2)))
             (w' : world) (e' : w' ≽ w) (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2)
             → <TypeStep u (eqtb w' e' a1 a2 eqa) (EQTPI A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  <TypeSUMa : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
              (c₁ : T1 ⇛ (SUM A1 B1) at w)
              (c₂ : T2 ⇛ (SUM A2 B2) at w)
              (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub a1 B1) (sub a2 B2)))
              (w' : world) (e' : w' ≽ w)
              → <TypeStep u (eqta w' e') (EQTSUM A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  <TypeSUMb : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
              (c₁ : T1 ⇛ (SUM A1 B1) at w)
              (c₂ : T2 ⇛ (SUM A2 B2) at w)
              (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub a1 B1) (sub a2 B2)))
              (w' : world) (e' : w' ≽ w) (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2)
              → <TypeStep u (eqtb w' e' a1 a2 eqa) (EQTSUM A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  <TypeSETa : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
              (c₁ : T1 ⇛ (SET A1 B1) at w)
              (c₂ : T2 ⇛ (SET A2 B2) at w)
              (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub a1 B1) (sub a2 B2)))
              (w' : world) (e' : w' ≽ w)
              → <TypeStep u (eqta w' e') (EQTSET A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  <TypeSETb : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
              (c₁ : T1 ⇛ (SET A1 B1) at w)
              (c₂ : T2 ⇛ (SET A2 B2) at w)
              (eqta : allW w (λ w' _ → eqTypes u w' A1 A2))
              (eqtb : allW w (λ w' e → ∀ a1 a2 → eqInType u w' (eqta w' e) a1 a2
                                     → eqTypes u w' (sub a1 B1) (sub a2 B2)))
              (w' : world) (e' : w' ≽ w) (a1 a2 : Term) (eqa : eqInType u w' (eqta w' e') a1 a2)
              → <TypeStep u (eqtb w' e' a1 a2 eqa) (EQTSET A1 B1 A2 B2 c₁ c₂ eqta eqtb)
  <TypeEQ : (w : world) (T1 T2 : Term) (a1 b1 a2 b2 A B : Term)
            (c₁ : T1 ⇛ (EQ a1 a2 A) at w)
            (c₂ : T2 ⇛ (EQ b1 b2 B) at w)
            (eqtA : allW w (λ w' _ → eqTypes u w' A B))
            (eqt1 : allW w (λ w' e → eqInType u w' (eqtA w' e) a1 b1))
            (eqt2 : allW w (λ w' e → eqInType u w' (eqtA w' e) a2 b2))
            (w' : world) (e' : w' ≽ w)
            → <TypeStep u (eqtA w' e') (EQTEQ a1 b1 a2 b2 A B c₁ c₂ eqtA eqt1 eqt2)
  <TypeUNIONl : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
                (c₁ : T1 ⇛ (UNION A1 B1) at w)
                (c₂ : T2 ⇛ (UNION A2 B2) at w)
                (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
                (eqtB : allW w (λ w' _ → eqTypes u w' B1 B2))
                (w' : world) (e' : w' ≽ w)
                → <TypeStep u (eqtA w' e') (EQTUNION A1 B1 A2 B2 c₁ c₂ eqtA eqtB)
  <TypeUNIONr : (w : world) (T1 T2 : Term) (A1 B1 A2 B2 : Term)
                (c₁ : T1 ⇛ (UNION A1 B1) at w)
                (c₂ : T2 ⇛ (UNION A2 B2) at w)
                (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
                (eqtB : allW w (λ w' _ → eqTypes u w' B1 B2))
                (w' : world) (e' : w' ≽ w)
                → <TypeStep u (eqtB w' e') (EQTUNION A1 B1 A2 B2 c₁ c₂ eqtA eqtB)
  <TypeSQUASH : (w : world) (T1 T2 : Term) (A1 A2 : Term)
                (c₁ : T1 ⇛ (TSQUASH A1) at w)
                (c₂ : T2 ⇛ (TSQUASH A2) at w)
                (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
                (w' : world) (e' : w' ≽ w)
                → <TypeStep u (eqtA w' e') (EQTSQUASH A1 A2 c₁ c₂ eqtA)
  <TypeDUM : (w : world) (T1 T2 : Term) (A1 A2 : Term)
             (c₁ : T1 ⇛ (DUM) at w)
             (c₂ : T2 ⇛ (DUM A2) at w)
             (eqtA : eqTypes u w' A1 A2)
             (w' : world) (e' : w' ≽ w)
             → <TypeStep u (eqtA w' e') (EQTDUM A1 A2 c₁ c₂ eqtA)
  <TypeFFDEFS : (w : world) (T1 T2 : Term) (A1 A2 x1 x2 : Term)
                (c₁ : T1 ⇛ (FFDEFS A1 x1) at w)
                (c₂ : T2 ⇛ (FFDEFS A2 x2) at w)
                (eqtA : allW w (λ w' _ → eqTypes u w' A1 A2))
                (eqx : allW w (λ w' e → eqInType u w' (eqtA w' e) x1 x2))
                (w' : world) (e' : w' ≽ w)
                → <TypeStep u (eqtA w' e') (EQFFDEFS A1 A2 x1 x2 c₁ c₂ eqtA eqx)
  <TypeBAR : (w : world) (T1 T2 : Term) (i : inbar w (λ w' _ → eqTypes u w' T1 T2))
             (w1 : world) (e1 : w1 ≽ w) (w2 : world) (e2 : w2 ≽ fst (i w1 e1)) (z : w2 ≽ w)
             → <TypeStep u (snd (snd (i w1 e1)) w2 e2 z) (EQTBAR i)



data <Type (u : univs) : {w1 : world} {T1 U1 : Term} (eqt1 : eqTypes u w1 T1 U1)
                         {w2 : world} {T2 U2 : Term} (eqt2 : eqTypes u w2 T2 U2) → Set₁
data <Type u where
  <Type1 : {w1 : world} {T1 U1 : Term} (eqt1 : eqTypes u w1 T1 U1)
           {w2 : world} {T2 U2 : Term} (eqt2 : eqTypes u w2 T2 U2)
           → <TypeStep u eqt1 eqt2 → <Type u eqt1 eqt2
  <TypeS : {w1 : world} {T1 U1 : Term} (eqt1 : eqTypes u w1 T1 U1)
           {w2 : world} {T2 U2 : Term} (eqt2 : eqTypes u w2 T2 U2)
           {w3 : world} {T3 U3 : Term} (eqt3 : eqTypes u w3 T3 U3)
           → <Type u eqt1 eqt2 → <TypeStep u eqt2 eqt3 → <Type u eqt1 eqt3


<Type-NAT : {u : univs} {w : world} {T1 T2 : Term} {eqt : eqTypes u w T1 T2}
            {w' : world} {U1 U2 : Term} {x₁ : U1 ⇛ NAT at w'} {x₂ : U2 ⇛ NAT at w'}
            → <Type u eqt (EQTNAT x₁ x₂) → ⊥
<Type-NAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTNAT x₁ x₂) ())
<Type-NAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTNAT x₁ x₂) ltt ())



<Type-QNAT : {u : univs} {w : world} {T1 T2 : Term} {eqt : eqTypes u w T1 T2}
             {w' : world} {U1 U2 : Term} {x₁ : U1 ⇛ QNAT at w'} {x₂ : U2 ⇛ QNAT at w'}
             → <Type u eqt (EQTQNAT x₁ x₂) → ⊥
<Type-QNAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTQNAT x₁ x₂) ())
<Type-QNAT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTQNAT x₁ x₂) ltt ())



<Type-LT : {u : univs} {w : world} {T1 T2 : Term} {eqt : eqTypes u w T1 T2}
           {w' : world} {U1 U2 a1 b1 a2 b2 : Term} {x₁ : U1 ⇛ LT a1 b1 at w'} {x₂ : U2 ⇛ LT a2 b2 at w'}
           {s₁ : strongMonEq w' a1 a2} {s₂ : strongMonEq w' b1 b2}
           → <Type u eqt (EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) → ⊥
<Type-LT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<Type1 .eqt .(EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ())
<Type-LT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<TypeS .eqt eqt2 .(EQTLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ltt ())



<Type-QLT : {u : univs} {w : world} {T1 T2 : Term} {eqt : eqTypes u w T1 T2}
            {w' : world} {U1 U2 a1 b1 a2 b2 : Term} {x₁ : U1 ⇛ QLT a1 b1 at w'} {x₂ : U2 ⇛ QLT a2 b2 at w'}
            {s₁ : weakMonEq w' a1 a2} {s₂ : weakMonEq w' b1 b2}
           → <Type u eqt (EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) → ⊥
<Type-QLT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<Type1 .eqt .(EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ())
<Type-QLT {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {a1} {b1} {a2} {b2} {x₁} {x₂} {s₁} {s₂} (<TypeS .eqt eqt2 .(EQTQLT a1 a2 b1 b2 x₁ x₂ s₁ s₂) ltt ())



<Type-FREE : {u : univs} {w : world} {T1 T2 : Term} {eqt : eqTypes u w T1 T2}
             {w' : world} {U1 U2 : Term} {x₁ : U1 ⇛ FREE at w'} {x₂ : U2 ⇛ FREE at w'}
             → <Type u eqt (EQTFREE x₁ x₂) → ⊥
<Type-FREE {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<Type1 .eqt .(EQTFREE x₁ x₂) ())
<Type-FREE {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x₁} {x₂} (<TypeS .eqt eqt2 .(EQTFREE x₁ x₂) ltt ())



<Type-UNIV : {u : univs} {w : world} {T1 T2 : Term} {eqt : eqTypes u w T1 T2}
             {w' : world} {U1 U2 : Term} {x : proj₁ (proj₂ u) w' U1 U2}
             → <Type u eqt (EQTUNIV x) → ⊥
<Type-UNIV {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x} (<Type1 .eqt .(EQTUNIV x) ())
<Type-UNIV {u} {w} {T1} {T2} {eqt} {w'} {U1} {U2} {x} (<TypeS .eqt eqt2 .(EQTUNIV x) ltt ())



⇛-refl : (w : world) (T : Term) → T ⇛ T at w
⇛-refl w T w' e' = lift (⇓-refl T w')



eqTypes-mon2 : (u : univs) → mon (proj₁ (proj₂ u)) → {w : world} {T1 T2 : Term} → eqTypes u w T1 T2
               → allW w (λ w' e' → eqTypes u w' T1 T2)
eqTypes-mon2 u m {.w'} {T1} {T2} eqt w' (extRefl .w') = eqt
eqTypes-mon2 u m {w} {T1} {T2} eqt w' e' = eqTypes-mon u m eqt w' e'



ind<Type : {u : univs} (umon :  mon (proj₁ (proj₂ u))) (P : {w : world} {T1 T2 : Term} → eqTypes u w T1 T2 → Set)
           → ({w : world} {T1 T2 : Term} (eqt : eqTypes u w T1 T2)
               → ({w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' eqt → P eqt')
               → P eqt)
           → {w : world} {T1 T2 : Term} (eqt : eqTypes u w T1 T2) → P eqt
ind<Type {u} umon P ind {w0} {X1} {X2} eqt =
  -- just pick something larger
  indLtt (EQTSQUASH X1 X2 (⇛-refl w0 (TSQUASH X1)) (⇛-refl w0 (TSQUASH X2)) aw)
         eqt
         (<Type1 eqt
                 (EQTSQUASH X1 X2 (⇛-refl w0 (TSQUASH X1)) (⇛-refl w0 (TSQUASH X2)) aw)
                 (<TypeSQUASH w0 (TSQUASH X1) (TSQUASH X2) X1 X2 (⇛-refl w0 (TSQUASH X1)) (⇛-refl w0 (TSQUASH X2)) aw w0 (extRefl w0)))
  where
    aw : allW w0 (λ w' _ → eqTypes u w' X1 X2)
    aw = eqTypes-mon2 u umon eqt

    indLtt : {w : world} {T1 T2 : Term} (eqt : eqTypes u w T1 T2)
             {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2')
             → <Type u eqt' eqt → P eqt'
    indLtt {w} {T1} {T2} (EQTNAT x x₁) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-NAT ltt)
    indLtt {w} {T1} {T2} (EQTQNAT x x₁) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-QNAT ltt)
    indLtt {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-LT ltt)
    indLtt {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-QLT ltt)
    indLtt {w} {T1} {T2} (EQTFREE x x₁) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-FREE ltt)

    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) (<TypePIa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {.(sub a1 B1)} {.(sub a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) (<TypePIb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (a1 a2 : Term) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta _ e') .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) x₂ (<TypePIa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb w2 e')) =
      ind' w2 e' eqt' x₂
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb _ e' a1 a2 eqa) .(EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) x₂ (<TypePIb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' x₂
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (a1 a2 : Term) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) (<TypeSUMa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {.(sub a1 B1)} {.(sub a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) (<TypeSUMb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (a1 a2 : Term) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta w2 e') .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) ltt (<TypeSUMa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb w2 e' a1 a2 eqa) .(EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) ltt (<TypeSUMb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (a1 a2 : Term) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {.A1} {.A2} .(eqta w' e') (<Type1 .(eqta w' e') .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) (<TypeSETa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .w' e')) =
      ind (eqta w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {.(sub a1 B1)} {.(sub a2 B2)} .(eqtb w' e' a1 a2 eqa) (<Type1 .(eqtb w' e' a1 a2 eqa) .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) (<TypeSETb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb .w' e' a1 a2 eqa)) =
      ind (eqtb w' e' a1 a2 eqa) (ind' w' e' a1 a2 eqa)
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (a1 a2 : Term) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqta w2 e') .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) ltt (<TypeSETa .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqta w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqta w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtb w2 e' a1 a2 eqa) .(EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) ltt (<TypeSETb .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqta .eqtb w2 e' a1 a2 eqa)) =
      ind' w2 e' a1 a2 eqa eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (a1 a2 : Term) (eqa : eqInType u w1 (eqta w1 e1) a1 a2) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtb w1 e1 a1 a2 eqa) → P eqt'
        ind' w1 e1 a1 a2 eqa {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtb w1 e1 a1 a2 eqa) eqt' ltt

    indLtt {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) {w'} {.A} {.B} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) (<TypeEQ .w .T1 .T2 .a1 .b1 .a2 .b2 .A .B .x .x₁ .eqtA .eqt1 .eqt2 .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) ltt (<TypeEQ .w .T1 .T2 .a1 .b1 .a2 .b2 .A .B .x .x₁ .eqtA .eqt1 .eqt2 w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) (<TypeUNIONl .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) {w'} {.B1} {.B2} .(eqtB w' e') (<Type1 .(eqtB w' e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) (<TypeUNIONr .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB .w' e')) =
      ind (eqtB w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtB w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtB w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) ltt (<TypeUNIONl .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtB w2 e') .(EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) ltt (<TypeUNIONr .w .T1 .T2 .A1 .B1 .A2 .B2 .x .x₁ .eqtA .eqtB w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtB w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtB w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA) {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQTSQUASH A1 A2 x x₁ eqtA) (<TypeSQUASH .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQTSQUASH A1 A2 x x₁ eqtA) ltt (<TypeSQUASH .w .T1 .T2 .A1 .A2 .x .x₁ .eqtA w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) {w'} {.A1} {.A2} .(eqtA w' e') (<Type1 .(eqtA w' e') .(EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) (<TypeFFDEFS .w .T1 .T2 .A1 .A2 .x1 .x2 .x .x₁ .eqtA .eqx .w' e')) =
      ind (eqtA w' e') (ind' w' e')
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(eqtA w2 e') .(EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) ltt (<TypeFFDEFS .w .T1 .T2 .A1 .A2 .x1 .x2 .x .x₁ .eqtA .eqx w2 e')) =
      ind' w2 e' eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2') → <Type u eqt' (eqtA w1 e1) → P eqt'
        ind' w1 e1 {w'} {T1'} {T2'} eqt' ltt = indLtt (eqtA w1 e1) eqt' ltt

    indLtt {w} {T1} {T2} (EQTUNIV x) {w'} {T1'} {T2'} eqt' ltt = ⊥-elim (<Type-UNIV ltt)

    indLtt {w} {T1} {T2} (EQTBAR i) {w'} {.T1} {.T2} .(snd (snd (i w1 e1)) w' e2 z) (<Type1 .(snd (snd (i w1 e1)) w' e2 z) .(EQTBAR i) (<TypeBAR .w .T1 .T2 .i w1 e1 .w' e2 z)) =
      ind (snd (snd (i w1 e1)) w' e2 z) (ind' w1 e1 w' e2 z)
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (w2 : world) (e2 : w2 ≽ fst (i w1 e1)) (z : w2 ≽ w)
               {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2')
               → <Type u eqt' (snd (snd (i w1 e1)) w2 e2 z) → P eqt'
        ind' w1 e1 w2 e2 z {w'} {T1'} {T2'} eqt' ltt = indLtt (snd (snd (i w1 e1)) w2 e2 z) eqt' ltt

    indLtt {w} {T1} {T2} (EQTBAR i) {w'} {T1'} {T2'} eqt' (<TypeS .eqt' .(snd (snd (i w1 e1)) w2 e2 z) .(EQTBAR i) ltt (<TypeBAR .w .T1 .T2 .i w1 e1 w2 e2 z)) =
      ind' w1 e1 w2 e2 z eqt' ltt
      where
        ind' : (w1 : world) (e1 : w1 ≽ w) (w2 : world) (e2 : w2 ≽ fst (i w1 e1)) (z : w2 ≽ w)
               {w' : world} {T1' T2' : Term} (eqt' : eqTypes u w' T1' T2')
               → <Type u eqt' (snd (snd (i w1 e1)) w2 e2 z) → P eqt'
        ind' w1 e1 w2 e2 z {w'} {T1'} {T2'} eqt' ltt = indLtt (snd (snd (i w1 e1)) w2 e2 z) eqt' ltt

\end{code}
