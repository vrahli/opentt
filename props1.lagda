\begin{code}
module props1 where

open import Level using (Level ; 0ℓ) renaming (suc to lsuc)
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
open import calculus
open import world
open import theory
open import props0
\end{code}


%Let us now prove a few simple results about this semantics


\begin{code}[hide]
-- ---------------------------------
-- More properties
{--
eqTypessym : (I : Inh) (u : univs) → TEQsym (eqTypes u I)
eqInTypesym : (I : Inh) (u : univs) (w : world) {T1 T2 : Term} (eqt : eqTypes u I w T1 T2) (a b : Term)
              → (eqInType u I w eqt a b)
              → (eqInType u I w eqt b a)
eqInTypesym2 : (I : Inh) (u : univs) (w : world) {T1 T2 : Term} (eqt : eqTypes u I w T1 T2) (a b : Term)
              → (eqInType u I w (eqTypessym I u w T1 T2 eqt) a b)
              → (eqInType u I w eqt a b)

eqTypessym I u w a b (EQTNAT x x₁) = EQTNAT x₁ x
eqTypessym I u w a b (EQTQNAT x x₁) = EQTQNAT x₁ x
eqTypessym I u w a b (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTLT a2 a1 b2 b1 x₁ x (strongMonEqsym I x₂) (strongMonEqsym I x₃)
eqTypessym I u w a b (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) =
  EQTQLT a2 a1 b2 b1 x₁ x (weakMonEqsym I x₂) (weakMonEqsym I x₃)
eqTypessym I u w a b (EQTFREE x x₁) = EQTFREE x₁ x
eqTypessym I u w a b (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTPI A2 B2 A1 B1 x₁ x
        (λ w1 e1 → eqTypessym _ _ _ _ _ (eqta _ e1))
        (λ w1 e1 a1 a2 et →
          let z = eqInTypesym2 I u w1 (eqta w1 e1) a2 a1 (eqInTypesym I u w1 (eqTypessym I u w1 A1 A2 (eqta w1 e1)) a1 a2 et) in
          eqTypessym _ _ _ _ _ (eqtb _ e1 a2 a1 z))
eqTypessym I u w a b (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) =
  EQTSUM A2 B2 A1 B1 x₁ x
        (λ w1 e1 → eqTypessym _ _ _ _ _ (eqta _ e1))
        (λ w1 e1 a1 a2 et →
          let z = eqInTypesym2 I u w1 (eqta w1 e1) a2 a1 (eqInTypesym I u w1 (eqTypessym I u w1 A1 A2 (eqta w1 e1)) a1 a2 et) in
          eqTypessym _ _ _ _ _ (eqtb _ e1 a2 a1 z))
eqTypessym I u w a b (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) = {!!}
eqTypessym I u w a b (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) = {!!}
eqTypessym I u w a b (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = {!!}
eqTypessym I u w a b (EQTSQUASH A1 A2 x x₁ eqtA) = {!!}
eqTypessym I u w a b (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = {!!}
eqTypessym I u w a b (EQTUNIV x) = {!!}
eqTypessym I u w a b (EQTBAR x) = {!!}
eqTypessym I u w a b (EQTLOWER A1 A2 c₁ c₂ eqt) = {!!}

eqInTypesym I u w (EQTNAT x x₁) a b e = inOpenBarstrongMonEqsym I e
eqInTypesym I u w (EQTQNAT x x₁) a b e = inOpenBarweakMonEqsym I e
eqInTypesym I u w (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) a b e = {!!}
eqInTypesym I u w (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) a b e = {!!}
eqInTypesym I u w (EQTFREE x x₁) a b e = {!!}
eqInTypesym I u w (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) a b e =
  λ w1 e1 → let (w2 , (e2 , z)) = e _ e1 in
   (_ , (e2 , λ w3 e3 a1 a2 eqa →
                let eqa' = eqInTypesym I u w3 (eqta w3 (eTrans e3 (eTrans (proj₁ (snd (e w1 e1))) e1))) a1 a2 eqa in
                let z1 = z _ e3 a2 a1 eqa' in
                let z2 = eqInTypesym I u w3 (eqtb w3 (eTrans e3 (eTrans (proj₁ (snd (e w1 e1))) e1)) a2 a1 eqa') (APPLY a a2) (APPLY b a1) z1 in
                {!!}))
eqInTypesym I u w (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) a b e = {!!}
eqInTypesym I u w (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) a b e = {!!}
eqInTypesym I u w (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) a b e = {!!}
eqInTypesym I u w (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) a b e = {!!}
eqInTypesym I u w (EQTSQUASH A1 A2 x x₁ eqtA) a b e = {!!}
eqInTypesym I u w (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) a b e = {!!}
eqInTypesym I u w (EQTUNIV x) a b e = {!!}
eqInTypesym I u w (EQTBAR x) a b e = {!!}
eqInTypesym I u w (EQTLOWER A1 A2 c₁ c₂ eqt) a b e = {!!}

eqInTypesym2 I u w e = {!!}
--}

{--eqtypesIsym : (I : Inh) → TEQsym (eqtypesI I)
eqtypesIsym I w a b e =
  let (n , e) = e in
  (n , {!!})--}

{--eqtypesNsym : (n k : ℕ) → TEQsym (eqtypesN n k)
eqtypesNsym n = {!!} --}

eqtypessym : TEQsym eqtypes
eqtypessym w a b t = {!!}
--  let (n , t) = t in
--   (n , λ j c → {!!})

eqtypestrans : TEQtrans eqtypes
eqtypestrans = {!!}

-- A proof that (eqtypes, eqintype) is a type system
TSeq : TS eqtypes eqintype
TSeq = mkts eqtypessym eqtypestrans {!!} {!!} {!!}


eqInTypeExt : (u : univs) (I : Inh) (w : world) (A B a b : Term) (e1 e2 : eqTypes u I w A B)
              → eqInType u I w e1 a b
              → eqInType u I w e2 a b
eqInTypeExt u I w A B a b e1 e2 i = {!!}


eqTypes-mon : (u : univs) → mon (eqTypes u)
eqTypes-mon u = {!!}

equalTypes-mon : (u : ℕ) → mon (equalTypes u)
equalTypes-mon u = eqTypes-mon (uni u)

equalInType-mon : (u : ℕ) (T : Term) → mon (λ I w → equalInType u I w T)
equalInType-mon u T = {!!}

equalInType-refl : {u : ℕ} {I : Inh} {w : world} {T a b : Term} → equalInType u I w T a b → equalInType u I w T a a
equalInType-refl {u} {I} {w} {T} {a} {b} e = {!!}


equalInTypeBar : (u : ℕ) (I : Inh) (w : world) (A a b : Term)
                 → inOpenBar I w (λ w' _ → equalInType u I w' A a b)
                 → equalInType u I w A a b
equalInTypeBar u I w A a b h =
  (EQTBAR (inOpenBarEqualInType-inOpenBarEqTypes u I w A a b h) ,
   λ w1 e1 → let (w2 , (e2 , h2)) = h w1 e1 in
   (w2 , ([]≽-refl I w2 , λ w3 e3 → let (eqt3 , eqi3) = h2 w3 e3 in
     eqInTypeExt (uni u) I w3 A A a b (proj₁ (snd (snd (h w1 e1)) w3 e3))
       (snd (snd (inOpenBarEqualInType-inOpenBarEqTypes u I w A a b h w1 e1))
            w3 ([]≽-trans {I} e3 {--(λ j c → extRefl (proj₁ (h w1 e1)))--} ([]≽-refl I w2)))
       eqi3)))


eqTypesSQUASH : (w : world) (I : Inh) (u : univs) (a b : Term)
  → # a → # b
  → eqTypes u I w a b
  → eqTypes u I w (SQUASH a) (SQUASH b)
eqTypesSQUASH w I u a b na nb eqt =
  EQTSET TRUE a TRUE b
         (compAllRefl I (SQUASH a) w)
         (compAllRefl I (SQUASH b) w)
         (λ w1 e1 → eqTypesTRUE _ _ _)
         (λ w1 e1 a1 a2 i →
           let s1 = sym (subNotIn a1 a na) in
           let s2 = sym (subNotIn a2 b nb) in
           let eqt1 = subst (λ a → eqTypes u I w a b) s1 eqt in
           let eqt2 = subst (λ b → eqTypes u I w (sub a1 a) b) s2 eqt1 in
           eqTypes-mon _ _ _ _ _ eqt2 _ e1)


ifeqTypesSQUASH : (w : world) (I : Inh) (u : univs) (a b : Term)
  → # a → # b
  → eqTypes u I w (SQUASH a) (SQUASH b)
  → eqTypes u I w a b
ifeqTypesSQUASH w I u a b na nb (EQTNAT x x₁) = ⊥-elim (SETneqNAT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTQNAT x x₁) = ⊥-elim (SETneqQNAT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (SETneqLT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) = ⊥-elim (SETneqQLT (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTFREE x x₁) = ⊥-elim (SETneqFREE (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb) = ⊥-elim (SETneqPI (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb) = ⊥-elim (SETneqSUM (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb) =
  let e1 = compAllVal I x tt in
  let e2 = compAllVal I x₁ tt in
  let a1 = SETinj1 e1 in
  let a2 = SETinj2 e1 in
  let b1 = SETinj1 e2 in
  let b2 = SETinj2 e2 in
  {!!}
ifeqTypesSQUASH w I u a b na nb (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA eqt1 eqt2) = ⊥-elim (SETneqEQ (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB) = ⊥-elim (SETneqUNION (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTSQUASH A1 A2 x x₁ eqtA) = ⊥-elim (SETneqTSQUASH (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA eqx) = ⊥-elim (SETneqFFDEFS (compAllVal I x₁ tt))
ifeqTypesSQUASH w I u a b na nb (EQTUNIV x) = {!!}
ifeqTypesSQUASH w I u a b na nb (EQTBAR x) = {!!}
ifeqTypesSQUASH w I u a b na nb (EQTLOWER A1 A2 x x₁ eqt) = ⊥-elim (SETneqLOWER (compAllVal I x tt))
ifeqTypesSQUASH w I u a b na nb (EQTSHRINK A1 A2 x x₁ eqt) = ⊥-elim (SETneqSHRINK (compAllVal I x tt))

{--eqTypesac00 : (w : world) (j n : ℕ) → eqTypes (uni n) (inhN j) w (SQUASH ac) (SQUASH ac)
eqTypesac00 w j n = eqTypesSQUASH w (inhN j) (uni n) ac ac dumNotInac dumNotInac {!!}--}

{--eqInTypeac00 : (w : world) (j n : ℕ) (eqt : eqTypes (uni n) (inhN j) w (SQUASH ac) (SQUASH ac))
                → eqInType (uni n) (inhN j) w eqt AX AX
eqInTypeac00 w j n eqt = {!!}--}


{--eqintypeNSQUASH : (w : world) (u t : Term) (j k : ℕ) (d : # u)
                  → eqintypeN j k w (SQUASH u) AX AX
                  → eqintypeN j k w u t t
eqintypeNSQUASH w u t j 0 d e = {!!} --tt
eqintypeNSQUASH w u t j (suc k) d (n , (eqt , eqi)) = {!!}
--  (n , (ifeqTypesSQUASH w (inhN (suc j)) (uni n) u u d d eqt , {!!}))
--}

eqintypeSQUASH : (w : world) (u : Term) → (Σ Term (λ t → eqintype w u t t)) → eqintype w (SQUASH u) AX AX
eqintypeSQUASH w u (t , (n , e)) = {!!} -- (n , λ j c → let e' = e j c in {!!})

ifequalInTypePI : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                → equalInType u I w (PI A B) t₁ t₂
                → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂
                                    → equalInType u I w' (sub a₁ B) (APPLY t₁ a₁) (APPLY t₂ a₂))
ifequalInTypePI u I w A B t₁ t₂ eqi = {!!}

equalInTypePI : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                → equalTypes u I w A A
                → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalTypes u I w' (sub a₁ B) (sub a₂ B))
                → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalInType u I w' (sub a₁ B) (APPLY t₁ a₁) (APPLY t₂ a₂))
                → equalInType u I w (PI A B) t₁ t₂
equalInTypePI u I w A B t₁ t₂ eqta eqtb eqib = {!!}

equalInTypePIlam : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                   → equalTypes u I w A A
                   → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalTypes u I w' (sub a₁ B) (sub a₂ B))
                   → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalInType u I w' (sub a₁ B) (sub a₁ t₁) (sub a₂ t₂))
                   → equalInType u I w (PI A B) (LAMBDA t₁) (LAMBDA t₂)
equalInTypePIlam u I w A B t₁ t₂ eqta eqtb eqib = {!!}

equalInTypeSQUASH : (u : ℕ) (I : Inh) (w : world) (T : Term)
                    → inOpenBar I w (λ w1 e1 → Σ Term (λ t → equalInType u I w1 T t t))
                    → equalInType u I w (SQUASH T) AX AX
equalInTypeSQUASH u I w T h = {!!}

ifequalInTypeSQUASH : (u : ℕ) (I : Inh) (w : world) (T a b : Term)
                      → equalInType u I w (SQUASH T) a b
                      → inOpenBar I w (λ w1 e1 → Σ Term (λ t → equalInType u I w1 T t t))
ifequalInTypeSQUASH u I w T a b h = {!!}

equalInTypeSUM : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (a₁ b₁ a₂ b₂ : Term)
                 → allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType u I w' A a₁ a₂ → equalTypes u I w' (sub a₁ B) (sub a₂ B))
                 → equalInType u I w A a₁ a₂
                 → equalInType u I w (sub a₁ B) b₁ b₂
                 → equalInType u I w (SUM A B) (PAIR a₁ b₁) (PAIR a₂ b₂)
equalInTypeSUM u I w A B a₁ b₁ a₂ b₂ eqtb eqa eqb = {!!}

ifequalInTypeSUM : (u : ℕ) (I : Inh) (w : world) (A : Term) (B : Term) (t₁ t₂ : Term)
                 → equalInType u I w (SUM A B) t₁ t₂
                 → inOpenBar I w (λ w' e → Σ Term (λ a₁ → Σ Term (λ a₂ → Σ Term (λ b₁ → Σ Term (λ b₂ →
                         # a₁ × # a₂ × # b₁ × # b₂
                         × [ I ] t₁ ⇛ (PAIR a₁ b₁) at w'
                         × [ I ] t₂ ⇛ (PAIR a₂ b₂) at w'
                         × equalInType u I w' A a₁ a₂
                         × equalInType u I w' (sub a₁ B) b₁ b₂)))))
ifequalInTypeSUM u I w A B t₁ t₂ (eqt , eqi) = {!!}

ifequalInTypeNAT : (u : ℕ) (I : Inh) (w : world) (t₁ t₂ : Term)
                → equalInType u I w NAT t₁ t₂
                → inOpenBar I w (λ w1 e1 → strongMonEq I w1 t₁ t₂)
ifequalInTypeNAT u I w t₁ t₂ e = {!!}

{--
-- This one should be a "Type System" property
compPreservesEqualInTypeLeft : (u : univs) (I : Inh) (w : world) (A a b c : Term)
                               → [ I ] a ⇛ c at w
                               → equalInType u I w A a b
                               → equalInType u I w A c b
compPreservesEqualInTypeLeft u I w A a b c comp e = {!!}

-- This one should be a "Type System" property
compPreservesEqualInTypeRight : (u : univs) (I : Inh) (w : world) (A a b c : Term)
                                → [ I ] a ⇛ c at w
                                → equalInType u I w A a b
                                → equalInType u I w A a c
compPreservesEqualInTypeRight u I w A a b c comp e = {!!}
--}

--proj₁ (snd (uni u)) I w (LOWER T) (LOWER T)


impliesEqualInTypeLowerBar : (u : ℕ) (I : Inh) (w : world) (T a₁ a₂ : Term)
                             → inOpenBar I w (λ w' _ → allI (lower I) (λ i → equalInType u i w' T a₁ a₂))
                             → equalInType u I w (LOWER T) a₁ a₂
impliesEqualInTypeLowerBar u I w T a₁ a₂ e = {!!}
  {--equalInTypeBar
    u I w (LOWER T) a₁ a₂
    (λ w1 e1 → let (w2 , (e2 , z)) = e w1 e1 in (w2 , (e2 , λ w3 e3 →
      {!!} {--impliesEqualInTypeLower u I w3 T a₁ a₂ (λ w4 e4 → z w4 ([]≽-trans {I} e4 e3))--} )))
--}


ifequalInTypeacHypPiAux2 : (u : ℕ) (I : Inh) (w2 w1 : world) (p x₁ x₂ y₁ y₂ : Term) (n : ℕ)
                           → # p → # x₁ → # x₂ → # y₁ → # y₂
                           → [ I ] w2 ⪰ w1
                           → equalInType u I w2 LNAT x₁ x₂
                           → equalInType u I w2 (LAPPLY2 p (NUM n) x₁) y₁ y₂
                           → exW I w1
                                 (λ w3 e3 →
                                   allW I w3
                                     (λ w4 e4 → Σ Term (λ m → Σ Term (λ t →
                                                 # m × # t
                                                 × equalInType u I w4 LNAT m m
                                                 × equalInType u I w4 (LAPPLY2 p (NUM n) m) t t))))
ifequalInTypeacHypPiAux2 u I w2 w1 p x₁ x₂ y₁ y₂ n cp cx₁ cx₂ cy₁ cy₂ ext eqi1 eqi2 =
  (w2 , ext ,
   λ w3 e3 → (x₁ , y₁ , cx₁ , cy₁ ,
     equalInType-mon u LNAT x₁ x₁ I w2 (equalInType-refl eqi1) w3 e3 ,
     equalInType-mon u (LAPPLY2 p (NUM n) x₁) y₁ y₁ I w2 (equalInType-refl eqi2) w3 e3))

ifequalInTypeacHypPiAux1 : (u : ℕ) (I : Inh) (w2 w1 : world) (p t₁ t₂ : Term) (n : ℕ)
                           → # p
                           → [ I ] w2 ⪰ w1
                           → equalInType u I w2 (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0))) t₁ t₂
                           → exW I w1
                                 (λ w3 e3 →
                                   allW I w3
                                     (λ w4 e4 → Σ Term (λ m → Σ Term (λ t →
                                                 # m × # t
                                                 × equalInType u I w4 LNAT m m
                                                 × equalInType u I w4 (LAPPLY2 p (NUM n) m) t t))))
ifequalInTypeacHypPiAux1 u I w2 w1 p t₁ t₂ n cp ext eqi =
  let (w3 , e3 , eqi1) = ifequalInTypeSUM u I w2 _ _ _ _ eqi w2 ([]≽-refl I w2) in
  let (x₁ , x₂ , y₁ , y₂ , cx₁ , cx₂ , cy₁ , cy₂ , c₁ , c₂ , eqi2 , eqi3) = eqi1 w3 ([]≽-refl I w3) in
  let eqi4 = equalInTypesubLAPPLY2 {u} {I} {w3} {p} {x₁} cp eqi3 in
  ifequalInTypeacHypPiAux2 u I w3 w1 p x₁ x₂ y₁ y₂ n cp cx₁ cx₂ cy₁ cy₂ ([]≽-trans {I} e3 ext) eqi2 eqi4

ifequalInTypeacHypPi : (u : ℕ) (I : Inh) (w : world) (p a₁ a₂ : Term) → # p → # a₁ → # a₂
                       → equalInType u I w (acHypPi p) a₁ a₂
                       → (n : ℕ)
                       → inOpenBar I w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × equalInType u I w1 LNAT m m
                                                   × equalInType u I w1 (LAPPLY2 p (NUM n) m) t t)))
ifequalInTypeacHypPi u I w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 =
  let eqi1 = ifequalInTypePI
               u I w NAT (SQUASH (SUM LNAT (LAPPLY2 p (VAR 2) (VAR 0)))) a₁ a₂ eqi
               w1 e1 (NUM n) (NUM n) (closedNum n) (closedNum n)
               (numInNAT u I w1 n) in
  let eqi2 = subst (λ x → equalInType u I w1 x (APPLY a₁ (NUM n)) (APPLY a₂ (NUM n)))
                  (sub-NUM-SQUASH-SUM n p cp) eqi1 in
  let (w2 , (e2 , eqi3)) = ifequalInTypeSQUASH u I w1
                             (SUM LNAT (LAPPLY2 p (NUM n) (VAR 0)))
                             (APPLY a₁ (NUM n)) (APPLY a₂ (NUM n))
                             eqi2 w1 ([]≽-refl I w1) in
  let (t , eqi4) = eqi3 w2 ([]≽-refl I w2) in
  ifequalInTypeacHypPiAux1 u I w2 w1 p t t n cp e2 eqi4

ifequalInTypeacHypPi2 : (u : ℕ) (I : Inh) (w : world) (p a₁ a₂ : Term) → # p → # a₁ → # a₂
                       → equalInType u I w (acHypPi p) a₁ a₂
                       → (n : ℕ)
                       → inOpenBar I w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × allI (lower I) (λ i → equalInType u i w1 NAT m m)
                                                   × allI (lower I) (λ i → equalInType u i w1 (APPLY2 p (NUM n) m) t t))))
ifequalInTypeacHypPi2 u I w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 =
  let (w2 , e2 , h) = ifequalInTypeacHypPi u I w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 in
  let (m , t , cm , ct , eqn , eqa) = h w2 ([]≽-refl I w2) in
  let (w3 , e3 , eqn1) = equalInTypeLower u I w2 NAT m m eqn w2 ([]≽-refl I w2) in
  let eqa1 = equalInType-mon u (LAPPLY2 p (NUM n) m) t t I w2 eqa w3 e3 in
  let (w4 , e4 , eqa2) = equalInTypeLower u I w3 (APPLY2 p (NUM n ) m) t t eqa1 w3 ([]≽-refl I w3) in
  (w4 , []≽-trans {I} e4 ([]≽-trans {I} e3 e2) ,
    λ w5 e5 →
      m , t , cm , ct ,
      eqn1 w5 ([]≽-trans {I} e5 e4) ,
      eqa2 w5 e5)

ifequalInTypeacHypPi3 : (u j : ℕ) (w : world) (p a₁ a₂ : Term) → # p → # a₁ → # a₂
                       → equalInType u (inhN2Ls u j) w (acHypPi p) a₁ a₂
                       → (n : ℕ)
                       → inOpenBar (inhN2Ls u j) w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × allI (inhN2L u j) (λ i → equalInType u i w1 NAT m m)
                                                   × allI (inhN2L u j) (λ i → equalInType u i w1 (APPLY2 p (NUM n) m) t t))))
ifequalInTypeacHypPi3 u j w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 =
  let (w2 , e2 , h) = ifequalInTypeacHypPi2 u (inhN2Ls u j) w p a₁ a₂ cp ca₁ ca₂ eqi n w1 e1 in
  (w2 , e2 , λ w3 e3 → let (m , t , cm , ct , eqn , eqa) = h w3 e3 in
                        (m , t , cm , ct ,
                         allI-lower-inhN2Ls {u} {j} {λ x → equalInType u x w3 NAT m m} eqn ,
                         allI-lower-inhN2Ls {u} {j} {λ x → equalInType u x w3 (APPLY2 p (NUM n) m) t t} eqa ))


{--inh2L-suc-eq : (u j : ℕ) (c₁ : j ≤ suc j) (c₂ : suc j ≤ suc j) (w : world) (T : Term)
      → snd (snd (inhN2L u j)) (suc j) c₁ c₂ w T ≡ Σ Term (λ t → eqintypeN u j j w T t t)
inh2L-suc-eq u j c₁ c₂ w T with m≤n⇒m<n∨m≡n c₂
... | inj₁ p = ⊥-elim (1+n≰n p)
... | inj₂ p = refl--}

{--equalInType-topInh-inhN2L : (u : ℕ) (j : ℕ) (w : world) (T t : Term)
                            → equalInType u (inhN1L u j) w T t t
                            → topInh (inhN2L u j) w T
equalInType-topInh-inhN2L u j w T t h rewrite inh2L-suc-eq u j ≤-refl w T = (t , h)

equalInType-inhN2L-topInh : (u : ℕ) (j : ℕ) (w : world) (T : Term)
                            → topInh (inhN2L u j) w T
                            → Σ Term (λ t → equalInType u (inhN1L u j) w T t t)
equalInType-inhN2L-topInh u j w T h rewrite inh2L-suc-eq u j ≤-refl w T = h--}

equalInTypeMEM : (i : ℕ) (I : Inh) (w : world) (A a : Term)
                 → equalInType i I w A a a
                 → equalInType i I w (MEM a A) AX AX
equalInTypeMEM i I w A a (eqt , eqi) =
  EQTEQ a a a a A A (compAllRefl I (MEM a A) w) (compAllRefl I (MEM a A) w)
    (eqTypes-mon (uni i) A A I w eqt)
    {!!} {!!} ,
  {!!}

implies-equalInType-AND-MEM : (i : ℕ) (I : Inh) (w : world) (A B a b : Term) → # B
                              → equalInType i I w A a a
                              → equalInType i I w B b b
                              → equalInType i I w (AND (MEM a A) B) (PAIR AX b) (PAIR AX b)
implies-equalInType-AND-MEM i I w A B a b cB ea eb = equalInTypeSUM i I w (MEM a A) B AX b AX b aw1 ea1 eb1
  where
    aw1 : allW I w (λ w' _ → (a₁ a₂ : Term) → # a₁ → # a₂ → equalInType i I w' (MEM a A) a₁ a₂ → equalTypes i I w' (sub a₁ B) (sub a₂ B))
    aw1 w' e' a₁ a₂ ca₁ ca₂ ea1 rewrite subNotIn a₁ B cB | subNotIn a₂ B cB =
      equalTypes-mon i B B I w (proj₁ eb) w' e'

    ea1 : equalInType i I w (MEM a A) AX AX
    ea1 = equalInTypeMEM i I w A a ea

    eb1 : equalInType i I w (sub AX B) b b
    eb1 rewrite subNotIn AX B cB = eb

inhm-inhN2Ls : (u j : ℕ) → Inh.m (inhN2Ls u j) ≡ suc j
inhm-inhN2Ls u j = refl

inh-f-inhN2Ls : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
                → Σ Term (λ t → equalInType u (inhN u (suc j) (pred i)) w T t t)
                → Inh.f (inhN2Ls u j) (Inh.m (inhN2Ls u j)) i c₂ w T
inh-f-inhN2Ls u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls u j i c₁ c₂ w T h | inj₂ p rewrite p = h

inh-f-inhN2Ls-pred : (u j i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
                → Σ Term (λ t → equalInType u (inhN u j (pred i)) w T t t)
                → Inh.f (inhN2Ls u j) (pred (Inh.m (inhN2Ls u j))) i c₂ w T
inh-f-inhN2Ls-pred u j i c₁ c₂ w T h with m≤n⇒m<n∨m≡n c₂
... | inj₁ p with m≤n⇒m<n∨m≡n (sucLeInj p)
...          | inj₁ q = ⊥-elim (¬s≤ _ (≤-trans q c₁))
...          | inj₂ q rewrite q = h
inh-f-inhN2Ls-pred u j i c₁ c₂ w T h | inj₂ p rewrite p = h

s≤-≤pred : {i j : ℕ} → suc j ≤ i → j ≤ pred i
s≤-≤pred {suc i} {j} (_≤_.s≤s h) = h

≤0-≡0 : {j : ℕ} → j ≤ 0 → j ≡ 0
≤0-≡0 {.0} _≤_.z≤n = refl

pred≤pred : {i j : ℕ} → j ≤ i → pred j ≤ pred i
pred≤pred {i} {0} h = _≤_.z≤n
pred≤pred {suc i} {suc j} (_≤_.s≤s h) = h

between2 : {i j : ℕ} (c₁ : j ≤ i) (c₂ : i ≤ suc j) → i ≡ j ⊎ i ≡ (suc j)
between2 {.0} {j} c₁ _≤_.z≤n = inj₁ (sym (≤0-≡0 c₁))
between2 {suc k} {0} c₁ (_≤_.s≤s c₂) rewrite (≤0-≡0 c₂) = inj₂ refl
between2 {suc k} {suc j} c₁ (_≤_.s≤s c₂) with between2 (sucLeInj c₁) c₂
... | inj₁ p rewrite p = inj₁ refl
... | inj₂ p rewrite p = inj₂ refl

inhL-pred : (u i j m i0 : ℕ) (c : i0 ≤ pred i) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) (w : world) (T : Term)
            → inhL u m (pred i) i0 c w T ≡ Inh.f (inhN2L u j) m i0 (≤-trans c (pred≤pred c₂)) w T
inhL-pred u i j m i0 c c₁ c₂ w T with between2 c₁ c₂ | m≤n⇒m<n∨m≡n (≤-trans c (pred≤pred c₂))
... | inj₁ p | inj₁ q rewrite p | ≤-irrelevant (sucLeInj q) c = refl
... | inj₁ p | inj₂ q rewrite p | q = ⊥-elim (¬s≤ _ c)
... | inj₂ p | inj₁ q rewrite p with m≤n⇒m<n∨m≡n c
...                                | inj₁ r rewrite ≤-irrelevant (sucLeInj r) (sucLeInj q) = refl
...                                | inj₂ r rewrite r = ⊥-elim (¬s≤ _ q)
inhL-pred u i j m i0 c c₁ c₂ w T | inj₂ p | inj₂ q rewrite p | q with m≤n⇒m<n∨m≡n c
... | inj₁ r = ⊥-elim (¬s≤ _ r)
... | inj₂ r = refl


-- NOTE: we wouldn't be able to prove this if we had to prove [_]_⪰_ for all lower inhabitations too
exW≤lengthAux3 : (u : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (m p t : Term) → # p → # m
                 → allI (inhN2L u j) (λ i → equalInType u i w NAT m m)
                 → allI (inhN2L u j) (λ i → equalInType u i w (APPLY2 p (NUM (length l)) m) t t)
                 → ∈world (mkcs name l (acres p)) w
                 → [ inhN2Ls u j ] (extcs w name m) ⪰ w
exW≤lengthAux3 u j w name l m p t cp cm eqn eqa iw = extChoice w name l m (acres p) iw ai
  where
    eqi : (i j : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) → inhN u j (pred i) ≡ mkinh (Inh.m (inhN2L u j)) (pred i) (λ m₁ i₁ c → Inh.f (inhN2L u j) m₁ i₁ (≤-trans c (pred≤pred c₂)))
    eqi i j c₁ c₂ = eq-mkinh (fext (λ m → fext (λ i0 → fext (λ c → fext (λ w → fext (λ T → inhL-pred u i j m i0 c c₁ c₂ w T))))))

    eqn' : (i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) → equalInType u (inhN u j (pred i)) w NAT m m
    eqn' i c₁ c₂ rewrite eqi i j c₁ c₂ = eqn (pred i) (s≤-≤pred c₁) (pred≤pred c₂)

    eqa' : (i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j)) → equalInType u (inhN u j (pred i)) w (APPLY2 p (NUM (length l)) m) t t
    eqa' i c₁ c₂ rewrite eqi i j c₁ c₂ = eqa (pred i) (s≤-≤pred c₁) (pred≤pred c₂)

    ea : (i : ℕ) (c₁ : suc j ≤ i) (c₂ : i ≤ suc (suc j))
         → equalInType u (inhN u j (pred i)) w (acres p (length l) m) (PAIR AX t) (PAIR AX t)
    ea i c₁ c₂ =
      implies-equalInType-AND-MEM
        u (inhN u j (pred i)) w NAT (APPLY2 p (NUM (length l)) m) m t
        (#APPLY2-NUM p m (length l) cp cm)
        (eqn' i c₁ c₂) (eqa' i c₁ c₂)

    ai : allIW (inhN2Ls u j) (λ i₁ → i₁ w (acres p (length l) m))
    ai i c₁ c₂ = inh-f-inhN2Ls-pred u j i c₁ c₂ w (acres p (length l) m) (PAIR AX t , ea i c₁ c₂)
-- TODO: 'lower' should lower the whole interval...

exW≤lengthAux2 : (u : ℕ) (j : ℕ) (w w' : world) (name : csName) (l1 l2 : List Term) (k : ℕ) (m p t : Term)
                 → # p → # m → k ≤ length l1
                 → allI (inhN2L u j) (λ i → equalInType u i w' NAT m m)
                 → allI (inhN2L u j) (λ i → equalInType u i w' (APPLY2 p (NUM (length l1)) m) t t)
                 → ∈world (mkcs name (l1 ++ l2) (acres p)) w'
                 → [ inhN2Ls u j ] w' ⪰ w
                 → exW (inhN2Ls u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × suc k ≤ length l'))
exW≤lengthAux2 u j w w' name l1 [] k m p t cp cm len en ea iw ext rewrite ++[] l1 =
  let w1 = extcs w' name m in
  let e1 : [ inhN2Ls u j ] w1 ⪰ w'
      e1 = exW≤lengthAux3 u j w' name l1 m p t cp cm en ea iw in
  let len' : ∈world (mkcs name (l1 ∷ʳ m) (acres p)) w1
      len' = ∈world-extcs w' name l1 (acres p) m iw in
  let le' : suc k ≤ length (l1 ∷ʳ m)
      le' = suc≤len∷ʳ l1 m k len in
  (w1 , []≽-trans {inhN2Ls u j} e1 ext , l1 ∷ʳ m , len' , le')
exW≤lengthAux2 u j w w' name l1 (x ∷ l2) k m p t cp cm len en ea iw ext =
  (w' , ext , l1 ++ x ∷ l2 , iw ,
    subst (λ x → suc k ≤ x) (sym (length-++ l1 {x ∷ l2}))
      (subst (λ x → suc k ≤ x) (sym (+-suc (length l1) (length l2)))
        (_≤_.s≤s (≤-stepsʳ (length l2) len))))

exW≤lengthAux1 : (u : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (k : ℕ) (p a₁ a₂ : Term)
                 → # p → # a₁ → # a₂
                 → ∈world (mkcs name l (acres p)) w
                 → ((n : ℕ) → inOpenBar (inhN2Ls u j) w (λ w1 e1 → Σ Term (λ m → Σ Term (λ t →
                                                   # m × # t
                                                   × allI (inhN2L u j) (λ i → equalInType u i w1 NAT m m)
                                                   × allI (inhN2L u j) (λ i → equalInType u i w1 (APPLY2 p (NUM n) m) t t)))))
                 → exW (inhN2Ls u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
exW≤lengthAux1 u j w name l 0 p a₁ a₂ cp ca₁ ca₂ i e = (w , []≽-refl (inhN2Ls u j) w , l , i , _≤_.z≤n)
exW≤lengthAux1 u j w name l (suc k) p a₁ a₂ cp ca₁ ca₂ i e =
  let (w1 , e1 , l1 , i1 , len) = exW≤lengthAux1 u j w name l k p a₁ a₂ cp ca₁ ca₂ i e in
  let (w2 , e2 , h2) = e (length l1) w1 e1 in
  let (m , t , cm , ct , eqn , eqa) = h2 w2 ([]≽-refl (inhN2Ls u j) w2) in
  let (l2 , i2) = []≽-pres-∈world {inhN2Ls u j} e2 i1 in
  exW≤lengthAux2 u j w w2 name l1 l2 k m p t cp cm len eqn eqa i2 ([]≽-trans {inhN2Ls u j} e2 e1)


exW≤length : (u : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (k : ℕ) (p a₁ a₂ : Term)
             → # p → # a₁ → # a₂
             → ∈world (mkcs name l (acres p)) w
             → equalInType u (inhN2Ls u j) w (acHypPi p) a₁ a₂
             → exW (inhN2Ls u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
exW≤length u j w name l k p a₁ a₂ cp ca₁ ca₂ i e =
  let h = ifequalInTypeacHypPi3 u j w p a₁ a₂ cp ca₁ ca₂ e in
  exW≤lengthAux1 u j w name l k p a₁ a₂ cp ca₁ ca₂ i h

exW≤length2 : (u : ℕ) (j : ℕ) (w : world) (name : csName) (l : List Term) (k : ℕ) (p a₁ a₂ : Term)
             → # p → # a₁ → # a₂
             → ∈world (mkcs name l (acres p)) w
             → equalInType u (inhN2Ls u j) w (acHypPi p) a₁ a₂
             → exAllW (inhN2Ls u j) w (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
exW≤length2 u j w name l k p a₁ a₂ cp ca₁ ca₂ i e =
  let (w1 , e1 , l1 , i1 , len1) = exW≤length u j w name l k p a₁ a₂ cp ca₁ ca₂ i e in
  (w1 , e1 , λ w2 e2 →
     let (l2 , i2) = []≽-pres-∈world {inhN2Ls u j} e2 i1 in
     (l1 ++ l2 , i2 , subst (λ x → k ≤ x) (sym (length-++ l1 {l2})) (≤-stepsʳ (length l2) len1)))

foo : (u j i : ℕ) (w : world) (t : Term) (c₁ : j ≤ i) (c₂ : i ≤ suc j)
      → allIW (inhN2Ls u j) (λ i → i w t)
      → Σ Term (λ z → equalInType u (inhN u j i) w t z z)
foo u j i w t c₁ c₂ h = let h' = h i in {!!}


equalInTypeNAT-APPLY-CS : (u j k : ℕ) (w2 w1 : world) (name : csName) (l : List Term) (p a b : Term)
                          → ¬ (name ∈ (wdom w1))
                          → ∈world (mkcs name l (acres p)) w2
                          → k < length l
                          → [ inhN2Ls u j ] w2 ⪰ (newcs w1 name (acres p))
                          → [ inhN2Ls u j ] b ⇛ NUM k at w2
                          → [ inhN2Ls u j ] a ⇛ NUM k at w2
                          → allI (inhN2L u j) (λ i → equalInType u i w2 NAT (APPLY (CS name) a) (APPLY (CS name) b))
equalInTypeNAT-APPLY-CS u j k w2 w1 name l p a b niw iw len ext c₁ c₂ i0 i0₁ i0₂ = {!!}
  where
    h : Σ Term (λ t → Σ world (λ w → Σ (List Term) (λ l →
                       getChoice k name (extcs w name t) ≡ just t
                     × ∈world (mkcs name l (acres p)) w
                     × k ≡ length l
                     × [ inhN2Ls u j ] w2 ⪰ extcs w name t
                     × [ inhN2Ls u j ] w ⪰ newcs w1 name (acres p)
                     × allIW (inhN2Ls u j) (λ i → i w (acres p k t)))))
    h = []≽-ΣgetChoice (inhN2Ls u j) w1 w2 name l (acres p) k niw ext len iw

    t : Term
    t = proj₁ h

    w : world
    w = proj₁ (proj₂ h)

    l1 : List Term
    l1 = proj₁ (proj₂ (proj₂ h))

    gc : getChoice k name (extcs w name t) ≡ just t
    gc = proj₁ (proj₂ (proj₂ (proj₂ h)))

    iw1 : ∈world (mkcs name l1 (acres p)) w
    iw1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ h))))

    kel : k ≡ length l1
    kel = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ h)))))

    ext1 : [ inhN2Ls u j ] w2 ⪰ extcs w name t
    ext1 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ h))))))

    ext2 : [ inhN2Ls u j ] w ⪰ newcs w1 name (acres p)
    ext2 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ h)))))))

    r1 : allIW (inhN2Ls u j) (λ i → i w (acres p k t))
    r1 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ h)))))))

--  let (t , w , l1 , gc , iw , kel , ext1 , ext2 , r) =  in
--  let (t1 , r1) = equalInType-inhN2L-topInh u j w (acres p k t) r in
--  {!!}

equalInTypeCS : (u j k : ℕ) (w w1 w2 : world) (p a b a₁ a₂ : Term) (name : csName)
                → # p → # a₁ → # a₂
                → ¬ (name ∈ (wdom w1))
                → [ inhN2Ls u j ] a ⇛ NUM k at w2
                → [ inhN2Ls u j ] b ⇛ NUM k at w2
                → [ inhN2Ls u j ] (newcs w1 name (acres p)) ⪰ w
                → [ inhN2Ls u j ] w2 ⪰ (newcs w1 name (acres p))
                → equalInType u (inhN2Ls u j) w (acHypPi p) a₁ a₂
                → equalInType u (inhN2Ls u j) w2 (LOWER NAT) (APPLY (CS name) a) (APPLY (CS name) b)
equalInTypeCS u j k w w1 w2 p a b a₁ a₂ name cp ca₁ ca₂ niw c₁ c₂ e₁ e₂ eqh =
  impliesEqualInTypeLowerBar
    u (inhN2Ls u j) w2 NAT (APPLY (CS name) a) (APPLY (CS name) b) ea1
  where
    iw : ∈world (mkcs name [] (acres p)) (newcs w1 name (acres p))
    iw = ∈world-newcs w1 name (acres p) niw

    ea1 : inOpenBar (inhN2Ls u j) w2
                    (λ w' _ → allI (lower (inhN2Ls u j)) (λ i → equalInType u i w' NAT (APPLY (CS name) a) (APPLY (CS name) b)))
    ea1 w3 e3 = (w4 , e4 , ea2)
      where
        iw2 : Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w3)
        iw2 = []≽-pres-∈world {inhN2Ls u j} ([]≽-trans {inhN2Ls u j} e3 e₂) iw

        l2 : List Term
        l2 = fst iw2

        i2 : ∈world (mkcs name l2 (acres p)) w3
        i2 = snd iw2

        h : exAllW (inhN2Ls u j) w3 (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
        h = exW≤length2
             u j w3 name l2 k p a₁ a₂ cp ca₁ ca₂ i2
             (equalInType-mon u (acHypPi p) a₁ a₂ (inhN2Ls u j) w eqh w3 ([]≽-trans {inhN2Ls u j} e3 ([]≽-trans {inhN2Ls u j} e₂ e₁)))

        w4 : world
        w4 = proj₁ h

        e4 : [ inhN2Ls u j ] w4 ⪰ w3
        e4 = proj₁ (proj₂ h)

        h1 : allW (inhN2Ls u j) w4 (λ w' e' → Σ (List Term) (λ l' → ∈world (mkcs name l' (acres p)) w' × k ≤ length l'))
        h1 = proj₂ (proj₂ h)

        ea2 : allW (inhN2Ls u j) w4
                   (λ w' _ → allI (lower (inhN2Ls u j)) (λ i → equalInType u i w' NAT (APPLY (CS name) a) (APPLY (CS name) b)))
        ea2 w5 e5 = {!!} -- rewrite (lower-inhN2Ls u j) = {!!}

{--
    let i1 = ∈world-newcs w1 name (acres p) niw in
    λ w3 e3 →
    let (l2 , i2) = []≽-pres-∈world {inhN2Ls u j} ([]≽-trans {inhN2Ls u j} e3 e₂) i1 in
    let (w4 , e4 , h) = exW≤length2 u j w3 name l2 k p a₁ a₂ cp ca₁ ca₂ i2
                          {--(equalInType-mon u (acHypPi p) a₁ a₂ (inhN2L u j) w eqh w3
                            ([]≽-trans {inhN2H u j} e3 ([]≽-trans {inhN2L u j} e₂ e₁)))--} {!!} in
    (w4 , e4 , λ w5 e5 → let (l , iw , len) = h w5 e5 in {!!})
--}
-- TODO: we need c₁ and c₂ to be true in this INH and the lower one too to make use of them in the lower one in the conclusion
--   -> introduce a squashing operator for that?

 {--let eqh1 = equalInTypeLower (uni 0) j w (acHypPi p) a₁ a₂ eqh in
    λ w1 e1 → let (w2 , e2 , eqh2) = eqh1 w1 ([]≽-trans e1 ([]≽-trans e₂ e₁)) in
    (w2 , e2 , λ w3 e3 →
    let eqh3 = eqh2 w3 e3 in
    {!!} {--equalInTypeNAT
      (uni 0) (inhN1L j) w3 (APPLY (CS name) a) (APPLY (CS name) b)
      {!!}--})--}
-- We need to update 'ext' to include all inh not just the top one

{--
equalInTypeCS : (j k : ℕ) (w w1 w2 : world) (p a b a₁ a₂ : Term) (name : choiceSeqName)
                → [ inhNs j ] a ⇛ NUM k at w2
                → [ inhNs j ] b ⇛ NUM k at w2
                → [ inhNs j ] (mkentry name [] (acres p) ∷ w1) ⪰ w
                → [ inhNs j ] w2 ⪰ (mkentry name [] (acres p) ∷ w1)
                → equalInType (uni 0) (inhNs j) w (acHypP p) a₁ a₂
                → equalInType (uni 0) (inhNs j) w2 NAT (APPLY (CS name) a) (APPLY (CS name) b)
equalInTypeCS j k w w1 w2 p a b a₁ a₂ name c₁ c₂ e₁ e₂ eqh =
  equalInTypeNAT
    (uni 0) (inhNs j) w2 (APPLY (CS name) a) (APPLY (CS name) b)
    let eqh1 = equalInTypeLower (uni 0) j w (acHypPi p) a₁ a₂ eqh in
    λ w3 e3 →
      let eqh2 = eqh1 w3 (eTrans e3 (eTrans e₂ e₁)) in
      {!!} -- Now we have to extend the world with entries up to 'k'
            -- We also have to lower the NAT
--}


ac00trueAux2 : (u j : ℕ) (w : world) (p₁ p₂ : Term) → # p₁ → # p₂ → (a₁ a₂ : Term) → # a₁ → # a₂
               → equalInType u (inhN2L u j) w NATbinPred p₁ p₂
               → equalInType u (inhN2L u j) w (acHypPi p₁) a₁ a₂
               → equalInType u (inhN2L u j) w (acConclP p₁) AX AX
ac00trueAux2 u j w p₁ p₂ cp₁ cp₂ a₁ a₂ ca₁ ca₂ eqp eqa =
  equalInTypeSQUASH
    u (inhN2L u j) w (acConclSum p₁)
    λ w1 e1 →
      let name : csName
          name = proj₁ (freshName (wdom w1)) in
      let res : restriction
          res = acres p₁ in
      let w2 : world
          w2 = newcs w1 name res in
      let e2 : [ inhN2L u j ] w2 ⪰ w1
          e2 = []≽newcs (inhN2L u j) w1 name res (proj₂ (freshName (wdom w1))) in
      (w2 , (e2 , λ w3 e3 → (PAIR (CS name) (LAMBDA AX) ,
        equalInTypeSUM
          u (inhN2L u j) w3 LBAIRE (PI NAT (LAPPLY2 p₁ (VAR 0) (APPLY (VAR 1) (VAR 0))))
          _ _ _ _
          {!!}
          (equalInTypePI
            u (inhN2L u j) w3 NAT LNAT (CS name) (CS name)
            (eqTypesNAT w3 (inhN2L u j) (uni u))
            (λ w4 e4 a₃ a₄ ca₃ ca₄ eqt → {!!})
            (λ w4 e4 a₃ a₄ ca₃ ca₄ eqt →
              let z = ifequalInTypeNAT _ _ _ _ _ eqt in
              subst (λ x → equalInType u (inhN2L u j) w4 x
                                        (APPLY (CS (proj₁ (freshName (wdom w1)))) a₃)
                                        (APPLY (CS (proj₁ (freshName (wdom w1)))) a₄))
                    (sym (subLNAT a₃))
                    {!!} {--(equalInTypeBar
                       _ _ _ _ _ _
                       (inOpenBarMP
                         (inhN2L j) w4
                         (λ w5 e5 → strongMonEq (inhN2L j) w5 a₃ a₄)
                         (λ w' _ → equalInType (uni 0) (inhN2L j) w' NAT (APPLY (CS name) a₃) (APPLY (CS name) a₄))
                         (λ w5 e5 (k , (m1 , m2)) → {!!})
                         z))--}))
          {!!})))
-- We need to know that the restriction is realizable. How do we do that?
-- Or is that just going to come from the assumption (eqa)?

ac00trueAux1 : (u j : ℕ) (w : world) (p₁ p₂ : Term) → # p₁ → # p₂
               → equalInType u (inhN2L u j) w NATbinPred p₁ p₂
               → equalInType u (inhN2L u j) w (FUN (acHypPi p₁) (acConclP p₁)) lamAX lamAX
ac00trueAux1 u j w p₁ p₂ c₁ c₂ eqt =
  equalInTypePIlam u (inhN2L u j) w (acHypPi p₁) (acConclP p₁) AX AX
  {!!} {!!}
  (λ w1 e1 a₁ a₂ ca₁ ca₂ eqh →
    subst
      (λ x → equalInType u (inhN2L u j) w1 (sub a₁ (acConclP p₁)) x (sub a₂ AX))
      (sym (subAX a₁))
      (subst
        (λ x → equalInType u (inhN2L u j) w1 (sub a₁ (acConclP p₁)) AX x)
        (sym (subAX a₂))
        (subst
          (λ x → equalInType u (inhN2L u j) w1 x AX AX)
          (sym (subNotIn a₁ (acConclP p₁) (closedacConclP p₁ c₁)))
          {!!})))

ac00true : (w : world) → eqintype w ac acext acext
ac00true w =
  (0 , 1 , 1 ,
   λ { 0 ()
     ; j cj →
       equalInTypePIlam
           0 (inhN2L 0 j) w NATlbinPred acFun lamAX lamAX
           {!!} {!!}
           (λ w1 e1 p₁ p₂ c₁ c₂ i →
              subst
                (λ x → equalInType 0 (inhN2L 0 j) w1 (sub p₁ acFun) x (sub p₂ lamAX))
                (sym (sublamAX p₁))
                (subst
                  (λ x → equalInType 0 (inhN2L 0 j) w1 (sub p₁ acFun) lamAX x)
                  (sym (sublamAX p₂))
                  (subst
                    (λ x → equalInType 0 (inhN2L 0 j) w1 x lamAX lamAX)
                    (sym (subacFun p₁ c₁))
                    {!!}))) }
  )

{--case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x--}

{--lemma4 : (w : world) → ¬ (eqintype w (UNIV 1) (UNIV 1) (UNIV 1))
lemma4 w =  λ p →  case p of λ { ( n , (a , b) ) → {!!}}--}
\end{code}
