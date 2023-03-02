\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower ; _⊔_) renaming (suc to lsuc)
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
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
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
open import Function.Bundles
open import Axiom.UniquenessOfIdentityProofs
open import Axiom.Extensionality.Propositional

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import getChoice
open import newChoice
open import choiceExt
open import mod
open import bar


-- TODO: Progress is not required here
module forcing {n : Level} (m : Level) (W : PossibleWorlds {n}) (M : Mod m W) --(B : BarsProps W) --
               (C : Choice) (K : Compatible W C) (P : Progress W C K) (G : GetChoice W C K)
               (X : ChoiceExt W C)
               (N : NewChoice W C K G)
--               (B : BarsProps W)
               (E : Extensionality 0ℓ (lsuc (lsuc n) ⊔ lsuc (lsuc m)))
       where
open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
--open import mod(W) --bar(W)
open import barI(m)(W)(M)--{--(barI)--}(C)(K)(P)

\end{code}



We now provide an inductive-recursive realizability semantics of
OpenTT.


\begin{code}

{--wpreddepextirr : {w : 𝕎·} {f : wPred w} (h : wPredDep f) (i : □· w f) → Set(lsuc(L))
wpreddepextirr = wPredDepExtIrr-inOpenBar--}


{--≡# : {a b : Term} → a ≡ b → (ca : # a) (cb : # b) → ca ≡ cb
≡# {a} {b} e ca cb = {!!}--}


-- PERs and world dependent PERs
per : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
per = CTerm → CTerm → Set (lsuc n ⊔ lsuc m)

wper : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
wper = (w : 𝕎·) → per

ist : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
ist = CTerm → Set (lsuc n ⊔ lsuc m)

wist : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
wist = (w : 𝕎·) → ist

𝕃 : Set
𝕃 = ℕ

-- eqTypes and eqInType provide meaning to types w.r.t. already interpreted universes,
-- given by univs (1st conjunct defines the equality between such universes, while the
-- second conjunct defines the equality in such universes)
univsUpTo : 𝕃 → Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
univsUpTo n = (m : 𝕃) (p : m < n) → wper



univs : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
univs = Σ ℕ univsUpTo


↓𝕃 : 𝕃 → 𝕃
↓𝕃 0 = 0
↓𝕃 (suc n) = n


↓𝕃≤ : (n : ℕ) → ↓𝕃 n ≤ n
↓𝕃≤ 0 = ≤-refl
↓𝕃≤ (suc n) = n≤1+n n


↓univsUpTo : {n : 𝕃} → univsUpTo n → univsUpTo (↓𝕃 n)
↓univsUpTo {0} f m p = f m p
↓univsUpTo {suc n} f m p = f m (<-trans p (n<1+n n))


↓U : univs → univs
↓U (n , f) = (↓𝕃 n , ↓univsUpTo f)


data BC : Set where
  BCb : BC


{--
Σ∈𝔹'' : (B : Bars W) {w : 𝕎·} {g : wPred w} (b : 𝔹 W B w) (i : ∈𝔹 W b g) (f : wPredDep g) → Set(lsuc(L))
Σ∈𝔹'' B {w} {g} b i f =
  {w1 : 𝕎·} (e1 : w ⊑· w1) (ib : 𝔹.bar b w1)
  → Σ (𝔹 W B w1) (λ b' → ∈𝔹Dep W b' (i e1 ib) (↑wPredDep'' f e1))
{-# INLINE Σ∈𝔹'' #-}


□⋆ : {--BC →--} (w : 𝕎·) (f : wPred w) → Set(lsuc(L))
□⋆ {--_--} {--BCb--} = Mod.□ (BarsProps→Mod W B)
--λ w f → Σ∈𝔹 W (BarsProps.bars B) {w} f
{-# INLINE □⋆ #-}


□'⋆ : {--(z : BC)--} (w : 𝕎·) {g : wPred w} (h : □⋆ {--z--} w g) (f : wPredDep g) → Set(lsuc(L))
□'⋆ {--_--} {--BCb--} w {g} h f = Mod.□' (BarsProps→Mod W B) w h f
-- Σ∈𝔹' W (BarsProps.bars B) {w} {g} h f
 -- Σ∈𝔹'' (BarsProps.bars B) {w} {g} (fst h) (snd h) f
{-# INLINE BarsProps→Mod #-}
{-# INLINE □'⋆ #-}
--}


-- equality between types (an inductive definition)
-- and equality in types (a recursive function)
-- We don't check positivity here, this can be done for all instances of bar.Bar
{-# NO_POSITIVITY_CHECK #-}
data eqTypes (u : univs) (w : 𝕎·) (T1 T2 : CTerm) : Set (lsuc n ⊔ lsuc m)
--{-# TERMINATING #-}
eqInType : (u : univs) (w : 𝕎·) {T1 T2 : CTerm} → (eqTypes u w T1 T2) → per
\end{code}


Equality between type is defined as the following inductive definition


\begin{code}
data eqTypes u w T1 T2 where
  EQTNAT : T1 #⇛ #NAT at w → T2 #⇛ #NAT at w → eqTypes u w T1 T2
  EQTQNAT : T1 #⇛ #QNAT at w → T2 #⇛ #QNAT at w → eqTypes u w T1 T2
  EQTTNAT : T1 #⇛ #TNAT at w → T2 #⇛ #TNAT at w → eqTypes u w T1 T2
  EQTLT : (a1 a2 b1 b2 : CTerm)
    → T1 #⇛ (#LT a1 b1) at w
    → T2 #⇛ (#LT a2 b2) at w
    → #strongMonEq w a1 a2
    → #strongMonEq w b1 b2
    → eqTypes u w T1 T2
  EQTQLT : (a1 a2 b1 b2 : CTerm)
    → T1 #⇛ (#QLT a1 b1) at w
    → T2 #⇛ (#QLT a2 b2) at w
    → #weakMonEq w a1 a2
    → #weakMonEq w b1 b2
    → eqTypes u w T1 T2
  EQTFREE : T1 #⇛ #FREE at w → T2 #⇛ #FREE at w → eqTypes u w T1 T2
  EQTPI : (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
    → T1 #⇛ (#PI A1 B1) at w
    → T2 #⇛ (#PI A2 B2) at w
    → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                              → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTSUM : (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
    → T1 #⇛ (#SUM A1 B1) at w
    → T2 #⇛ (#SUM A2 B2) at w
    → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTSET : (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
    → T1 #⇛ (#SET A1 B1) at w
    → T2 #⇛ (#SET A2 B2) at w
    → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTISECT : (A1 B1 A2 B2 : CTerm)
    → T1 #⇛ (#ISECT A1 B1) at w
    → T2 #⇛ (#ISECT A2 B2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtB : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtB w e) a b))
    → eqTypes u w T1 T2
  EQTTUNION : (A1 : CTerm) (B1 : CTerm0) (A2 : CTerm) (B2 : CTerm0)
    → T1 #⇛ (#TUNION A1 B1) at w
    → T2 #⇛ (#TUNION A2 B2) at w
    → (eqta : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtb : ∀𝕎 w (λ w' e → (a1 a2 : CTerm) → eqInType u w' (eqta w' e) a1 a2
                         → eqTypes u w' (sub0 a1 B1) (sub0 a2 B2)))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqta w e) a b))
    → (extb : (a b c d : CTerm) → wPredDepExtIrr (λ w e x → eqInType u w (eqtb w e a b x) c d))
    → eqTypes u w T1 T2
  EQTEQ : (a1 b1 a2 b2 A B : CTerm)
    → T1 #⇛ #EQ a1 a2 A at w
    → T2 #⇛ #EQ b1 b2 B at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A B))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (eqt1 : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) a1 b1))
    → (eqt2 : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) a2 b2))
    → eqTypes u w T1 T2
  EQTUNION : (A1 B1 A2 B2 : CTerm)
    → T1 #⇛ (#UNION A1 B1) at w
    → T2 #⇛ (#UNION A2 B2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtB : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtB w e) a b))
    → eqTypes u w T1 T2
  EQTQTUNION : (A1 B1 A2 B2 : CTerm)
    → T1 #⇛ (#QTUNION A1 B1) at w
    → T2 #⇛ (#QTUNION A2 B2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (eqtB : ∀𝕎 w (λ w' _ → eqTypes u w' B1 B2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (extb : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtB w e) a b))
    → eqTypes u w T1 T2
  EQTSQUASH : (A1 A2 : CTerm)
    → T1 #⇛ (#TSQUASH A1) at w
    → T2 #⇛ (#TSQUASH A2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2
  EQTTRUNC : (A1 A2 : CTerm)
    → T1 #⇛ (#TTRUNC A1) at w
    → T2 #⇛ (#TTRUNC A2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2
  EQTCONST : (A1 A2 : CTerm)
    → T1 #⇛ (#TCONST A1) at w
    → T2 #⇛ (#TCONST A2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2
  EQTSUBSING : (A1 A2 : CTerm)
    → T1 #⇛ (#SUBSING A1) at w
    → T2 #⇛ (#SUBSING A2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2
{--  EQTDUM : (A1 A2 : Term)
    → T1 ⇛ (DUM A1) at w
    → T2 ⇛ (DUM A2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : Term) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → eqTypes u w T1 T2--}
  EQFFDEFS : (A1 A2 x1 x2 : CTerm)
    → T1 #⇛ (#FFDEFS A1 x1) at w
    → T2 #⇛ (#FFDEFS A2 x2) at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes u w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType u w (eqtA w e) a b))
    → (eqx : ∀𝕎 w (λ w' e → eqInType u w' (eqtA w' e) x1 x2))
    → eqTypes u w T1 T2
  EQTPURE :
    T1 #⇛ #PURE at w
    → T2 #⇛ #PURE at w
    → eqTypes u w T1 T2
  EQTUNIV : (i : ℕ) (p : i < fst u)
    → T1 #⇛ #UNIV i at w
    → T2 #⇛ #UNIV i at w
    → eqTypes u w T1 T2
  EQTLIFT : (A1 A2 : CTerm)
    → T1 #⇛ #LIFT A1 at w
    → T2 #⇛ #LIFT A2 at w
    → (eqtA : ∀𝕎 w (λ w' _ → eqTypes (↓U u) w' A1 A2))
    → (exta : (a b : CTerm) → wPredExtIrr (λ w e → eqInType (↓U u) w (eqtA w e) a b))
    → eqTypes u w T1 T2
  EQTBAR : □· w (λ w' _ → eqTypes u w' T1 T2) → eqTypes u w T1 T2
\end{code}

Equality in types is defined as the following recursive function.

\begin{code}
PIeq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → per
PIeq eqa eqb f g = (a b : CTerm) → (e : eqa a b) → eqb a b e (#APPLY f a) (#APPLY g b)

SUMeq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → wper
SUMeq eqa eqb w f g =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ CTerm (λ b1 → Σ CTerm (λ b2 →
    Σ (eqa a1 a2) (λ ea →
    f #⇛ (#PAIR a1 b1) at w
    × g #⇛ (#PAIR a2 b2) at w
    × eqb a1 a2 ea b1 b2)))))

SETeq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → per
SETeq eqa eqb f g = Σ CTerm (λ b → Σ (eqa f g) (λ ea → eqb f g ea b b))


EQeq : (a1 a2 : CTerm) (eqa : per) → wper
EQeq a1 a2 eqa w t1 t2 =
  --t1 #⇛ #AX at w × t2 #⇛ #AX at w ×
  eqa a1 a2


ISECTeq : (eqa eqb : per) → per
ISECTeq eqa eqb t1 t2 = eqa t1 t2 × eqb t1 t2


UNIONeq : (eqa eqb : per) → wper
UNIONeq eqa eqb w t1 t2  =
  Σ CTerm (λ a → Σ CTerm (λ b →
    (t1 #⇛ (#INL a) at w × t2 #⇛ (#INL b) at w × eqa a b)
    ⊎
    (t1 #⇛ (#INR a) at w × t2 #⇛ (#INR b) at w × eqb a b)))


QTUNIONeq : (eqa eqb : per) → wper
QTUNIONeq eqa eqb w t1 t2  =
  Σ CTerm (λ a → Σ CTerm (λ b →
    (t1 #⇓ (#INL a) at w × t2 #⇓ (#INL b) at w × eqa a b)
    ⊎
    (t1 #⇓ (#INR a) at w × t2 #⇓ (#INR b) at w × eqb a b)))


{--
 -- Positivity issues with this one...
 -- We prove in props0 that they are equivalent
data TSQUASHeq (eqa : per) (w : 𝕎·) (t1 t2 : CTerm) : Set(lsuc(L))
data TSQUASHeq eqa w t1 t2 where
  TSQUASHeq-base : (a1 a2 : CTerm) → #isValue a1 → #isValue a2 → eqa a1 a2 → ∼C w t1 a1 → ∼C w t2 a2 → TSQUASHeq eqa w t1 t2
  TSQUASHeq-trans : (t : CTerm) → TSQUASHeq eqa w t1 t → TSQUASHeq eqa w t t2 → TSQUASHeq eqa w t1 t2
--}


{-- We equivalently define the above definition as follows... --}
TSQUASHeqBase : (eqa : per) → wper
TSQUASHeqBase eqa w t1 t2 =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → #isValue a1 × #isValue a2 × ∼C! w t1 a1 × ∼C! w t2 a2 × eqa a1 a2))


TSQUASHeqℕ : ℕ → (eqa : per) → wper
TSQUASHeqℕ 0 eqa w t1 t2 = TSQUASHeqBase eqa w t1 t2
TSQUASHeqℕ (suc n) eqa w t1 t2 = Σ CTerm (λ t → TSQUASHeqBase eqa w t1 t × TSQUASHeqℕ n eqa w t t2)


TSQUASHeq : (eqa : per) → wper
TSQUASHeq eqa w t1 t2 = Σ ℕ (λ n → TSQUASHeqℕ n eqa w t1 t2)


{-- We equivalently define the above definition as follows... --}
TTRUNCeqBase : (eqa : per) → wper
TTRUNCeqBase eqa w t1 t2 =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → #isValue a1 × #isValue a2 × t1 #⇓ a1 at w × t2 #⇓ a2 at w × eqa a1 a2))


TTRUNCeqℕ : ℕ → (eqa : per) → wper
TTRUNCeqℕ 0 eqa w t1 t2 = TTRUNCeqBase eqa w t1 t2
TTRUNCeqℕ (suc n) eqa w t1 t2 = Σ CTerm (λ t → TTRUNCeqBase eqa w t1 t × TTRUNCeqℕ n eqa w t t2)


TTRUNCeq : (eqa : per) → wper
TTRUNCeq eqa w t1 t2 = Σ ℕ (λ n → TTRUNCeqℕ n eqa w t1 t2)


TUNIONeqBase : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → per
TUNIONeqBase eqa eqb t1 t2 =
  Σ CTerm (λ a1 → Σ CTerm (λ a2 → Σ (eqa a1 a2) (λ ea → eqb a1 a2 ea t1 t2)))


TUNIONeqℕ : ℕ → (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → per
TUNIONeqℕ 0 eqa eqb t1 t2 = TUNIONeqBase eqa eqb t1 t2
TUNIONeqℕ (suc n) eqa eqb t1 t2 = Σ CTerm (λ t → TUNIONeqBase eqa eqb t1 t × TUNIONeqℕ n eqa eqb t t2)


TUNIONeq : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) → per
TUNIONeq eqa eqb t1 t2 = Σ ℕ (λ n → TUNIONeqℕ n eqa eqb t1 t2)


TCONSTeq : (eqa : per) → wper
TCONSTeq eqa w t1 t2 =
  eqa t1 t2
  × #⇓→#⇓! w t1
  × #⇓→#⇓! w t2


SUBSINGeq : (eqa : per) → per
SUBSINGeq eqa t1 t2 = eqa t1 t1 × eqa t2 t2


FFDEFSeq : CTerm → (eqa : per) → wper
FFDEFSeq x1 eqa w t1 t2 =
  Σ CTerm (λ x →
   --(t1 #⇛ #AX at w) × (t2 #⇛ #AX at w) ×
   eqa x1 x × #¬Names x)


PUREeq : per
PUREeq t1 t2 = Lift {0ℓ} (lsuc n ⊔ lsuc m) (#¬Names t1 × #¬Names t2)


NATeq : wper
NATeq w t1 t2 = Lift {n} (lsuc n ⊔ lsuc m) (#strongMonEq w t1 t2)
--  #⇛!sameℕ w t1 t2


TNATeq : wper
TNATeq w t1 t2 = Lift {n} (lsuc n ⊔ lsuc m) (#∀𝕎-⇓∼ℕ w t1 t2)


{-# TERMINATING #-}
--{-# INLINE □·' #-}
--{-# INLINE inBethBar' #-}
--{-# INLINE inOpenBar' #-}
-- NOTE: EQTNAT's equality was defined in terms of #strongMonEq, and is now defined in terms of #⇛!sameℕ.
-- We could have another nat type that's interpreted by #strongMonEq.
-- We want #⇛!sameℕ here to get some functions in Nat->QT(Bool)
-- Only to prove →equalInType-CS-NAT→T in props3?
eqInType _ w (EQTNAT _ _) t1 t2 = □· w (λ w' _ → NATeq w' t1 t2)
eqInType _ w (EQTQNAT _ _) t1 t2 = □· w (λ w' _ → #weakMonEq w' t1 t2)
eqInType _ w (EQTTNAT _ _) t1 t2 = □· w (λ w' _ → TNATeq w' t1 t2)
eqInType _ w (EQTLT a1 _ b1 _ _ _ _ _) t1 t2 = □· w (λ w' _ → #<NUM-pair w' a1 b1)
eqInType _ w (EQTQLT a1 _ b1 _ _ _ _ _) t1 t2 = □· w (λ w' _ → #<NUM-pair w' a1 b1)
eqInType _ w (EQTFREE _ _) t1 t2 = □· w (λ w' _ → #⇛to-same-CS w' t1 t2)
eqInType u w (EQTPI _ _ _ _ _ _ eqta eqtb exta extb) f1 f2 =
  □· w (λ w' e → PIeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) f1 f2)
eqInType u w (EQTSUM _ _ _ _ _ _ eqta eqtb exta extb) t1 t2 =
  □· w (λ w' e → SUMeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) w' t1 t2)
eqInType u w (EQTSET _ _ _ _ _ _ eqta eqtb exta extb) t1 t2 =
  □· w (λ w' e → SETeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) t1 t2)
eqInType u w (EQTISECT _ _ _ _ _ _ eqtA eqtB exta extb) t1 t2 =
  □· w (λ w' e → ISECTeq (eqInType u w' (eqtA w' e)) (eqInType u w' (eqtB w' e)) t1 t2)
eqInType u w (EQTTUNION _ _ _ _ _ _ eqta eqtb exta extb) t1 t2 =
  □· w (λ w' e → TUNIONeq (eqInType u w' (eqta w' e)) (λ a1 a2 eqa → eqInType u w' (eqtb w' e a1 a2 eqa)) t1 t2)
eqInType u w (EQTEQ a1 _ a2 _ _ _ _ _ eqtA exta eqt1 eqt2) t1 t2 =
  □· w (λ w' e → EQeq a1 a2 (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTUNION _ _ _ _ _ _ eqtA eqtB exta extb) t1 t2 =
  □· w (λ w' e → UNIONeq (eqInType u w' (eqtA w' e)) (eqInType u w' (eqtB w' e)) w' t1 t2)
eqInType u w (EQTQTUNION _ _ _ _ _ _ eqtA eqtB exta extb) t1 t2 =
  □· w (λ w' e → QTUNIONeq (eqInType u w' (eqtA w' e)) (eqInType u w' (eqtB w' e)) w' t1 t2)
eqInType u w (EQTSQUASH _ _ _ _ eqtA exta) t1 t2 =
  □· w (λ w' e → TSQUASHeq (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTTRUNC _ _ _ _ eqtA exta) t1 t2 =
  □· w (λ w' e → TTRUNCeq (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTCONST _ _ _ _ eqtA exta) t1 t2 =
  □· w (λ w' e → TCONSTeq (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTSUBSING _ _ _ _ eqtA exta) t1 t2 =
  □· w (λ w' e → SUBSINGeq (eqInType u w' (eqtA w' e)) t1 t2)
--eqInType u w (EQTDUM _ _ _ _ eqtA exta) t1 t2 = Lift {0ℓ} 1ℓ ⊤
eqInType u w (EQFFDEFS _ _ x1 _ _ _ eqtA exta _) t1 t2 =
  □· w (λ w' e → FFDEFSeq x1 (eqInType u w' (eqtA w' e)) w' t1 t2)
eqInType u w (EQTPURE _ _) t1 t2 =
  □· w (λ w' e → PUREeq t1 t2)
eqInType u w (EQTUNIV i p c₁ c₂) T1 T2 = snd u i p w T1 T2
eqInType u w (EQTLIFT A1 A2 c₁ c₂ eqtA exta) t1 t2 =
  □· w (λ w' e → eqInType (↓U u) w' (eqtA w' e) t1 t2)
--  □· w (λ w' e → eqInType (↓U u) w' (eqtA w' e) T1 T2)
eqInType u w (EQTBAR f) t1 t2 =
  □·' w f (λ w' _ (x : eqTypes u w' _ _) → eqInType u w' x t1 t2)
  {-- This is an unfolding of the above, as agda doesn't like the above.
      Why doesn't it work with the INLINE? --}
{--  ∀𝕎 w (λ w0 e0 →
           let p  = f w0 e0 in
           let w1 = proj₁ p in
           let e1 = proj₁ (proj₂ p) in
           let q  = proj₂ (proj₂ p) in
           ∀∃∀𝕎 w1 (λ w2 e2 → (y : w1 ⊑· w2) (z : w ⊑· w2) → eqInType u w2 (q w2 y z) t1 t2))
--           ∃𝕎 w1 (λ w2 e2 → ∀𝕎 w2 (λ w3 e3 → (z : w ⊑· w3) → eqInType u w3 (q w3 (⊑-trans· e2 e3) z) t1 t2)))
--}
\end{code}


We finally close the construction as follows:


\begin{code}
-- Two level-m universes are equal if they compute to (UNIV m)
eqUnivi : (m : ℕ) → wper
eqUnivi m w T1 T2 = □· w (λ w' _ → ⌜ T1 ⌝ ⇛ (UNIV m) at w' × ⌜ T2 ⌝ ⇛ (UNIV m) at w')

{--uni0 : univsUpTo 0
uni0 i ()--}


□·EqTypes : (u : univs) (w : 𝕎·) (T1 T2 : CTerm) → Set (lsuc n ⊔ lsuc m)
□·EqTypes u w T1 T2 = □· w (λ w' _ → eqTypes u w' T1 T2)

uniUpTo : (n : ℕ) → univsUpTo n
uniUpTo 0 i ()
uniUpTo (suc n) m p with m <? n
... | yes q = uniUpTo n m q
... | no q = □·EqTypes (n , uniUpTo n) -- i.e., m ≡ n


{--
-- Two terms are equal in universe m if they are equal according to eqTypes
eqInUnivi : (m : ℕ) → wper
eqInUnivi 0 = λ _ _ _ → Lift {0ℓ} 1ℓ ⊥
eqInUnivi (suc m) w T1 T2 = {!!}
--  □· w (λ w' _ → eqTypes (m , (eqUnivi m , eqInUnivi m)) w' T1 T2 {-- ⊎ eqInUnivi m w' T1 T2--})
-- To have this ⊎ we need a way to lift types in eqTypes, so that types equal at level 'n' can be equal
-- as types in lower universes, and then lifted up to being equal as types in 'n' again
-- The type system probably isn't transitive without that.
--}


{--eqInUnivi≤ : (m : ℕ) (i : ℕ) (p : i ≤ m) → wper
eqInUnivi≤ 0 i p = λ _ _ _ → Lift {0ℓ} 1ℓ ⊥
eqInUnivi≤ (suc m) i p w T1 T2 with suc m ≤? c =
  □· w (λ w' _ → eqTypes (m , (eqUnivi m , eqInUnivi m)) w' T1 T2 {-- ⊎ eqInUnivi m w' T1 T2--})--}

--- Add an explicit level-lifting constructor to the type system
mkU : (n : ℕ) (u : univsUpTo n) → univs
mkU n u = (n , u)

uni : ℕ → univs
uni n = mkU n (uniUpTo n) --(eqUnivi n , eqInUnivi n))


{--ul : ℕ → ℕ
ul n = {--suc--} n--}


is-uni : (u : univs) → Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
is-uni u = u ≡ uni (fst u)

is-uni→ : {i : ℕ} (u : univsUpTo i) → is-uni (i , u) → u ≡ uniUpTo i
is-uni→ {i} .(uniUpTo i) refl = refl

is-uni-uni : (i : 𝕃) → is-uni (uni i)
is-uni-uni r = refl


≡univs : {i : 𝕃} {u1 u2 : univsUpTo i} → u1 ≡ u2 → mkU i u1 ≡ mkU i u2
≡univs {i} {u1} {u2} e rewrite e = refl

≡uniUpTo : (i j : 𝕃) (p q : j < i) → uniUpTo i j p ≡ uniUpTo i j q
≡uniUpTo (suc i) j p q with j <? i
... | yes w = refl
... | no w = refl

↓U-uni : (i : 𝕃) → ↓U (uni i) ≡ uni (↓𝕃 i)
↓U-uni 0 = refl
↓U-uni (suc i) = ≡univs (E e)
  where
    e : (x : 𝕃) → ↓univsUpTo (uniUpTo (suc i)) x ≡ uniUpTo i x
    e x with x <? i
    ... | yes p = E f
      where
        f : (x₁ : suc x ≤ i) → uniUpTo i x p ≡ uniUpTo i x x₁
        f q = ≡uniUpTo i x p q
    ... | no p = E f
      where
        f : (x₁ : suc x ≤ i) → □·EqTypes (i , uniUpTo i) ≡ uniUpTo i x x₁
        f q = ⊥-elim (p q)

𝕌 : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
𝕌 = Σ univs is-uni

mk𝕌 : {u : univs} (isu : is-uni u) → 𝕌
mk𝕌 {u} isu = (u , isu)

ℕ→𝕌 : ℕ → 𝕌
ℕ→𝕌 i = mk𝕌 {uni i} (is-uni-uni i)


is-uni-↓U : {u : univs} → is-uni u → is-uni (↓U u)
is-uni-↓U {u} isu rewrite isu = ↓U-uni (fst u)


↓𝕌 : 𝕌 → 𝕌
↓𝕌 (u , isu) = ↓U u , is-uni-↓U isu


_·ᵤ : 𝕌 → univs
_·ᵤ u = fst u


_·ᵢ : (u : 𝕌) → is-uni (u ·ᵤ)
_·ᵢ u = snd u


_·ₙ : 𝕌 → ℕ
_·ₙ u = fst (u ·ᵤ)


≡Types : (u : 𝕌) → wper
≡Types u = eqTypes (u ·ᵤ)

≡∈Type : (u : 𝕌) (w : 𝕎·) {T1 T2 : CTerm} → (eqTypes (u ·ᵤ) w T1 T2) → per
≡∈Type u w eqt = eqInType (u ·ᵤ) w eqt

TEQ : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
TEQ = wper

IST : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
IST = wist

EQT : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
EQT = (w : 𝕎·) (T a b : CTerm) → Set (lsuc n ⊔ lsuc m)

MEMT : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
MEMT = (w : 𝕎·) (T a : CTerm) → Set (lsuc n ⊔ lsuc m)

-- Finally, the 'equal types' and 'equal in types' relations
equalTypes : (u : ℕ) → TEQ
equalTypes u = eqTypes (uni u)

isType : (u : ℕ) → IST
isType u w T = equalTypes u w T T

equalTerms : (n : ℕ) (w : 𝕎·) {T1 T2 : CTerm} → (equalTypes n w T1 T2) → per
equalTerms n w eqt = eqInType (uni n) w eqt

equalInType : (u : ℕ) → EQT
equalInType u w T a b = Σ (isType u w T) (λ p → equalTerms u w p a b)

∈Type : (u : ℕ) → MEMT
∈Type u w T a = equalInType u w T a a


INHT : Set (lsuc (lsuc n) ⊔ lsuc (lsuc m))
INHT = (w : 𝕎·) (T : CTerm) → Set (lsuc n ⊔ lsuc m)


inhType : (u : ℕ) → INHT
inhType u w T = Σ CTerm (λ t → ∈Type u w T t)

eqtypes : TEQ
eqtypes w T1 T2 = Σ ℕ (λ u → equalTypes u w T1 T2)

eqintype : EQT
eqintype w T a b = Σ ℕ (λ u → equalInType u w T a b)

member : MEMT
member w T a = eqintype w T a a

{--wfinhN1L : (j : ℕ) → wfInh (inhN1L j)
wfinhN1L j = ≤-refl

wfinhN2L : (j : ℕ) → wfInh (inhN2L j)
wfinhN2L j = (n≤1+n _)--}

¬s≤ : (j : ℕ) → ¬ suc j ≤ j
¬s≤ .(suc _) (_≤_.s≤s h) = ¬s≤ _ h

¬≡s : (j : ℕ) → ¬ j ≡ suc j
¬≡s 0 ()
¬≡s (suc j) ()

¬s≤0 : (j : ℕ) → ¬ suc j ≤ 0
¬s≤0 j ()

eq-pair : {a b : Level} {A : Set a} {B : Set b} {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ≡ a₂ → b₁ ≡ b₂ → ( a₁ , b₁ ) ≡ ( a₂ , b₂ )
eq-pair {a} {b} {A} {B} {a₁} {a₂} {b₁} {b₂} p q rewrite p | q = refl


≤-trans-≤-refl : {i j : ℕ} (c : i ≤ j) → ≤-trans c ≤-refl ≡ c
≤-trans-≤-refl {i} {j} c = ≤-irrelevant _ c


-- ---------------------------------
-- Type system
intype : (w : 𝕎·) (T t : CTerm) → Set (lsuc n ⊔ lsuc m)
intype w T t = eqintype w T t t

TEQsym : TEQ → Set (lsuc n ⊔ lsuc m)
TEQsym τ = (w : 𝕎·) (A B : CTerm) → τ w A B → τ w B A

TEQtrans : TEQ → Set (lsuc n ⊔ lsuc m)
TEQtrans τ = (w : 𝕎·) (A B C : CTerm) → τ w A B → τ w B C → τ w A C

EQTsym : EQT → Set (lsuc n ⊔ lsuc m)
EQTsym σ = (w : 𝕎·) (A a b : CTerm) → σ w A a b → σ w A b a

EQTtrans : EQT → Set (lsuc n ⊔ lsuc m)
EQTtrans σ  = (w : 𝕎·) (A a b c : CTerm) → σ w A a b → σ w A b c → σ w A a c

TSext : TEQ → EQT → Set (lsuc n ⊔ lsuc m)
TSext τ σ = (w : 𝕎·) (A B a b : CTerm) → τ w A B → σ w A a b → σ w B a b

-- NOTE: Can we do be better than #⇛!?
TEQcomp : TEQ → Set (lsuc n ⊔ lsuc m)
TEQcomp τ = (w : 𝕎·) (A B : CTerm) → A #⇛! B at w → τ w A A → τ w A B

-- NOTE: Can we do be better than #⇛!?
EQTcomp : EQT → Set (lsuc n ⊔ lsuc m)
EQTcomp σ = (w : 𝕎·) (A a b : CTerm) → a #⇛! b at w → σ w A a a → σ w A a b

TEQmon : TEQ → Set (lsuc n ⊔ lsuc m)
TEQmon τ = {w1 w2 : 𝕎·} (A B : CTerm) → w1 ⊑· w2 → τ w1 A B → τ w2 A B

EQTmon : EQT → Set (lsuc n ⊔ lsuc m)
EQTmon σ = {w1 w2 : 𝕎·} (A a b : CTerm) → w1 ⊑· w2 → σ w1 A a b → σ w2 A a b

TEQloc : TEQ → Set (lsuc n ⊔ lsuc m)
TEQloc τ = {w : 𝕎·} (A B : CTerm) → □· w (λ w' _ → τ w' A B) → τ w A B

EQTloc : EQT → Set (lsuc n ⊔ lsuc m)
EQTloc σ = {w : 𝕎·} (A a b : CTerm) → □· w (λ w' _ → σ w' A a b) → σ w A a b

EQTcons : EQT → Set (lsuc n ⊔ lsuc m)
EQTcons σ = (w : 𝕎·) (a : CTerm) → ¬ σ w #FALSE a a

\end{code}
