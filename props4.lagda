\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

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
open import getChoice
open import progress
open import choiceExt
open import newChoice
open import mod
open import encode


module props4 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (N : NewChoice W C K G)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
              (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import type_sys_props_m(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)




→equalTypesLT : {i : ℕ} {w : 𝕎·} {a₁ a₂ b₁ b₂ : CTerm}
                 → equalInType i w #NAT a₁ a₂
                 → equalInType i w #NAT b₁ b₂
                 → equalTypes i w (#LT a₁ b₁) (#LT a₂ b₂)
→equalTypesLT {i} {w} {a₁} {a₂} {b₁} {b₂} ea eb =
  eqTypes-local (∀𝕎-□Func2 aw ea1 eb1)
  where
    ea1 : □· w (λ w' _ → NATeq w' a₁ a₂)
    ea1 = equalInType-NAT→ i w a₁ a₂ ea

    eb1 : □· w (λ w' _ → NATeq w' b₁ b₂)
    eb1 = equalInType-NAT→ i w b₁ b₂ eb

    aw : ∀𝕎 w (λ w' e' → NATeq w' a₁ a₂ → NATeq w' b₁ b₂ → equalTypes i w' (#LT a₁ b₁) (#LT a₂ b₂))
    aw  w1 e1 ha hb =
      EQTLT a₁ a₂ b₁ b₂ (#compAllRefl (#LT a₁ b₁) w1) (#compAllRefl (#LT a₂ b₂) w1) ha hb



→INL-equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B x y : CTerm}
                          → isType n w B
                          → equalInType n w A x y
                          → equalInType n w (#UNION A B) (#INL x) (#INL y)
→INL-equalInType-UNION {n} {w} {A} {B} {x} {y} tb h =
  →equalInType-UNION (fst h) tb (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → UNIONeq (equalInType n w' A) (equalInType n w' B) w' (#INL x) (#INL y))
    aw w' e' = x , y , inj₁ (⇓-refl ⌜ #INL x ⌝ w' {--#compAllRefl (#INL x) w'--} ,
                             ⇓-refl ⌜ #INL y ⌝ w' {--#compAllRefl (#INL y) w'--} ,
                             equalInType-mon h w' e')


→INR-equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B x y : CTerm}
                          → isType n w A
                          → equalInType n w B x y
                          → equalInType n w (#UNION A B) (#INR x) (#INR y)
→INR-equalInType-UNION {n} {w} {A} {B} {x} {y} ta h =
  →equalInType-UNION ta (fst h) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → UNIONeq (equalInType n w' A) (equalInType n w' B) w' (#INR x) (#INR y))
    aw w' e' = x , y , inj₂ (⇓-refl ⌜ #INR x ⌝ w' {--#compAllRefl (#INR x) w'--} ,
                             ⇓-refl ⌜ #INR y ⌝ w' {--#compAllRefl (#INR y) w'--} ,
                             equalInType-mon h w' e')



{--
-- MOVE to props3
→equalInType-QTUNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓! (#INL x) at w' × b #⇓! (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓! (#INR x) at w' × b #⇓! (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#TSQUASH (#UNION A B)) a b
→equalInType-QTUNION {n} {w} {A} {B} {a} {b} isa isb i =
  equalInTypeTSQUASH← (Mod.∀𝕎-□Func M aw ({--Mod.→□∀𝕎 M--} i))
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇓! #INL x at w' × b #⇓! #INL y at w' × equalInType n w' A x y ⊎
                            a #⇓! #INR x at w' × b #⇓! #INR y at w' × equalInType n w' B x y))
                        → TSQUASHeq (equalInType n w' (#UNION A B)) w' a b)
    aw w' e' (x , y , inj₁ (c₁ , c₂ , h)) = TSQUASH-eq→ (TSQUASH-eq-base (#INL x) (#INL y) tt tt (#⇓!→∼C! {w'} {a} {#INL x} c₁) (#⇓!→∼C! {w'} {b} {#INL y} c₂) (→INL-equalInType-UNION (eqTypes-mon (uni n) isb w' e') h))
    aw w' e' (x , y , inj₂ (c₁ , c₂ , h)) = TSQUASH-eq→ (TSQUASH-eq-base (#INR x) (#INR y) tt tt (#⇓!→∼C! {w'} {a} {#INR x} c₁) (#⇓!→∼C! {w'} {b} {#INR y} c₂) (→INR-equalInType-UNION (eqTypes-mon (uni n) isa w' e') h))
--}



{--
-- MOVE to props3
→equalInType-TRUNION : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → isType n w A
                       → isType n w B
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓ (#INL x) at w' × b #⇓ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓ (#INR x) at w' × b #⇓ (#INR y) at w' × equalInType n w' B x y))))
                       → equalInType n w (#TTRUNC (#UNION A B)) a b
→equalInType-TRUNION {n} {w} {A} {B} {a} {b} isa isb i =
  equalInTypeTTRUNC← (Mod.∀𝕎-□Func M aw ({--Mod.→□∀𝕎 M--} i))
  where
    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                            a #⇓ #INL x at w' × b #⇓ #INL y at w' × equalInType n w' A x y ⊎
                            a #⇓ #INR x at w' × b #⇓ #INR y at w' × equalInType n w' B x y))
                        → TTRUNCeq (equalInType n w' (#UNION A B)) w' a b)
    aw w' e' (x , y , inj₁ (c₁ , c₂ , h)) =
      TTRUNC-eq→ (TTRUNC-eq-base
                    (#INL x) (#INL y) tt tt c₁ c₂
                    (→INL-equalInType-UNION (eqTypes-mon (uni n) isb w' e') h))
    aw w' e' (x , y , inj₂ (c₁ , c₂ , h)) =
      TTRUNC-eq→ (TTRUNC-eq-base
                    (#INR x) (#INR y) tt tt c₁ c₂
                    (→INR-equalInType-UNION (eqTypes-mon (uni n) isa w' e') h))
--}



{--
-- MOVE to props3
TTRUNC-eq-UNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                    → TTRUNC-eq (equalInType n w (#UNION A B)) w a b
                    → Σ CTerm (λ x → Σ CTerm (λ y →
                           a #⇓ #INL x at w × b #⇓ #INL y at w × equalInType n w A x y ⊎
                           a #⇓ #INR x at w × b #⇓ #INR y at w × equalInType n w B x y))
TTRUNC-eq-UNION→ {n} {w} {A} {B} {a} {b} (TTRUNC-eq-base a1 a2 i1 i2 c1 c2 ea) = {!!} --Mod.□-const M (Mod.∀𝕎-□Func M aw eqi)
  where
    eqi : □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                          → (a1 #⇛ (#INL x) at w' × a2 #⇛ (#INL y) at w' × equalInType n w' A x y)
                             ⊎ (a1 #⇛ (#INR x) at w' × a2 #⇛ (#INR y) at w' × equalInType n w' B x y))))
    eqi = equalInType-UNION→ ea

    aw : ∀𝕎 w (λ w' e' → Σ CTerm (λ x → Σ CTerm (λ y →
                           a1 #⇛ #INL x at w' × a2 #⇛ #INL y at w' × equalInType n w' A x y ⊎
                           a1 #⇛ #INR x at w' × a2 #⇛ #INR y at w' × equalInType n w' B x y))
                       → Σ CTerm (λ x → Σ CTerm (λ y →
                           a #⇓ #INL x at w × b #⇓ #INL y at w × equalInType n w A x y ⊎
                           a #⇓ #INR x at w × b #⇓ #INR y at w × equalInType n w B x y)))
    aw w' e' (x , y , inj₁ (c₁ , c₂ , eqa)) =
      x , y , inj₁ (≡R→#⇓ (#⇛→≡ c₁ i1) c1 ,
                    ≡R→#⇓ (#⇛→≡ c₂ i2) c2 ,
                    equalInType-local (Mod.∀𝕎-□Func M aw' eqi))
      where
        aw' : ∀𝕎 w (λ w'' e'' → Σ CTerm (λ x₁ → Σ CTerm (λ y₁ →
                                   a1 #⇛ #INL x₁ at w'' × a2 #⇛ #INL y₁ at w'' × equalInType n w'' A x₁ y₁
                                   ⊎ a1 #⇛ #INR x₁ at w'' × a2 #⇛ #INR y₁ at w'' × equalInType n w'' B x₁ y₁))
                              → equalInType n w'' A x y)
        aw' w'' e'' (x₁ , y₁ , inj₁ (d₁ , d₂ , eqa')) = {!!}
        aw' w'' e'' (x₁ , y₁ , inj₂ (d₁ , d₂ , eqb')) = {!!}
    aw w' e' (x , y , inj₂ (c₁ , c₂ , eqb)) = {!!}

TTRUNC-eq-UNION→ {n} {w} {A} {B} {a} {b} (TTRUNC-eq-trans t h1 h2) = {!!}
--}



{--
-- MOVE to props3
equalInType-TRUNION→ : {n : ℕ} {w : 𝕎·} {A B a b : CTerm}
                       → equalInType n w (#TTRUNC (#UNION A B)) a b
                       → □· w (λ w' _ → Σ CTerm (λ x → Σ CTerm (λ y
                                          → (a #⇓ (#INL x) at w' × b #⇓ (#INL y) at w' × equalInType n w' A x y)
                                             ⊎
                                             (a #⇓ (#INR x) at w' × b #⇓ (#INR y) at w' × equalInType n w' B x y))))
equalInType-TRUNION→ {n} {w} {A} {B} {a} {b} i = Mod.∀𝕎-□Func M {!!} j
  where
    j : □· w (λ w' _ → TTRUNCeq (equalInType n w' (#UNION A B)) w' a b)
    j = equalInTypeTTRUNC→ i

    aw : ∀𝕎 w (λ w' e' → TTRUNCeq (equalInType n w' (#UNION A B)) w' a b
                       → Σ CTerm (λ x → Σ CTerm (λ y →
                           a #⇓ #INL x at w' × b #⇓ #INL y at w' × equalInType n w' A x y ⊎
                           a #⇓ #INR x at w' × b #⇓ #INR y at w' × equalInType n w' B x y)))
    aw w' e' h = {!!}
--}



{--
-- MOVE to terms
QTUNION : Term → Term → Term
QTUNION a b = TSQUASH (UNION a b)


-- MOVE to terms
#QTUNION : CTerm → CTerm → CTerm
#QTUNION a b = ct (QTUNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # UNION ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | CTerm.closed b = refl


#QTUNION≡ : (a b : CTerm) → #QTUNION a b ≡ #TSQUASH (#UNION a b)
#QTUNION≡ a b = CTerm≡ refl
--}



{--FFDEFSeq-ext-eq : {eqa1 eqa2 : per} {w : 𝕎·} {t1 t2 : CTerm} {a b : CTerm}
                 → ((a b : CTerm) → eqa1 a b → eqa2 a b)
                 → a ≡ b
                 → FFDEFSeq a eqa1 w t1 t2
                 → FFDEFSeq b eqa2 w t1 t2
FFDEFSeq-ext-eq {eqa1} {eqa2} {w} {t1} {t2} {a} {b} ext eqab (x , e , nn) rewrite eqab =
  x , ext b x e , nn
--}


{--
equalInTypeFFDEFS→ : {w : 𝕎·} {i : ℕ} {a b A u : CTerm}
                       → equalInType i w (#FFDEFS A u) a b
                       → □· w (λ w' _ → FFDEFSeq u (equalInType i w' A) w' a b)
--{-# TERMINATING #-}
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTNAT x x₁ , eqi) = ⊥-elim (FFDEFSneqNAT (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTQNAT x x₁ , eqi) = ⊥-elim (FFDEFSneqQNAT (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTTNAT x x₁ , eqi) = ⊥-elim (FFDEFSneqTNAT (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (FFDEFSneqLT (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (FFDEFSneqQLT (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTFREE x x₁ , eqi) = ⊥-elim (FFDEFSneqFREE (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (FFDEFSneqPI (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (FFDEFSneqSUM (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (FFDEFSneqW (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (FFDEFSneqSET (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (FFDEFSneqTUNION (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTEQ a1 b1 a2 b2 A₁ B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (FFDEFSneqEQ (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (FFDEFSneqUNION (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (FFDEFSneqQTUNION (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (FFDEFSneqTSQUASH (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (FFDEFSneqTTRUNC (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTNOWRITE x x₁ , eqi) = ⊥-elim (FFDEFSneqNOWRITE (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTNOREAD x x₁ , eqi) = ⊥-elim (FFDEFSneqNOREAD (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (FFDEFSneqSUBSING (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) =
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → FFDEFSeq x1 (equalTerms i w' (eqtA w' e')) w' a b → FFDEFSeq u (equalInType i w' A) w' a b)
    aw w1 e1 p = FFDEFSeq-ext-eq {equalTerms i w1 (eqtA w1 e1)} {equalInType i w1 A} {w1} {a} {b} {x1} {u}
                                 (λ a1 a2 ea → eqInType→equalInType (#FFDEFSinj1 {A} {u} {A1} {x1} (#compAllVal x tt)) (eqtA w1 e1) ea)
                                 (sym (#FFDEFSinj2 {A} {u} {A1} {x1} (#compAllVal x tt))) p
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTUNIV i₁ p x x₁ , eqi) = ⊥-elim (FFDEFSneqUNIV (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (FFDEFSneqLIFT (compAllVal x₁ tt))
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTBAR x , eqi) =
  Mod.□-idem M (∀𝕎-□'-□₀ W M x aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → (z : isType i w' (#FFDEFS A u))
                        → equalTerms i w' z a b
                        → □· w' (↑wPred' (λ w'' e → FFDEFSeq u (equalInType i w'' A) w'' a b) e'))
    aw w1 e1 z h = Mod.∀𝕎-□Func M (λ w1 e1 k y → k) (equalInTypeFFDEFS→ (z , h))
--}



eqTypesFFDEFS← : {w : 𝕎·} {i : ℕ} {A B a b : CTerm}
                  → equalTypes i w A B
                  → equalInType i w A a b
                  → equalTypes i w (#FFDEFS A a) (#FFDEFS B b)
eqTypesFFDEFS← {w} {i} {A} {B} {a} {b} eqt eqi =
  EQFFDEFS
    A B a b
    (#compAllRefl (#FFDEFS A a) w)
    (#compAllRefl (#FFDEFS B b) w)
    (eqTypes-mon (uni i) eqt)
    (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqt))
    (λ w1 e1 → equalInType→eqInType {_} {_} {A} {A} {B} {a} {b} refl {eqTypes-mon (uni i) eqt w1 e1} (equalInType-mon eqi w1 e1))


→≡#lift-<NUM-pair : {w : 𝕎·} (a1 a2 b1 b2 : CTerm)
                     → a1 ≡ a2
                     → b1 ≡ b2
                     → #lift-<NUM-pair w a1 b1
                     → #lift-<NUM-pair w a2 b2
→≡#lift-<NUM-pair {w} a1 a2 b1 b2 eqa eqb h rewrite eqa | eqb = h


abstract
  equalInType-LT-⇛NUM→ : {i : ℕ} {w : 𝕎·} {a b u v : CTerm} {n m : ℕ}
                         → a #⇛ #NUM m at w
                         → b #⇛ #NUM n at w
                         → equalInType i w (#LT a b) u v
                         → m < n
  equalInType-LT-⇛NUM→ {u} {w} {a} {b} {v₁} {v₂} {n} {m} compa compb (eqt , eqi) =
    concl (#LT a b) (#LT a b) eqt eqi compa compb refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {v₁ v₂ : CTerm} (eqi : equalTerms u w eqt v₁ v₂)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {v₁' v₂' : CTerm} (eqi' : equalTerms u' w' eqt' v₁' v₂')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → a #⇛ #NUM m at w' → b #⇛ #NUM n at w' → T1' ≡ #LT a b → T2' ≡ #LT a b → m < n)
            → a #⇛ #NUM m at w → b #⇛ #NUM n at w → T1 ≡ #LT a b → T2 ≡ #LT a b → m < n
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqQNAT (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 =
        lower (Mod.□-const M {w} (Mod.∀𝕎-□Func M aw h))
        where
          h : □· w (λ w' _ → #lift-<NUM-pair w' a b)
          h = Mod.∀𝕎-□Func M (λ w1 e1 h → →≡#lift-<NUM-pair a1 a b1 b (sym (CTerm≡ (LTinj1 (compAllVal x tt)))) (sym (CTerm≡ (LTinj2 (compAllVal x tt)))) h) eqi

          aw : ∀𝕎 w (λ w' e' → #lift-<NUM-pair w' a b → Lift (lsuc L) (m < n))
          aw w1 e1 (lift (n1 , m1 , comp1 , comp2 , ltnm))
            rewrite NUMinj (⇓-val-det tt tt comp1 (lower (compa w1 e1)))
                  | NUMinj (⇓-val-det tt tt comp2 (lower (compb w1 e1))) = lift ltnm
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqUNION (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqTSQUASH (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqNOWRITE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqNOREAD (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {v₁} {v₂} eqi ind compa compb eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (LTneqLIFT(compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {v₁} {v₂} eqi ind compa compb eq1 eq2 =
        lower (Mod.□-const M {w} (Mod.∀𝕎-□'-□ M x aw eqi))
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → (at : at□· x w' e' z)
                              → equalTerms u w' z v₁ v₂ → Lift (lsuc L) (m < n))
          aw w' e' z at j = lift (ind {u} {w'} {T1} {T2} z j (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) (∀𝕎-mon e' compa) (∀𝕎-mon e' compb) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes u w T1 T2) (eqi : equalTerms u w eqt v₁ v₂)
              → a #⇛ #NUM m at w → b #⇛ #NUM n at w
              → T1 ≡ #LT a b → T2 ≡ #LT a b → m < n
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {u} {w} {T1} {T2} eqt {v₁} {v₂} eqi
            → a #⇛ #NUM m at w → b #⇛ #NUM n at w
            → T1 ≡ #LT a b → T2 ≡ #LT a b → m < n)
          ind eqt v₁ v₂ eqi


→equalInType-NAT! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → #⇛!sameℕ w' a b)
                    → equalInType i w #NAT! a b
→equalInType-NAT! i w a b eqi =
  →equalInTypeNOWRITEMOD (Mod.∀𝕎-□Func M aw eqi)
  where
    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                       → NOWRITEMODeq (equalInType i w' #NAT) w' a b)
    aw w1 e1 (n , c₁ , c₂) =
      →equalInType-NAT i w1 a b
        (Mod.∀𝕎-□ M (λ w2 e2 → n , #⇛!-#⇛ {w2} {a} {#NUM n} (∀𝕎-mon e2 c₁) , #⇛!-#⇛ {w2} {b} {#NUM n} (∀𝕎-mon e2 c₂))) ,
      (#⇛!-pres-#⇓→#⇓!-rev {w1} {#NUM n} {a} c₁ (#⇓→#⇓!-NUM w1 n) ,
       #⇛!-pres-#⇓→#⇓!-rev {w1} {#NUM n} {b} c₂ (#⇓→#⇓!-NUM w1 n))


abstract
  →equalInType-W : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (C : CTerm) (t u : CTerm)
                 → isType i w A
                 → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
                 → isType i w C
                 → □· w (λ w' _ → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t u)
                 → equalInType i w (#WT A B C) t u
  →equalInType-W i w A B C t u eqta eqtb eqtc h =
    EQTW
      A B C A B C (#⇛-refl w (#WT A B C)) (#⇛-refl w (#WT A B C))
      (eqTypes-mon (uni i) eqta)
      (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb)
      (eqTypes-mon (uni i) eqtc)
      (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqta))
      (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb))
      (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqtc)) ,
    Mod.∀𝕎-□Func M aw h
    where
      aw : ∀𝕎 w (λ w' e' → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t u
                         → weq (eqInType (uni i) w' (eqTypes-mon (uni i) eqta w' e'))
                               (λ a1 a2 eqa → eqInType (uni i) w' (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb w' e' a1 a2 eqa))
                               (eqInType (uni i) w' (eqTypes-mon (uni i) eqtc w' e')) w' t u)
      aw w' e' q =
        weq-ext-eq
          (λ a b x → equalInType→eqInType refl {eqTypes-mon (uni i) eqta w' e'} x)
          (λ f g a b ea1 ea2 x → eqInType→equalInType refl (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb w' e' a b ea2) x)
          (λ a b x → equalInType→eqInType refl {eqTypes-mon (uni i) eqtc w' e'} x)
          q


abstract
  equalInType-W : {u : ℕ} {w : 𝕎·} {A : CTerm} {B : CTerm0} {C : CTerm} {f g : CTerm}
                → isType u w A
                → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType u w' A a₁ a₂) → equalTypes u w' (sub0 a₁ B) (sub0 a₂ B))
                → isType u w C
                → □· w (λ w' _ → weq (equalInType u w' A) (λ a b ea → equalInType u w' (sub0 a B)) (equalInType u w' C) w' f g)
                → equalInType u w (#WT A B C) f g
  equalInType-W {u} {w} {A} {B} {C} {f} {g} ha hb hc eqi = →equalInType-W u w A B C f g ha hb hc eqi


abstract
  equalInType-W→ : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (C : CTerm) (t₁ t₂ : CTerm)
                   → equalInType i w (#WT A B C) t₁ t₂
                   → □· w (λ w' _ → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t₁ t₂)
  equalInType-W→ i w A B C t₁ t₂ (eqt , eqi) = concl (#WT A B C) (#WT A B C) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {t₁ t₂ : CTerm} (eqi : equalTerms u w eqt t₁ t₂)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {t₁' t₂' : CTerm} (eqi' : equalTerms u' w' eqt' t₁' t₂')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #WT A B C → T2' ≡ #WT A B C
                → □· w' (λ w'' _ → weq (equalInType u' w'' A) (λ a₁ b₁ eqa → equalInType u' w'' (sub0 a₁ B)) (equalInType u' w'' C) w'' t₁' t₂'))
            → T1 ≡ #WT A B C → T2 ≡ #WT A B C
            → □· w (λ w' _ → weq (equalInType u w' A) (λ a₁ b₁ eqa → equalInType u w' (sub0 a₁ B)) (equalInType u w' C) w' t₁ t₂)
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqQNAT (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → weq (equalTerms u w' (eqta w' e')) (λ a1 a2 eqa → equalTerms u w' (eqtb w' e' a1 a2 eqa)) (equalTerms u w' (eqtc w' e')) w' t₁ t₂
                             → weq (equalInType u w' A) (λ a b eqa → equalInType u w' (sub0 a B)) (equalInType u w' C) w' t₁ t₂)
          aw w' e' q =
            weq-ext-eq
              (λ a b z → eqInType→equalInType {u} {w'} {A} {A1} {A2} (#Winj1 {A} {B} {C} {A1} {B1} {C1} (#compAllVal x tt)) (eqta w' e') z)
              (λ f g a b ea1 ea2 z → equalInType→eqInType (→≡sub0 (#Winj2 {A} {B} {C} {A1} {B1} {C1} (#compAllVal x tt))) {eqtb w' e' a b ea1} z)
              (λ a b z → eqInType→equalInType {u} {w'} {C} {C1} {C2} (#Winj3 {A} {B} {C} {A1} {B1} {C1} (#compAllVal x tt)) (eqtc w' e') z)
              q
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqUNION (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqTSQUASH (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqNOWRITE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqNOREAD (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (WneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {t₁} {t₂} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → (at : at□· x w' e' z)
                              → equalTerms u w' z t₁ t₂
                              → □· w' (↑wPred' (λ w'' _ → weq (equalInType u w'' A) (λ a b eqa → equalInType u w'' (sub0 a B)) (equalInType u w'' C) w'' t₁ t₂) e'))
          aw w' e' z at j = Mod.∀𝕎-□Func M (λ w1 e1 z _ → z) (ind {u} {w'} {T1} {T2} z j (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2) (eqi : equalTerms i w eqt t₁ t₂)
              → T1 ≡ #WT A B C → T2 ≡ #WT A B C
              → □· w (λ w' _ → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t₁ t₂)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {t₁} {t₂} eqi
            → T1 ≡ #WT A B C → T2 ≡ #WT A B C
            → □· w (λ w' _ → weq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t₁ t₂))
          ind eqt t₁ t₂ eqi


abstract
  equalInType-M→ : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (C : CTerm) (t₁ t₂ : CTerm)
                   → equalInType i w (#MT A B C) t₁ t₂
                   → □· w (λ w' _ → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t₁ t₂)
  equalInType-M→ i w A B C t₁ t₂ (eqt , eqi) = concl (#MT A B C) (#MT A B C) eqt eqi refl refl
    where
      ind : {u : ℕ} {w : 𝕎·} {T1 T2 : CTerm} (eqt : equalTypes u w T1 T2) {t₁ t₂ : CTerm} (eqi : equalTerms u w eqt t₁ t₂)
            → ({u' : ℕ} {w' : 𝕎·} {T1' T2' : CTerm} (eqt' : equalTypes u' w' T1' T2') {t₁' t₂' : CTerm} (eqi' : equalTerms u' w' eqt' t₁' t₂')
                → <Type {ℕ→𝕌 u'} eqt' {ℕ→𝕌 u} eqt → T1' ≡ #MT A B C → T2' ≡ #MT A B C
                → □· w' (λ w'' _ → meq (equalInType u' w'' A) (λ a₁ b₁ eqa → equalInType u' w'' (sub0 a₁ B)) (equalInType u' w'' C) w'' t₁' t₂'))
            → T1 ≡ #MT A B C → T2 ≡ #MT A B C
            → □· w (λ w' _ → meq (equalInType u w' A) (λ a₁ b₁ eqa → equalInType u w' (sub0 a₁ B)) (equalInType u w' C) w' t₁ t₂)
--      ind {u} {w} {T1} {T2} (EQTNAT x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQNAT x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqQNAT (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTTNAT x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqTNAT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqQLT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTFREE x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqFREE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqPI (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTW A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqW (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTM A1 B1 C1 A2 B2 C2 x x₁ eqta eqtb eqtc exta extb extc) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 =
        Mod.∀𝕎-□Func M aw eqi
        where
          aw : ∀𝕎 w (λ w' e' → meq (equalTerms u w' (eqta w' e')) (λ a1 a2 eqa → equalTerms u w' (eqtb w' e' a1 a2 eqa)) (equalTerms u w' (eqtc w' e')) w' t₁ t₂
                             → meq (equalInType u w' A) (λ a b eqa → equalInType u w' (sub0 a B)) (equalInType u w' C) w' t₁ t₂)
          aw w' e' q =
            meq-ext-eq
              (λ a b z → eqInType→equalInType {u} {w'} {A} {A1} {A2} (#Minj1 {A} {B} {C} {A1} {B1} {C1} (#compAllVal x tt)) (eqta w' e') z)
              (λ f g a b ea1 ea2 z → equalInType→eqInType (→≡sub0 (#Minj2 {A} {B} {C} {A1} {B1} {C1} (#compAllVal x tt))) {eqtb w' e' a b ea1} z)
              (λ a b z → eqInType→equalInType {u} {w'} {C} {C1} {C2} (#Minj3 {A} {B} {C} {A1} {B1} {C1} (#compAllVal x tt)) (eqtc w' e') z)
              q
      ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqSUM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqSET (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqISECT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ x x₁ eqtA exta eqt1 eqt2) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqUNION (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqQTUNION (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqTSQUASH (compAllVal x tt))
--      ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqTTRUNC (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOWRITE x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqNOWRITE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOREAD x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqNOREAD (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqSUBSING (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqFFDEFS (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTPURE x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqPURE (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTNOSEQ x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqNOSEQ (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTTERM t1 t2 x x₁ x₂) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqTERM (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTUNIV i₁ p x x₁) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqUNIV (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 x x₁ eqtA exta) {t₁} {t₂} eqi ind eq1 eq2 rewrite eq1 | eq2 = ⊥-elim (MneqLIFT (compAllVal x tt))
      ind {u} {w} {T1} {T2} (EQTBAR x) {t₁} {t₂} eqi ind eq1 eq2 =
        Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
        where
          aw : ∀𝕎 w (λ w' e' → (z : equalTypes u w' T1 T2)
                              → (at : at□· x w' e' z)
                              → equalTerms u w' z t₁ t₂
                              → □· w' (↑wPred' (λ w'' _ → meq (equalInType u w'' A) (λ a b eqa → equalInType u w'' (sub0 a B)) (equalInType u w'' C) w'' t₁ t₂) e'))
          aw w' e' z at j = Mod.∀𝕎-□Func M (λ w1 e1 z _ → z) (ind {u} {w'} {T1} {T2} z j (<Type1 z (EQTBAR x) (<TypeBAR (ℕ→𝕌 u) w T1 T2 x w' e' z at)) eq1 eq2)

      concl : (T1 T2 : CTerm) (eqt : equalTypes i w T1 T2) (eqi : equalTerms i w eqt t₁ t₂)
              → T1 ≡ #MT A B C → T2 ≡ #MT A B C
              → □· w (λ w' _ → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t₁ t₂)
      concl T1 T2 eqt eqi =
        equalTerms-ind
          (λ {i} {w} {T1} {T2} eqt {t₁} {t₂} eqi
            → T1 ≡ #MT A B C → T2 ≡ #MT A B C
            → □· w (λ w' _ → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t₁ t₂))
          ind eqt t₁ t₂ eqi


→equalInType-M : (i : ℕ) (w : 𝕎·) (A : CTerm) (B : CTerm0) (C : CTerm) (t u : CTerm)
                  → isType i w A
                  → ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) (ea : equalInType i w' A a₁ a₂) → equalTypes i w' (sub0 a₁ B) (sub0 a₂ B))
                  → isType i w C
                  → □· w (λ w' _ → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t u)
                  → equalInType i w (#MT A B C) t u
→equalInType-M i w A B C t u eqta eqtb eqtc h =
  EQTM
    A B C A B C (#⇛-refl w (#MT A B C)) (#⇛-refl w (#MT A B C))
    (eqTypes-mon (uni i) eqta)
    (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb)
    (eqTypes-mon (uni i) eqtc)
    (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqta))
    (wPredDepExtIrr-eqInType2 {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb))
    (wPredExtIrr-eqInType (eqTypes-mon (uni i) eqtc)) ,
  Mod.∀𝕎-□Func M aw h
  where
    aw : ∀𝕎 w (λ w' e' → meq (equalInType i w' A) (λ a b eqa → equalInType i w' (sub0 a B)) (equalInType i w' C) w' t u
                       → meq (eqInType (uni i) w' (eqTypes-mon (uni i) eqta w' e'))
                             (λ a1 a2 eqa → eqInType (uni i) w' (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb w' e' a1 a2 eqa))
                             (eqInType (uni i) w' (eqTypes-mon (uni i) eqtc w' e')) w' t u)
    aw w' e' q =
      meq-ext-eq
        (λ a b x → equalInType→eqInType refl {eqTypes-mon (uni i) eqta w' e'} x)
        (λ f g a b ea1 ea2 x → eqInType→equalInType refl (equalInTypeFam→eqTypesFam {i} {w} {A} {B} {A} {B} (eqTypes-mon (uni i) eqta) eqtb w' e' a b ea2) x)
        (λ a b x → equalInType→eqInType refl {eqTypes-mon (uni i) eqtc w' e'} x)
        q


∈BAIRE→NAT→ : {i : ℕ} {w : 𝕎·} {F₁ F₂ f₁ f₂ : CTerm}
                → equalInType i w #BAIRE→NAT F₁ F₂
                → equalInType i w #BAIRE f₁ f₂
                → equalInType i w #NAT (#APPLY F₁ f₁) (#APPLY F₂ f₂)
∈BAIRE→NAT→ {i} {w} {F₁} {F₂} {f₁} {f₂} ∈F ∈f =
  equalInType-FUN→
    {i} {w} {#BAIRE} {#NAT} {F₁} {F₂} (≡CTerm→equalInType #BAIRE→NAT≡ ∈F) w (⊑-refl· _) f₁ f₂
    ∈f


eqTypesBAIRE : {w : 𝕎·} {i : ℕ} → isType i w #BAIRE
eqTypesBAIRE {w} {i} = ≡CTerm→eqTypes (sym #BAIRE≡) (sym #BAIRE≡) (eqTypesFUN← eqTypesNAT eqTypesNAT)


⇛NUMs→equalInType-NAT : (i : ℕ) (w : 𝕎·) (a b : CTerm) (k : ℕ)
                          → a #⇛ #NUM k at w
                          → b #⇛ #NUM k at w
                          → equalInType i w #NAT a b
⇛NUMs→equalInType-NAT i w a b k c1 c2 =
  →equalInType-NAT i w a b (Mod.∀𝕎-□ M (λ w1 e1 → k , ∀𝕎-mon e1 c1 , ∀𝕎-mon e1 c2))


⇛NUM→equalInType-NAT : {i : ℕ} {w : 𝕎·} {a : CTerm} {k : ℕ}
                        → a #⇛ #NUM k at w
                        → equalInType i w #NAT a (#NUM k)
⇛NUM→equalInType-NAT {i} {w} {a} {k} comp =
  ⇛NUMs→equalInType-NAT i w a (#NUM k) k comp (#⇛-refl w (#NUM k))

\end{code}
