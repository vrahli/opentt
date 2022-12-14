\begin{code}
{-# OPTIONS --rewriting #-}

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


module props4 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
              (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
              (X : ChoiceExt W C)
              (N : NewChoice W C K G)
              (E : Extensionality 0ℓ (lsuc(lsuc(L))))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_qtunion(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)



≡CTerm→equalInTypeₗ : {u : ℕ} {w : 𝕎·} {A a a' b : CTerm}
                      → a ≡ a'
                      → equalInType u w A a b
                      → equalInType u w A a' b
≡CTerm→equalInTypeₗ {u} {w} {A} {a} {a'} {b} e z rewrite e = z



≡CTerm→equalInTypeᵣ : {u : ℕ} {w : 𝕎·} {A a b b' : CTerm}
                      → b ≡ b'
                      → equalInType u w A a b
                      → equalInType u w A a b'
≡CTerm→equalInTypeᵣ {u} {w} {A} {a} {b} {b'} e z rewrite e = z



≡CTerm→∈Type : {u : ℕ} {w : 𝕎·} {A a a' : CTerm}
                      → a ≡ a'
                      → ∈Type u w A a
                      → ∈Type u w A a'
≡CTerm→∈Type {u} {w} {A} {a} {a'} e z rewrite e = z



-- MOVE to mod
∀𝕎-□Func2 : {w : 𝕎·} {f g h : wPred w}
                       → ∀𝕎 w (λ w' e' → f w' e' → g w' e' → h w' e')
                       → □· w f
                       → □· w g
                       → □· w h
∀𝕎-□Func2 {w} {f} {g} {h} aw a b = Mod.□Func M (Mod.∀𝕎-□Func M aw a) b


-- MOVE to mod
∀𝕎-□Func3 : {w : 𝕎·} {f g h k : wPred w}
                       → ∀𝕎 w (λ w' e' → f w' e' → g w' e' → h w' e' → k w' e')
                       → □· w f
                       → □· w g
                       → □· w h
                       → □· w k
∀𝕎-□Func3 {w} {f} {g} {h} aw a b c = Mod.□Func M (Mod.□Func M (Mod.∀𝕎-□Func M aw a) b) c



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
    aw : ∀𝕎 w (λ w' _ → Σ CTerm (λ x₁ → Σ CTerm (λ y₁ →
               #INL x #⇛ #INL x₁ at w' × #INL y #⇛ #INL y₁ at w' × equalInType n w' A x₁ y₁
               ⊎ #INL x #⇛ #INR x₁ at w' × #INL y #⇛ #INR y₁ at w' × equalInType n w' B x₁ y₁)))
    aw w' e' = x , y , inj₁ (#compAllRefl (#INL x) w' , #compAllRefl (#INL y) w' , equalInType-mon h w' e')


→INR-equalInType-UNION : {n : ℕ} {w : 𝕎·} {A B x y : CTerm}
                          → isType n w A
                          → equalInType n w B x y
                          → equalInType n w (#UNION A B) (#INR x) (#INR y)
→INR-equalInType-UNION {n} {w} {A} {B} {x} {y} ta h =
  →equalInType-UNION ta (fst h) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → Σ CTerm (λ x₁ → Σ CTerm (λ y₁ →
               #INR x #⇛ #INL x₁ at w' × #INR y #⇛ #INL y₁ at w' × equalInType n w' A x₁ y₁
               ⊎ #INR x #⇛ #INR x₁ at w' × #INR y #⇛ #INR y₁ at w' × equalInType n w' B x₁ y₁)))
    aw w' e' = x , y , inj₂ (#compAllRefl (#INR x) w' , #compAllRefl (#INR y) w' , equalInType-mon h w' e')



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
{-# TERMINATING #-}
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
equalInTypeFFDEFS→ {w} {i} {a} {b} {A} {u} (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (FFDEFSneqTCONST (compAllVal x₁ tt))
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
  Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
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




equalInType-LT-⇛NUM→ : {i : ℕ} {w : 𝕎·} {a b u v : CTerm} {n m : ℕ}
                        → a #⇛ #NUM m at w
                        → b #⇛ #NUM n at w
                        → equalInType i w (#LT a b) u v
                        → m < n
{-# TERMINATING #-}
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTNAT x x₁ , eqi) = ⊥-elim (LTneqNAT (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTQNAT x x₁ , eqi) = ⊥-elim (LTneqQNAT (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTTNAT x x₁ , eqi) = ⊥-elim (LTneqTNAT (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) =
  lower (Mod.□-const M {w} (Mod.∀𝕎-□Func M aw h))
  where
    h : □· w (λ w' _ → #lift-<NUM-pair w' a b)
    h rewrite LTinj1 (compAllVal x tt) | LTinj2 (compAllVal x tt) = eqi

    aw : ∀𝕎 w (λ w' e' → #lift-<NUM-pair w' a b → Lift (lsuc L) (m < n))
    aw w1 e1 (lift (n1 , m1 , comp1 , comp2 , ltnm))
      rewrite NUMinj (⇓-val-det tt tt comp1 (lower (compa w1 e1)))
            | NUMinj (⇓-val-det tt tt comp2 (lower (compb w1 e1))) = lift ltnm
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTQLT a1 a2 b1 b2 x x₁ x₂ x₃ , eqi) = ⊥-elim (LTneqQLT (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTFREE x x₁ , eqi) = ⊥-elim (LTneqFREE (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTPI A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LTneqPI (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTSUM A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LTneqSUM (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTW A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LTneqW (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTSET A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LTneqSET (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTISECT A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (LTneqISECT (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTTUNION A1 B1 A2 B2 x x₁ eqta eqtb exta extb , eqi) = ⊥-elim (LTneqTUNION (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTEQ a1 b1 a2 b2 A B x x₁ eqtA exta eqt1 eqt2 , eqi) = ⊥-elim (LTneqEQ (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (LTneqUNION (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTQTUNION A1 B1 A2 B2 x x₁ eqtA eqtB exta extb , eqi) = ⊥-elim (LTneqQTUNION (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTSQUASH A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LTneqTSQUASH (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTTRUNC A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LTneqTTRUNC (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTCONST A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LTneqTCONST (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTSUBSING A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LTneqSUBSING (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTPURE x x₁ , eqi) = ⊥-elim (LTneqPURE (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQFFDEFS A1 A2 x1 x2 x x₁ eqtA exta eqx , eqi) = ⊥-elim (LTneqFFDEFS (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTUNIV i₁ p x x₁ , eqi) = ⊥-elim (LTneqUNIV (compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTLIFT A1 A2 x x₁ eqtA exta , eqi) = ⊥-elim (LTneqLIFT(compAllVal x tt))
equalInType-LT-⇛NUM→ {i} {w} {a} {b} {u} {v} {n} {m} compa compb (EQTBAR x , eqi) =
  lower (Mod.□-const M {w} (Mod.∀𝕎-□'-□ M x aw eqi))
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes (uni i) w' (#LT a b) (#LT a b))
                        → eqInType (uni i) w' z u v → Lift (lsuc L) (m < n))
    aw w1 e1 z eqj = lift (equalInType-LT-⇛NUM→ {i} {w1} {a} {b} {u} {v} {n} {m} (∀𝕎-mon e1 compa) (∀𝕎-mon e1 compb) (z , eqj))



→equalInType-NAT! : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                    → □· w (λ w' _ → #⇛!sameℕ w' a b)
                    → equalInType i w #NAT! a b
→equalInType-NAT! i w a b eqi =
  isTypeNAT! ,
  Mod.∀𝕎-□Func M aw eqi
  where
    aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                       → TCONSTeq (λ t1 t2 → □· w' (λ w'' _ → #strongMonEq w'' t1 t2)) w' a b)
    aw w1 e1 (n , c₁ , c₂) =
      Mod.∀𝕎-□ M (λ w2 e2 → n , #⇛!-#⇛ {w2} {a} {#NUM n} (∀𝕎-mon e2 c₁) , #⇛!-#⇛ {w2} {b} {#NUM n} (∀𝕎-mon e2 c₂)) ,
      #⇛!-pres-#⇓→#⇓!-rev {w1} {#NUM n} {a} c₁ (#⇓→#⇓!-NUM w1 n) ,
      #⇛!-pres-#⇓→#⇓!-rev {w1} {#NUM n} {b} c₂ (#⇓→#⇓!-NUM w1 n)

\end{code}
