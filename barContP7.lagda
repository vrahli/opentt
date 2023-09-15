\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --lossy-unification #-}
--{-# OPTIONS --auto-inline #-}


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
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional
open import Axiom.ExcludedMiddle


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import choiceExt
open import choiceVal
open import compatible
open import getChoice
open import progress
open import freeze
open import newChoice
open import mod
--open import choiceBar
open import encode


module barContP7 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
                 (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
--open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
open import terms9 --(W)(C)(K)(G)(X)(N)(EC)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalTypes-#⇛-left-right-rev)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (→equalInType-NAT! ; equalInType-W→)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇓sameℕ)
--open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)


lowerVars3-fvars-CTerm2⊆[] : (a : CTerm2) → lowerVars (lowerVars (lowerVars (fvars ⌜ a ⌝))) ⊆ []
lowerVars3-fvars-CTerm2⊆[] a {x} i = ⊥-elim (k2 k1)
  where
    i1 : suc x ∈ lowerVars (lowerVars (fvars ⌜ a ⌝))
    i1 = ∈lowerVars→ x (lowerVars (lowerVars (fvars ⌜ a ⌝))) i

    i2 : suc (suc x) ∈ lowerVars (fvars ⌜ a ⌝)
    i2 = ∈lowerVars→ (suc x) (lowerVars (fvars ⌜ a ⌝)) i1

    i3 : suc (suc (suc x)) ∈ fvars ⌜ a ⌝
    i3 = ∈lowerVars→ (suc (suc x)) (fvars ⌜ a ⌝) i2

    k1 : suc (suc (suc x)) ∈ 0 ∷ 1 ∷ [ 2 ]
    k1 = ⊆?→⊆ (CTerm2.closed a) i3

    k2 : suc (suc (suc x)) ∈ 0 ∷ 1 ∷ [ 2 ] → ⊥
    k2 (there (there (here ())))
    k2 (there (there (there ())))


lowerVars3-fvars-CTerm2≡[] : (a : CTerm2) → lowerVars (lowerVars (lowerVars (fvars ⌜ a ⌝))) ≡ []
lowerVars3-fvars-CTerm2≡[] a = ⊆[]→≡[] (lowerVars3-fvars-CTerm2⊆[] a)


#WREC : CTerm → CTerm2 → CTerm
#WREC a b = ct (WREC ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : # WREC ⌜ a ⌝ ⌜ b ⌝
    c rewrite CTerm.closed a | lowerVars3-fvars-CTerm2≡[] b = refl


#[3]DECIDE : CTerm3 → CTerm4 → CTerm4 → CTerm3
#[3]DECIDE a b c = ct3 (DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) d
  where
    d : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] DECIDE ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    d = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝) ++ lowerVars (fvars ⌜ c ⌝)} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                    (⊆++ (lowerVars-fvars-[0,1,2,3,4] {fvars ⌜ b ⌝} (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed b)))
                          (lowerVars-fvars-[0,1,2,3,4] {fvars ⌜ c ⌝} (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]} (CTerm4.closed c)))))


#BAIRE!≡ : #BAIRE! ≡ #FUN #NAT #NAT!
#BAIRE!≡ = CTerm≡ refl


APPLY-∈BAIRE-NUM→ : (i : ℕ) (w : 𝕎·) (f : CTerm) (n : ℕ)
                      → ∈Type i w #BAIRE f
                      → ∈Type i w #NAT (#APPLY f (#NUM n))
APPLY-∈BAIRE-NUM→ i w f n f∈ =
  equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ f∈) w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


APPLY-∈BAIRE!-NUM→ : (i : ℕ) (w : 𝕎·) (f : CTerm) (n : ℕ)
                      → ∈Type i w #BAIRE! f
                      → ∈Type i w #NAT! (#APPLY f (#NUM n))
APPLY-∈BAIRE!-NUM→ i w f n f∈ =
  equalInType-FUN→ (≡CTerm→equalInType #BAIRE!≡ f∈) w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


APPLY-≡∈BAIRE-NUM→ : (i : ℕ) (w : 𝕎·) (f g : CTerm) (n : ℕ)
                      → equalInType i w #BAIRE f g
                      → equalInType i w #NAT (#APPLY f (#NUM n)) (#APPLY g (#NUM n))
APPLY-≡∈BAIRE-NUM→ i w f g n f∈ =
  equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ f∈) w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


APPLY-≡∈BAIRE!-NUM→ : (i : ℕ) (w : 𝕎·) (f g : CTerm) (n : ℕ)
                      → equalInType i w #BAIRE! f g
                      → equalInType i w #NAT! (#APPLY f (#NUM n)) (#APPLY g (#NUM n))
APPLY-≡∈BAIRE!-NUM→ i w f g n f∈ =
  equalInType-FUN→ (≡CTerm→equalInType #BAIRE!≡ f∈) w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


BAIRE2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE f) → 𝕊
BAIRE2𝕊 kb {i} {w} {f} f∈ n = fst j
  where
    j : NATmem w (#APPLY f (#NUM n))
    j = kb (equalInType-NAT→ i w _ _ (APPLY-∈BAIRE-NUM→ i w f n f∈)) w (⊑-refl· w)


BAIRE!2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE! f) → 𝕊
BAIRE!2𝕊 kb {i} {w} {f} f∈ n = fst j
  where
    j : #⇛!sameℕ w (#APPLY f (#NUM n)) (#APPLY f (#NUM n))
    j = kb (equalInType-NAT!→ i w _ _ (APPLY-∈BAIRE!-NUM→ i w f n f∈)) w (⊑-refl· w)


#⇛NUM→equalInType-NAT : (i : ℕ) (w : 𝕎·) (a : CTerm) (k : ℕ)
                          → a #⇛ #NUM k at w
                          → equalInType i w #NAT a (#NUM k)
#⇛NUM→equalInType-NAT i w a k ea =
  →equalInType-NAT i w _ _ (Mod.∀𝕎-□ M (λ w1 e1 → k , ∀𝕎-mon e1 ea , #⇛-refl w1 (#NUM k)))


NATeq→#⇛NUMₗ : {w : 𝕎·} {a b : CTerm} {k : ℕ}
                → NATeq w a b
                → b #⇛ #NUM k at w
                → a #⇛ #NUM k at w
NATeq→#⇛NUMₗ {w} {a} {b} {k} (j , c1 , c2) c
  rewrite NUMinj (⇛-val-det {w} {⌜ b ⌝} {NUM j} {NUM k} tt tt c2 c) = c1


#⇛!sameℕ→#⇛!NUMₗ : {w : 𝕎·} {a b : CTerm} {k : ℕ}
                      → #⇛!sameℕ w a b
                      → b #⇛! #NUM k at w
                      → a #⇛! #NUM k at w
#⇛!sameℕ→#⇛!NUMₗ {w} {a} {b} {k} (j , c1 , c2) c
  rewrite NUMinj (⇛!-val-det {w} {⌜ b ⌝} {NUM j} {NUM k} tt tt c2 c) = c1


BAIRE2𝕊-equalInBAIRE : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE f)
                        → equalInType i w #BAIRE f (#MSEQ (BAIRE2𝕊 kb f∈))
BAIRE2𝕊-equalInBAIRE kb {i} {w} {f} f∈ =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    s : 𝕊
    s = BAIRE2𝕊 kb f∈

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY f a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ ea =
      →equalInType-NAT i w1 _  _ (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 _ _ ea))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂ → NATeq w' (#APPLY f a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (k , c1 , c2) = s k , j3 , APPLY-MSEQ⇛ w2 s ⌜ a₂ ⌝ k c2
          where
            j1 : #APPLY f (#NUM k) #⇛ #NUM (s k) at w
            j1 = fst (snd (kb (equalInType-NAT→ i w _ _ (APPLY-∈BAIRE-NUM→ i w f k f∈)) w (⊑-refl· w)))

            j2 : NATeq w2 (#APPLY f a₁) (#APPLY f (#NUM k))
            j2 = kb (equalInType-NAT→ i w2 _ _ (equalInType-FUN→ (≡CTerm→equalInType #BAIRE≡ f∈) w2 (⊑-trans· e1 e2) a₁ (#NUM k) (#⇛NUM→equalInType-NAT i w2 a₁ k c1))) w2 (⊑-refl· w2)

            j3 : #APPLY f a₁ #⇛ #NUM (s k) at w2
            j3 = NATeq→#⇛NUMₗ {w2} {#APPLY f a₁} {#APPLY f (#NUM k)} j2 (∀𝕎-mon (⊑-trans· e1 e2) j1)


APPLY-NUM-MSEQ⇛! : (w : 𝕎·) (s : 𝕊) (k : ℕ)
                    → APPLY (MSEQ s) (NUM k) ⇛! NUM (s k) at w
APPLY-NUM-MSEQ⇛! w s k w1 e1 = lift (2 , refl)


BAIRE!2𝕊-equalInNAT! : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE! f) (k : ℕ)
                         → equalInType i w #NAT! (#APPLY f (#NUM k)) (#APPLY (#MSEQ (BAIRE!2𝕊 kb f∈)) (#NUM k))
BAIRE!2𝕊-equalInNAT! kb {i} {w} {f} f∈ k =
  →equalInType-NAT! i w (#APPLY f (#NUM k)) (#APPLY (#MSEQ (BAIRE!2𝕊 kb f∈)) (#NUM k)) (Mod.∀𝕎-□ M aw)
  where
    s : 𝕊
    s = BAIRE!2𝕊 kb f∈

    j1 : #APPLY f (#NUM k) #⇛! #NUM (s k) at w
    j1 = fst (snd (kb (equalInType-NAT!→ i w _ _ (APPLY-∈BAIRE!-NUM→ i w f k f∈)) w (⊑-refl· w)))

    aw : ∀𝕎 w (λ w' _ → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY (#MSEQ (BAIRE!2𝕊 kb f∈)) (#NUM k)))
    aw w1 e1 = s k , ∀𝕎-mon e1 j1 , APPLY-NUM-MSEQ⇛! w1 s k


#tab : (F : CTerm) (k : ℕ) (f : CTerm) → CTerm
#tab F k f = #APPLY2 (#loop F) (#NUM k) f


wmem : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t : CTerm) → Set(lsuc(L))
wmem eqa eqb w t = weq₀ eqa eqb w t t


BAIRE2list : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE f) (k : ℕ) → CTerm
BAIRE2list kb {i} {w} {f} f∈ k = seq2list (BAIRE2𝕊 kb f∈) k


∈Type-IndBarB→ : (i : ℕ) (w : 𝕎·) (b : CTerm)
                   → ∈Type i w #IndBarB b
                   → □· w (λ w' _ → Σ CTerm (λ t → Σ ℕ (λ n → b #⇛! #INL t at w' × t #⇛ #NUM n at w'))
                                      ⊎ Σ CTerm (λ t → b #⇛! #INR t at w'))
∈Type-IndBarB→ i w b b∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-UNION₀!→ b∈))
  where
    aw : ∀𝕎 w (λ w' e' → UNION₀!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' b b
                        → □· w' (↑wPred' (λ w'' _ → Σ CTerm (λ t → Σ ℕ (λ n → b #⇛! #INL t at w'' × t #⇛ #NUM n at w''))
                                                      ⊎ Σ CTerm (λ t → b #⇛! #INR t at w'')) e'))
    aw w1 e1 (x , y , inj₁ (c1 , c2 , eqi)) =
      Mod.∀𝕎-□Func M (λ w2 e2 (j , d1 , d2) z → inj₁ (x , j , ∀𝕎-mon e2 c1 , d1)) (equalInType-NAT→ i w1 _ _ eqi)
    aw w1 e1 (x , y , inj₂ (c1 , c2 , eqi)) =
      Mod.∀𝕎-□ M (λ w2 e2 z → inj₂ (x , ∀𝕎-mon e2 c1))


equalInType-IndBarB→ : (i : ℕ) (w : 𝕎·) (a b : CTerm)
                       → equalInType i w #IndBarB a b
                       → □· w (λ w' _ → Σ CTerm (λ t → Σ CTerm (λ u → Σ ℕ (λ n → a #⇛! #INL t at w' × b #⇛! #INL u at w' × t #⇛ #NUM n at w' × u #⇛ #NUM n at w')))
                                         ⊎ Σ CTerm (λ t → Σ CTerm (λ u → a #⇛! #INR t at w' × b #⇛! #INR u at w')))
equalInType-IndBarB→ i w a b b∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-UNION₀!→ b∈))
  where
    aw : ∀𝕎 w (λ w' e' → UNION₀!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' a b
                        → □· w' (↑wPred' (λ w' _ → Σ CTerm (λ t → Σ CTerm (λ u → Σ ℕ (λ n → a #⇛! #INL t at w' × b #⇛! #INL u at w' × t #⇛ #NUM n at w' × u #⇛ #NUM n at w')))
                                                     ⊎ Σ CTerm (λ t → Σ CTerm (λ u → a #⇛! #INR t at w' × b #⇛! #INR u at w')))
                                          e'))
    aw w1 e1 (x , y , inj₁ (c1 , c2 , eqi)) =
      Mod.∀𝕎-□Func
        M (λ w2 e2 (j , d1 , d2) z → inj₁ (x , y , j , ∀𝕎-mon e2 c1 , ∀𝕎-mon e2 c2 , d1 , d2))
        (equalInType-NAT→ i w1 _ _ eqi)
    aw w1 e1 (x , y , inj₂ (c1 , c2 , eqi)) =
      Mod.∀𝕎-□ M (λ w2 e2 z → inj₂ (x , y , ∀𝕎-mon e2 c1 , ∀𝕎-mon e2 c2))


followDA2 : (k k' r s : Term) → Term
followDA2 k k' r s =
  LET (APPLY s k)
      (APPLY2 (shiftUp 0 r) (VAR 0) (shiftUp 0 k'))


followDA : (k r s : Term) → Term
followDA k r s =
  LET (SUC k)
      (followDA2 (shiftUp 0 k) (VAR 0) (shiftUp 0 r) (shiftUp 0 s))


followD : (k a r s : Term) → Term
followD k a r s =
  DECIDE a
         (VAR 0) -- i
         (followDA (shiftUp 0 k) (shiftUp 0 r) (shiftUp 0 s))


followBT : (a r s : Term) → Term
followBT a r s =
  LAMBDA {--k--}
    (followD (VAR 0) (shiftUp 0 a) (shiftUp 0 r) (shiftUp 0 s))


followB : (s : Term) → Term
followB s = followBT (VAR 0) (VAR 2) (shiftUp 0 (shiftUp 0 (shiftUp 0 s)))


follow : (s w : Term) (n : ℕ) → Term
follow s w n =
  APPLY (WREC w (followB s)) -- k
        (NUM n)
        -- VAR 0: k
        -- VAR 1: a
        -- VAR 2: f
        -- VAR 3: r


#follow : (s w : CTerm) (n : ℕ) → CTerm
#follow s w n =
  #APPLY (#WREC w (#[2]LAMBDA (#[3]DECIDE #[3]VAR1 -- a
                                          #[4]VAR0 -- i
                                          (#[4]LET (#[4]SUC #[4]VAR1)
                                                   (#[5]LET (#[5]APPLY (#[5]shiftUp0 (#[4]shiftUp0 (#[3]shiftUp0 (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 s))))))
                                                                       #[5]VAR2) --k
                                                            (#[6]APPLY2 #[6]VAR6 -- r
                                                                        #[6]VAR0
                                                                        #[6]VAR1)))))) -- k
         (#NUM n)


-- sanity check
⌜#follow⌝≡ : (s w : CTerm) (n : ℕ) → ⌜ #follow s w n ⌝ ≡ follow ⌜ s ⌝ ⌜ w ⌝ n
⌜#follow⌝≡ s w n = refl


≡ₗr→⇓from-to : {w w' : 𝕎·} {a b c : Term} → b ≡ a → a ⇓ c from w to w' → b ⇓ c from w to w'
≡ₗr→⇓from-to {w} {w'} {a} {b} {c} e comp rewrite e = comp


sub3-followB≡ : (a g f : CTerm)
                → sub (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) (sub (shiftUp 0 ⌜ g ⌝) (sub (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) (followB ⌜ f ⌝)))
                   ≡ followBT ⌜ a ⌝ (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) ⌜ f ⌝
sub3-followB≡ a g f
   rewrite #shiftUp 0 a
         | #shiftUp 0 a
         | #shiftUp 0 g
         | #shiftUp 0 a
         | #shiftUp 0 a
         | #shiftUp 0 a
         | #shiftUp 0 a
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 3 f
         | #shiftUp 6 f
         | #shiftUp 7 f
         | #shiftUp 7 f
         | #shiftUp 7 f
         | #shiftUp 7 f
         | #shiftUp 7 f
         | #shiftUp 0 g
         | #shiftUp 0 g
         | #shiftUp 0 g
         | #shiftUp 0 g
         | #shiftUp 1 g
         | #shiftUp 1 g
         | #shiftUp 1 g
         | #shiftUp 1 g
         | #shiftUp 1 g
         | #shiftDown 1 a
         | #shiftDown 5 g
         | #shiftDown 11 f
         | #subv 1 ⌜ g ⌝ ⌜ a ⌝ (CTerm.closed a)
         | #subv 3 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
         | #shiftDown 1 a
         | #shiftDown 3 f
         | #subv 3 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
         | #shiftDown 3 f
         | #subv 1 (LAMBDA (WREC (APPLY ⌜ g ⌝ (VAR 0)) (LAMBDA (DECIDE (VAR 1) (VAR 0) (LET (SUC (VAR 1)) (LET (APPLY ⌜ f ⌝ (VAR 2)) (APPLY2 (VAR 6) (VAR 0) (VAR 1)))))))) ⌜ a ⌝ (CTerm.closed a)
         | #subv 3 (LAMBDA (WREC (APPLY ⌜ g ⌝ (VAR 0)) (LAMBDA (DECIDE (VAR 1) (VAR 0) (LET (SUC (VAR 1)) (LET (APPLY ⌜ f ⌝ (VAR 2)) (APPLY2 (VAR 6) (VAR 0) (VAR 1)))))))) ⌜ f ⌝ (CTerm.closed f)
         | #shiftDown 1 a
         | #shiftDown 3 f
   = refl


sub-followD≡ : (k : ℕ) (a g f : CTerm)
               → sub (NUM k) (followD (VAR 0) (shiftUp 0 ⌜ a ⌝) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
                  ≡ followD (NUM k) ⌜ a ⌝ (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) ⌜ f ⌝
sub-followD≡ k a g f
  rewrite #shiftUp 0 a
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 3 f
        | #shiftUp 6 f
        | #shiftUp 7 f
        | #shiftUp 7 f
        | #shiftUp 7 f
        | #shiftUp 7 f
        | #shiftUp 0 g
        | #shiftUp 1 g
        | #shiftUp 1 g
        | #shiftUp 1 g
        | #shiftUp 1 g
        | #subv 0 ⌜ #NUM k ⌝ ⌜ a ⌝ (CTerm.closed a)
        | #subv 4 ⌜ #NUM k ⌝ ⌜ g ⌝ (CTerm.closed g)
        | #subv 2 ⌜ #NUM k ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #subv 10 ⌜ #NUM k ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 0 a
        | #shiftDown 4 g
        | #shiftDown 10 f
        | #shiftDown 2 f
  = refl


#follow-INL⇓from-to : (w w' : 𝕎·) (I a g f t : CTerm) (k n : ℕ)
                      → I #⇓ #SUP a g from w to w'
                      → a #⇛! #INL t at w
                      → t #⇛ #NUM n at w
                      → Σ 𝕎· (λ w'' → #follow f I k #⇓ #NUM n from w to w'')
#follow-INL⇓from-to w w' I a g f t k n cI ca cn =
  fst cn' ,
  ⇓-trans₂
    (APPLY⇓ (NUM k) (WREC⇓ (followB ⌜ f ⌝) cI))
    (⇓-trans₂
      (APPLY⇓ (NUM k) (WREC-SUP⇓ w' ⌜ a ⌝ ⌜ g ⌝ (followB ⌜ f ⌝)))
      (≡ₗr→⇓from-to
        (≡APPLY (sub3-followB≡ a g f) refl)
        (⇓-trans₂
          (APPLY-LAMBDA⇓  w'
            (followD (VAR 0) (shiftUp 0 ⌜ a ⌝) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
            (NUM k))
          (≡ₗr→⇓from-to
            (sub-followD≡ k a g f)
            (⇓-trans₂
               (DECIDE⇓ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
                        (lower (ca w' (⇓from-to→⊑ {w} {w'} {⌜ I ⌝} {⌜ #SUP a g ⌝} cI))))
               (⇓-trans₂
                  (DECIDE-INL⇓ w' ⌜ t ⌝ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)))
                  (≡ₗr→⇓from-to (sub-VAR0 ⌜ t ⌝) (snd cn'))))))))
  where
    cn' : Σ 𝕎· (λ w'' → t #⇓ #NUM n from w' to w'')
    cn' = #⇓→from-to {w'} {t} {#NUM n} (lower (cn w' (⇓from-to→⊑ {w} {w'} {⌜ I ⌝} {⌜ #SUP a g ⌝} cI)))


-- INL case - this does not depend on f
#follow-INL⇓ : (w : 𝕎·) (I a g f t : CTerm) (k n : ℕ)
               → I #⇓ #SUP a g at w
               → a #⇛! #INL t at w
               → t #⇛ #NUM n at w
               → #follow f I k #⇓ #NUM n at w
#follow-INL⇓ w I a g f t k n cI ca cn =
  #⇓from-to→#⇓ {w} {fst c} {#follow f I k} {#NUM n} (snd c)
  where
    cI' : Σ 𝕎· (λ w' → I #⇓ #SUP a g from w to w')
    cI' = #⇓→from-to {w} {I} {#SUP a g} cI

    c : Σ 𝕎· (λ w'' → #follow f I k #⇓ #NUM n from w to w'')
    c = #follow-INL⇓from-to w (fst cI') I a g f t k n (snd cI') ca cn


-- INL case - this does not depend on f
#follow-INL⇛ : (w : 𝕎·) (I a g f t : CTerm) (k n : ℕ)
               → I #⇛ #SUP a g at w
               → a #⇛! #INL t at w
               → t #⇛ #NUM n at w
               → #follow f I k #⇛ #NUM n at w
#follow-INL⇛ w I a g f t k n cI ca cn w1 e1 =
  lift (#follow-INL⇓ w1 I a g f t k n (lower (cI w1 e1)) (∀𝕎-mon e1 ca) (∀𝕎-mon e1 cn))


sub-followDA≡ : (t f g : CTerm) (k : ℕ)
                → sub ⌜ t ⌝ (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
                   ≡ followDA (NUM k) (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) ⌜ f ⌝
sub-followDA≡ t f g k
   rewrite #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 0 f
         | #shiftUp 3 f
         | #shiftUp 3 f
         | #shiftUp 4 f
         | #shiftUp 6 f
         | #shiftUp 7 f
         | #shiftUp 7 f
         | #shiftUp 7 f
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 t
         | #shiftUp 0 g
         | #shiftUp 1 g
         | #shiftUp 1 g
         | #shiftUp 1 g
         | #subv 3 ⌜ t ⌝ ⌜ g ⌝ (CTerm.closed g)
         | #subv 1 ⌜ t ⌝ ⌜ f ⌝ (CTerm.closed f)
         | #subv 9 ⌜ t ⌝ ⌜ f ⌝ (CTerm.closed f)
         | #shiftDown 3 g
         | #shiftDown 1 f
         | #shiftDown 0 f
         | #shiftDown 9 f
   = refl


sub-followDA2≡ : (m k : ℕ) (f g : CTerm)
                 → sub (NUM m) (followDA2 (shiftUp 0 (NUM k)) (VAR 0) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
                    ≡ followDA2 (NUM k) (NUM m) (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) ⌜ f ⌝
sub-followDA2≡ m k f g
  rewrite #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 3 f
        | #shiftUp 6 f
        | #shiftUp 7 f
        | #shiftUp 7 f
        | #shiftUp 0 g
        | #shiftUp 1 g
        | #shiftUp 1 g
        | #subv 2 ⌜ #NUM m ⌝ ⌜ g ⌝ (CTerm.closed g)
        | #subv 0 ⌜ #NUM m ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #subv 8 ⌜ #NUM m ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 2 g
        | #shiftDown 0 f
        | #shiftDown 8 f
  = refl


sub-WREC-followB : (a g f : CTerm)
                   → sub ⌜ a ⌝ (WREC (APPLY (shiftUp 0 ⌜ g ⌝) (VAR 0)) (shiftUp 3 (followB ⌜ f ⌝)))
                      ≡ WREC (APPLY ⌜ g ⌝ ⌜ a ⌝) (followB ⌜ f ⌝)
sub-WREC-followB a g f
  rewrite #shiftUp 0 a
        | #shiftUp 0 a
        | #shiftUp 0 a
        | #shiftUp 0 a
        | #shiftUp 0 a
        | #shiftUp 0 a
        | #shiftUp 0 a
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 3 f
        | #shiftUp 6 f
        | #shiftUp 0 g
        | #subv 0 ⌜ a ⌝ ⌜ g ⌝ (CTerm.closed g)
        | #subv 6 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 0 a
        | #shiftDown 6 a
        | #shiftDown 0 g
        | #shiftDown 6 f
  = refl


sub-APPLY2-WRECr-followB : (j k : ℕ) (f g : CTerm)
                           → sub (NUM j) (APPLY2 (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (VAR 0) (NUM (suc k)))
                              ≡ APPLY2 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) (NUM j) (NUM (suc k))
sub-APPLY2-WRECr-followB j k f g
  rewrite #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 0 f
        | #shiftUp 6 f
        | #shiftUp 7 f
        | #shiftUp 0 g
        | #shiftUp 1 g
        | #subv 1 ⌜ #NUM j ⌝ ⌜ g ⌝ (CTerm.closed g)
        | #subv 7 ⌜ #NUM j ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 1 g
        | #shiftDown 7 f
  = refl


#follow-INR⇓from-to : (w w' : 𝕎·) (I a g f t : CTerm) (k j : ℕ)
                      → I #⇓ #SUP a g from w to w'
                      → a #⇛! #INR t at w
                      → #APPLY f (#NUM k) #⇛! #NUM j at w'
                      → #follow f I k #⇓ #follow f (#APPLY g (#NUM j)) (suc k) from w to w'
#follow-INR⇓from-to w w' I a g f t k j cI ca cj =
  ⇓-trans₂
    (APPLY⇓ (NUM k) (WREC⇓ (followB ⌜ f ⌝) cI))
    (⇓-trans₂
      (APPLY⇓ (NUM k) (WREC-SUP⇓ w' ⌜ a ⌝ ⌜ g ⌝ (followB ⌜ f ⌝)))
      (≡ₗr→⇓from-to
        (≡APPLY (sub3-followB≡ a g f) refl)
        (⇓-trans₂
          (APPLY-LAMBDA⇓ w' (followD (VAR 0) (shiftUp 0 ⌜ a ⌝) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)) (NUM k))
          (≡ₗr→⇓from-to
            (sub-followD≡ k a g f)
            (⇓-trans₂
               (DECIDE⇓ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
                        (lower (ca w' e')))
               (⇓-trans₂
                  (DECIDE-INR⇓ w' ⌜ t ⌝ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)))
                  (≡ₗr→⇓from-to
                    (sub-followDA≡ t f g k)
                    (⇓-trans₂
                      (LET⇓ (followDA2 (shiftUp 0 (NUM k)) (VAR 0) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)) (SUC-NUM⇓ w' k))
                      (⇓-trans₂
                        (LET-val⇓ w' (NUM (suc k)) (followDA2 (shiftUp 0 (NUM k)) (VAR 0) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)) tt)
                        (≡ₗr→⇓from-to
                          (sub-followDA2≡ (suc k) k f g)
                          (⇓-trans₂
                            (LET⇓ (APPLY2 (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (VAR 0) (NUM (suc k))) (lower (cj w' (⊑-refl· w'))))
                            (⇓-trans₂
                               (LET-val⇓ w' (NUM j) (APPLY2 (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (VAR 0) (NUM (suc k))) tt)
                               (≡ₗr→⇓from-to
                                 (sub-APPLY2-WRECr-followB j k f g)
                                 (⇓-trans₂
                                   (APPLY⇓ (NUM (suc k)) (APPLY-LAMBDA⇓ w' (WREC (APPLY (shiftUp 0 ⌜ g ⌝) (VAR 0)) (shiftUp 3 (followB ⌜ f ⌝))) (NUM j)))
                                   (≡ₗr→⇓from-to
                                     (≡APPLY (sub-WREC-followB (#NUM j) g f) refl)
                                     (⇓from-to-refl _ w'))))))))))))))))
  where
    e' : w ⊑· w'
    e' = ⇓from-to→⊑ {w} {w'} {⌜ I ⌝} {⌜ #SUP a g ⌝} cI


-- INR case - this case depends on f
#follow-INR⇓ : (w : 𝕎·) (I a g f t : CTerm) (k j : ℕ)
               → I #⇓ #SUP a g at w
               → a #⇛! #INR t at w
               → #APPLY f (#NUM k) #⇛! #NUM j at w
               → #follow f I k #⇓ #follow f (#APPLY g (#NUM j)) (suc k) at w
#follow-INR⇓ w I a g f t k j cI ca cj =
  #⇓from-to→#⇓
    {w} {fst cI'} {#follow f I k} {#follow f (#APPLY g (#NUM j)) (suc k)}
    (#follow-INR⇓from-to w (fst cI') I a g f t k j (snd cI') ca (∀𝕎-mon e' cj))
  where
    cI' : Σ 𝕎· (λ w' → I #⇓ #SUP a g from w to w')
    cI' = #⇓→from-to {w} {I} {#SUP a g} cI

    e' : w ⊑· fst cI'
    e' = ⇓from-to→⊑ {w} {fst cI'} {⌜ I ⌝} {⌜ #SUP a g ⌝} (snd cI')


#follow-INR⇛ : (w : 𝕎·) (I a g f t : CTerm) (k j : ℕ)
                → I #⇛ #SUP a g at w
                → a #⇛! #INR t at w
                → #APPLY f (#NUM k) #⇛! #NUM j at w
                → #follow f I k #⇛ #follow f (#APPLY g (#NUM j)) (suc k) at w
#follow-INR⇛ w I a g f t k j cI ca cj w1 e1 =
  lift (#follow-INR⇓ w1 I a g f t k j (lower (cI w1 e1)) (∀𝕎-mon e1 ca) (∀𝕎-mon e1 cj))


INR→!≡∈Type-IndBarC : (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T x a b c : CTerm)
                     → type-#⇛!-NUM P T
                     → x #⇛! #INR a at w
                     → equalInType i w (sub0 x (#IndBarC T)) b c
                     → □· w (λ w' _ → Σ ℕ (λ n → b #⇛! #NUM n at w' × c #⇛! #NUM n at w' × P n))
INR→!≡∈Type-IndBarC i w P T x a b c tyn comp j rewrite sub0-IndBarC≡ T x =
  Mod.∀𝕎-□Func M (λ w1 e1 z → z) (tyn j1)
  where
    j1 : equalInType i w (#NOWRITEMOD T) b c
    j1 = equalInType-#⇛ (#DECIDE⇛INR⇛! w T x a #[0]VOID comp) j


equalInType-#⇛-rev : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                      → U #⇛! T at w
                      → equalInType i w T a b
                      → equalInType i w U a b
equalInType-#⇛-rev {i} {w} {T} {U} {a} {b} comp e =
  TSext-equalTypes-equalInType
    i w T U a b
    (equalTypes-#⇛-left-right-rev {i} {w} {T} {T} {U} {T} (#⇛-refl w T) (#⇛!→#⇛ {w} {U} {T} comp) (fst e))
    e


≡→#⇛! : (w : 𝕎·) (a b : CTerm) → a ≡ b → a #⇛! b at w
≡→#⇛! w a b e rewrite e = #⇛!-refl {w} {b}


sub0-indBarC⇛INR⇛! : (w : 𝕎·) (T x a : CTerm)
                           → x #⇛! #INR a at w
                           → sub0 x (#IndBarC T) #⇛! #NOWRITEMOD T at w
sub0-indBarC⇛INR⇛! w T x a comp =
  #⇛!-trans
    {w} {sub0 x (#IndBarC T)} {#DECIDE x #[0]VOID (#[0]shiftUp0 (#NOWRITEMOD T))} {#NOWRITEMOD T}
    (≡→#⇛! w (sub0 x (#IndBarC T)) (#DECIDE x #[0]VOID (#[0]shiftUp0 (#NOWRITEMOD T))) (CTerm≡ e))
    (#DECIDE⇛INR⇛! w T x a #[0]VOID comp)
  where
    e : ⌜ sub0 x (#IndBarC T) ⌝ ≡ ⌜ #DECIDE x #[0]VOID (#[0]shiftUp0 (#NOWRITEMOD T)) ⌝
    e rewrite #shiftUp 0 x | #shiftUp 0 x | #shiftDown 0 x | #shiftUp 0 T | #shiftUp 0 T
            | #subv 1 ⌜ x ⌝ ⌜ T ⌝ (CTerm.closed T) | #shiftDown 1 T = refl


#⇛→NATeq : {w : 𝕎·} {a1 a2 b1 b2 : CTerm}
             → b1 #⇛ a1 at w
             → b2 #⇛ a2 at w
             → NATeq w a1 a2
             → NATeq w b1 b2
#⇛→NATeq {w} {a1} {a2} {b1} {b2} c1 c2 (j , d1 , d2) =
  j , ⇛-trans c1 d1 , ⇛-trans c2 d2


#⇓SUP→weq-refl : {eqa : per} {eqb : (a b : CTerm) → eqa a b → per} {w : 𝕎·} {I a1 a2 f1 f2 : CTerm} {j : ℕ}
                  → I #⇓ #SUP a1 f1 at w
                  → I #⇓ #SUP a2 f2 at w
                  → weq₀ eqa eqb w (#APPLY f1 (#NUM j)) (#APPLY f2 (#NUM j))
                  → weq₀ eqa eqb w (#APPLY f1 (#NUM j)) (#APPLY f1 (#NUM j))
#⇓SUP→weq-refl {eqa} {eqb} {w} {I} {a1} {a2} {f1} {f2} {j} c1 c2 h
  rewrite #SUPinj1 {a2} {f2} {a1} {f1} (#⇓-val-det {_} {I} tt tt c2 c1)
        | #SUPinj2 {a2} {f2} {a1} {f1} (#⇓-val-det {_} {I} tt tt c2 c1) = h


#⇛!-NUM-type-NOWRITEMOD : (P : ℕ → Set) (T : CTerm) (i : ℕ) (w : 𝕎·) (n : ℕ)
                        → #⇛!-NUM-type P T
                        → P n
                        → ∈Type i w (#NOWRITEMOD T) (#NUM n)
#⇛!-NUM-type-NOWRITEMOD P T i w n nty pn =
  →equalInTypeNOWRITEMOD (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → NOWRITEMODeq (equalInType i w' T) w' (#NUM n) (#NUM n))
    aw w1 e1 = nty {i} {w1} {n} pn , #⇓→#⇓!-NUM w1 n , #⇓→#⇓!-NUM w1 n


weq→follow-NATeq : (kb : K□) (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T I1 I2 f g : CTerm) (k : ℕ)
                     → type-#⇛!-NUM P T
                     → #⇛!-NUM-type P T
                     → weq₀ (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a (#IndBarC T))) w I1 I2
                     → ((k : ℕ) → equalInType i w (#NOWRITEMOD T) (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
                     → NATeq {--#⇓sameℕ--} w (#follow f I1 k) (#follow g I2 k)
weq→follow-NATeq kb i w P T I1 I2 f g k tyn nty (weqC₀ a1 f1 a2 f2 e c1 c2 ind) eqf
  with kb (equalInType-IndBarB→ i w a1 a2 e) w (⊑-refl· w)
... | inj₁ (t , u , n , d1 , d2 , x1 , x2) = n , comp1 , comp2
      where
        comp1 : #follow f I1 k #⇛ #NUM n at w
        comp1 = #follow-INL⇛ w I1 a1 f1 f t k n c1 d1 x1

        comp2 : #follow g I2 k #⇛ #NUM n at w
        comp2 = #follow-INL⇛ w I2 a2 f2 g u k n c2 d2 x2
... | inj₂ (t , u , d1 , d2) =
    #⇛→NATeq
      {w}
      {#follow f (#APPLY f1 (#NUM j)) (suc k)}
      {#follow g (#APPLY f2 (#NUM j)) (suc k)}
      {#follow f I1 k}
      {#follow g I2 k}
      comp1 comp2
      ind'
      where
        eqf0 : equalInType i w (#NOWRITEMOD T) (#APPLY f (#NUM k)) (#APPLY g (#NUM k))
        eqf0 = eqf k

        eqf1 : equalInType i w (sub0 a1 (#IndBarC T)) (#APPLY f (#NUM k)) (#APPLY g (#NUM k))
        eqf1 = equalInType-#⇛-rev (sub0-indBarC⇛INR⇛! w T a1 t d1) eqf0

        eqf2 : □· w (λ w' _ → Σ ℕ (λ n → #APPLY f (#NUM k) #⇛! #NUM n at w' × #APPLY g (#NUM k) #⇛! #NUM n at w' × P n))
        eqf2 = INR→!≡∈Type-IndBarC i w P T a1 t _ _ tyn d1 eqf1

        eqf3 : Σ ℕ (λ n → #APPLY f (#NUM k) #⇛! #NUM n at w × #APPLY g (#NUM k) #⇛! #NUM n at w × P n)
        eqf3 = kb eqf2 w (⊑-refl· w)

        j : ℕ
        j = fst eqf3

        cf : #APPLY f (#NUM k) #⇛! #NUM j at w
        cf = fst (snd eqf3)

        cg : #APPLY g (#NUM k) #⇛! #NUM j at w
        cg = fst (snd (snd eqf3))

        pj : P j
        pj = snd (snd (snd eqf3))

        eqj : equalInType i w (sub0 a1 (#IndBarC T)) (#NUM j) (#NUM j)
        eqj = equalInType-#⇛-rev (sub0-indBarC⇛INR⇛! w T a1 t d1) (#⇛!-NUM-type-NOWRITEMOD P T i w j nty pj)

        ind' : NATeq {--#⇓sameℕ--} w (#follow f (#APPLY f1 (#NUM j)) (suc k)) (#follow g (#APPLY f2 (#NUM j)) (suc k))
        ind' = weq→follow-NATeq kb i w P T (#APPLY f1 (#NUM j)) (#APPLY f2 (#NUM j)) f g (suc k) tyn nty (ind (#NUM j) (#NUM j) eqj) eqf

        comp1 : #follow f I1 k #⇛ #follow f (#APPLY f1 (#NUM j)) (suc k) at w
        comp1 = #follow-INR⇛ w I1 a1 f1 f t k j c1 d1 cf

        comp2 : #follow g I2 k #⇛ #follow g (#APPLY f2 (#NUM j)) (suc k) at w
        comp2 = #follow-INR⇛ w I2 a2 f2 g u k j c2 d2 cg


NATeq-trans : {w : 𝕎·} {a b c : CTerm}
              → NATeq w a b
              → NATeq w b c
              → NATeq w a c
NATeq-trans {w} {a} {b} {c} (k , c1 , c2) (j , d1 , d2)
  rewrite #NUMinj (#⇛-val-det {_} {b} tt tt d1 c2) = k , c1 , d2


BAIRE!2𝕊-equalInBAIRE : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE! f)
                        → equalInType i w #BAIRE f (#MSEQ (BAIRE!2𝕊 kb f∈))
BAIRE!2𝕊-equalInBAIRE kb {i} {w} {f} f∈ =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    s : 𝕊
    s = BAIRE!2𝕊 kb f∈

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY f a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ ea =
      →equalInType-NAT i w1 _  _ (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 _ _ ea))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂ → NATeq w' (#APPLY f a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (k , c1 , c2) = s k , #⇛!→#⇛ {w2} {#APPLY f a₁} {#NUM (s k)} j3 , APPLY-MSEQ⇛ w2 s ⌜ a₂ ⌝ k c2
          where
            j1 : #APPLY f (#NUM k) #⇛! #NUM (s k) at w
            j1 = fst (snd (kb (equalInType-NAT!→ i w _ _ (APPLY-∈BAIRE!-NUM→ i w f k f∈)) w (⊑-refl· w)))

            j2 : #⇛!sameℕ w2 (#APPLY f a₁) (#APPLY f (#NUM k))
            j2 = kb (equalInType-NAT!→ i w2 _ _ (equalInType-FUN→ (≡CTerm→equalInType #BAIRE!≡ f∈) w2 (⊑-trans· e1 e2) a₁ (#NUM k) (#⇛NUM→equalInType-NAT i w2 a₁ k c1))) w2 (⊑-refl· w2)

            j3 : #APPLY f a₁ #⇛! #NUM (s k) at w2
            j3 = #⇛!sameℕ→#⇛!NUMₗ {w2} {#APPLY f a₁} {#APPLY f (#NUM k)} j2 (∀𝕎-mon (⊑-trans· e1 e2) j1)



#⇛!sameℕ→NATeq : {w : 𝕎·} {a b : CTerm}
                    → #⇛!sameℕ w a b
                    → NATeq w a b
#⇛!sameℕ→NATeq {w} {a} {b} (k , c1 , c2) = k , #⇛!→#⇛ {w} {a} {#NUM k} c1 , #⇛!→#⇛ {w} {b} {#NUM k} c2


≤suc : (n : ℕ) → n ≤ suc n
≤suc 0 = _≤_.z≤n
≤suc (suc n) = _≤_.s≤s (≤suc n)


#APPLY-seq2list⇛¬< : (w : 𝕎·) (s : 𝕊) (a : CTerm) (k n : ℕ)
                      → ¬ k < n
                      → a #⇛ #NUM k at w
                      → #APPLY (seq2list s n) a #⇛ #N0 at w
#APPLY-seq2list⇛¬< w s a k 0 ltn comp = λ w1 e1 → lift (1 , refl)
#APPLY-seq2list⇛¬< w s a k (suc n) ltn comp =
  #⇛-trans
    {w} {#APPLY (seq2list s (suc n)) a} {#IFEQ a (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)} {#N0}
    (APPLY-APPENDf⇛ w (#NUM n) (seq2list s n) (#NUM (s n)) a)
    (#⇛-trans
       {w}
       {#IFEQ a (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)}
       {#IFEQ (#NUM k) (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)}
       {#N0}
       (IFEQ⇛₁ {w} {⌜ a ⌝} {NUM k} {NUM n} {NUM (s n)} {⌜ #APPLY (seq2list s n) a ⌝} comp)
       c1)
  where
    c1 : #IFEQ (#NUM k) (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a) #⇛ #N0 at w
    c1 with k ≟ n
    ... | yes p rewrite p = ⊥-elim (ltn ≤-refl)
    ... | no p =
      #⇛-trans
        {w}
        {#IFEQ (#NUM k) (#NUM n) (#NUM (s n)) (#APPLY (seq2list s n) a)}
        {#APPLY (seq2list s n) a}
        {#N0}
        (IFEQ⇛¬= {n} {k} {w} {NUM (s n)} {⌜ #APPLY (seq2list s n) a ⌝} p)
        (#APPLY-seq2list⇛¬< w s a k n (λ z → ltn (≤-trans z (≤suc n))) comp)


∈Type-BAIRE-seq2list : (i : ℕ) (w : 𝕎·) (s : 𝕊) (n : ℕ)
                        → ∈Type i w #BAIRE (seq2list s n)
∈Type-BAIRE-seq2list i w s n =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' #NAT (#APPLY (seq2list s n) a₁) (#APPLY (seq2list s n) a₂))
    aw w1 e1 a₁ a₂ ea =
      →equalInType-NAT
        i w1 (#APPLY (seq2list s n) a₁) (#APPLY (seq2list s n) a₂)
        (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 a₁ a₂ ea))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂ → NATeq w' (#APPLY (seq2list s n) a₁) (#APPLY (seq2list s n) a₂))
        aw1 w2 e2 (k , c1 , c2) with k <? n
        ... | yes p = s k , #APPLY-seq2list⇛ w2 s a₁ k n p c1 , #APPLY-seq2list⇛ w2 s a₂ k n p c2
        ... | no p = 0 , #APPLY-seq2list⇛¬< w2 s a₁ k n p c1 , #APPLY-seq2list⇛¬< w2 s a₂ k n p c2


∈Type-NAT→T-seq2list : (i : ℕ) (w : 𝕎·) (s : 𝕊) (n : ℕ) (P : ℕ → Set) (T : CTerm)
                        → P 0
                        → ((n : ℕ) → P (s n))
                        → #⇛!-NUM-type P T
                        → type-preserves-#⇛ T
                        → isType i w T
                        → ∈Type i w (#FUN #NAT T) (seq2list s n)
∈Type-NAT→T-seq2list i w s n P T p0 ps nty prest tyt =
  equalInType-FUN eqTypesNAT tyt aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' T (#APPLY (seq2list s n) a₁) (#APPLY (seq2list s n) a₂))
    aw w1 e1 a₁ a₂ ea =
      equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 a₁ a₂ ea))
        where
          aw1 : ∀𝕎 w1 (λ w' _ → NATeq w' a₁ a₂ → equalInType i w' T (#APPLY (seq2list s n) a₁) (#APPLY (seq2list s n) a₂))
          aw1 w1 e1 (k , c₁ , c₂) with k <? n
          ... | yes p = prest i w1 (#APPLY (seq2list s n) a₁) (#NUM (s k)) (#APPLY (seq2list s n) a₂) (#NUM (s k)) (#APPLY-seq2list⇛ w1 s a₁ k n p c₁) (#APPLY-seq2list⇛ w1 s a₂ k n p c₂) (nty {i} {w1} {s k} (ps k))
          ... | no p = prest i w1 (#APPLY (seq2list s n) a₁) #N0 (#APPLY (seq2list s n) a₂) #N0 (#APPLY-seq2list⇛¬< w1 s a₁ k n p c₁) (#APPLY-seq2list⇛¬< w1 s a₂ k n p c₂) (nty {i} {w1} {0} p0)


→APPLY-upd-seq2list#⇛NUM : (kb : K□) (cn : cℕ) (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F : CTerm) (r : Name) (s : 𝕊) (k : ℕ)
                             → P 0
                             → ((n : ℕ) → P (s n))
                             → #⇛!-NUM-type P T
                             → compatible· r w Res⊤
                             → type-preserves-#⇛ T
                             → isType i w T
                             → ∈Type i w (#FunBar T) F
                             → Σ ℕ (λ n → #APPLY F (#upd r (seq2list s k)) #⇛ #NUM n at w)
→APPLY-upd-seq2list#⇛NUM kb cn i w P T F r s k p0 ps nty compat prest tyt F∈ =
  fst neq , fst (snd neq)
  where
    ∈B : ∈Type i w (#FUN #NAT T) (#upd r (seq2list s k))
    ∈B = upd∈BAIRE cn i w r T (seq2list s k) compat prest tyt (∈Type-NAT→T-seq2list i w s k P T p0 ps nty prest tyt)

    neq : NATmem w (#APPLY F (#upd r (seq2list s k)))
    neq = kb (equalInType-NAT→ i w _ _ (equalInType-FUN→ F∈ w (⊑-refl· w) (#upd r (seq2list s k)) (#upd r (seq2list s k)) ∈B)) w (⊑-refl· w)


#APPLY-MSEQ-NUM#⇛! : (s : 𝕊) (k : ℕ) (w : 𝕎·)
                      → #APPLY (#MSEQ s) (#NUM k) #⇛! #NUM (s k) at w
#APPLY-MSEQ-NUM#⇛! s k w w1 e1 = lift (2 , refl)


APPLY-loopR-NUM⇛! : (w : 𝕎·) (R f : CTerm) (m n : ℕ)
                    → #APPLY (#loopR R (#NUM n) f) (#NUM m) #⇛! #APPLY2 R (#NUM (suc n)) (#APPENDf (#NUM n) f (#NUM m)) at w
APPLY-loopR-NUM⇛! w R f m n w1 e1 =
  lift (APPLY-loopR-⇓ w1 w1 w1 R (#NUM n) f (#NUM m) m n (0 , refl) (0 , refl))


#⇛SUP→× : (w : 𝕎·) (I t a f b g : CTerm)
            → I #⇛! t at w
            → I #⇛ #SUP a f at w
            → t #⇛ #SUP b g at w
            → a ≡ b × f ≡ g
#⇛SUP→× w I t a f b g c1 c2 c3
  rewrite #SUPinj1 {b} {g} {a} {f} (#⇛-val-det {_} {I} tt tt (#⇛-trans {w} {I} {t} {#SUP b g} (#⇛!→#⇛ {w} {I} {t} c1) c3) c2)
        | #SUPinj2 {b} {g} {a} {f} (#⇛-val-det {_} {I} tt tt (#⇛-trans {w} {I} {t} {#SUP b g} (#⇛!→#⇛ {w} {I} {t} c1) c3) c2)
  = refl , refl


NUM∈sub0-IndBarc : (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T a x : CTerm) (k : ℕ)
                    → P k
                    → #⇛!-NUM-type P T
                    → a #⇛! #INR x at w
                    → ∈Type i w (sub0 a (#IndBarC T)) (#NUM k)
NUM∈sub0-IndBarc i w P T a x k pk nty comp =
  equalInType-#⇛-rev (sub0-indBarC⇛INR⇛! w T a x comp) (#⇛!-NUM-type-NOWRITEMOD P T i w k nty pk)
-- (NUM-equalInType-NAT! i w k)


≡ₗ→#⇛! : (w : 𝕎·) (a b : CTerm)
          → a ≡ b
          → a #⇛! b at w
≡ₗ→#⇛! w a b e rewrite e = #⇛!-refl {w} {b}


≡ₗ→#⇛ : (w : 𝕎·) (a b : CTerm)
         → a ≡ b
         → a #⇛ b at w
≡ₗ→#⇛ w a b e rewrite e = #⇛-refl w b


≡#follow : (a1 a2 b1 b2 : CTerm) (c1 c2 : ℕ)
           → a1 ≡ a2
           → b1 ≡ b2
           → c1 ≡ c2
           → #follow a1 b1 c1 ≡ #follow a2 b2 c2
≡#follow a1 a2 b1 b2 c1 c2 e1 e2 e3 rewrite e1 | e2 | e3 = refl

\end{code}
