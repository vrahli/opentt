\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --experimental-lossy-unification #-}
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


module barContP7 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
--open import terms5(W)(C)(K)(G)(X)(N)
--open import terms6(W)(C)(K)(G)(X)(N)
--open import terms7(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)
open import terms9(W)(C)(K)(G)(X)(N)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E) using (#⇓sameℕ)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)


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


APPLY-∈BAIRE-NUM→ : (i : ℕ) (w : 𝕎·) (f : CTerm) (n : ℕ)
                      → ∈Type i w #BAIRE f
                      → ∈Type i w #NAT (#APPLY f (#NUM n))
APPLY-∈BAIRE-NUM→ i w f n f∈ =
  equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


APPLY-∈BAIRE!-NUM→ : (i : ℕ) (w : 𝕎·) (f : CTerm) (n : ℕ)
                      → ∈Type i w #BAIRE! f
                      → ∈Type i w #NAT! (#APPLY f (#NUM n))
APPLY-∈BAIRE!-NUM→ i w f n f∈ =
  equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


APPLY-≡∈BAIRE-NUM→ : (i : ℕ) (w : 𝕎·) (f g : CTerm) (n : ℕ)
                      → equalInType i w #BAIRE f g
                      → equalInType i w #NAT (#APPLY f (#NUM n)) (#APPLY g (#NUM n))
APPLY-≡∈BAIRE-NUM→ i w f g n f∈ =
  equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


APPLY-≡∈BAIRE!-NUM→ : (i : ℕ) (w : 𝕎·) (f g : CTerm) (n : ℕ)
                      → equalInType i w #BAIRE! f g
                      → equalInType i w #NAT! (#APPLY f (#NUM n)) (#APPLY g (#NUM n))
APPLY-≡∈BAIRE!-NUM→ i w f g n f∈ =
  equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)


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
  equalInType-FUN eqTypesNAT eqTypesNAT aw
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
            j2 = kb (equalInType-NAT→ i w2 _ _ (equalInType-FUN→ f∈ w2 (⊑-trans· e1 e2) a₁ (#NUM k) (#⇛NUM→equalInType-NAT i w2 a₁ k c1))) w2 (⊑-refl· w2)

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


#tab : (r : Name) (F : CTerm) (k : ℕ) (f : CTerm) → CTerm
#tab r F k f = #APPLY2 (#loop r F) (#NUM k) f


wmem : (eqa : per) (eqb : (a b : CTerm) → eqa a b → per) (w : 𝕎·) (t : CTerm) → Set(lsuc(L))
wmem eqa eqb w t = weq eqa eqb w t t


BAIRE2list : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE f) (k : ℕ) → CTerm
BAIRE2list kb {i} {w} {f} f∈ k = seq2list (BAIRE2𝕊 kb f∈) k


∈Type-IndBarB→ : (i : ℕ) (w : 𝕎·) (b : CTerm)
                   → ∈Type i w #IndBarB b
                   → □· w (λ w' _ → Σ CTerm (λ t → Σ ℕ (λ n → b #⇛! #INL t at w' × t #⇛ #NUM n at w'))
                                      ⊎ Σ CTerm (λ t → b #⇛! #INR t at w'))
∈Type-IndBarB→ i w b b∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-UNION!→ b∈))
  where
    aw : ∀𝕎 w (λ w' e' → UNION!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' b b
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
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInType-UNION!→ b∈))
  where
    aw : ∀𝕎 w (λ w' e' → UNION!eq (equalInType i w' #NAT) (equalInType i w' #UNIT) w' a b
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


≡ₗ→⇓from-to : {w w' : 𝕎·} {a b c : Term} → b ≡ a → a ⇓ c from w to w' → b ⇓ c from w to w'
≡ₗ→⇓from-to {w} {w'} {a} {b} {c} e comp rewrite e = comp


sub3-followB≡ : (a g f : CTerm)
                → sub (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) (sub ⌜ g ⌝ (sub ⌜ a ⌝ (followB ⌜ f ⌝)))
                   ≡ followBT ⌜ a ⌝ (WRECr (followB ⌜ f ⌝) ⌜ g ⌝) ⌜ f ⌝
sub3-followB≡ a g f
   rewrite #shiftUp 0 a
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
      (≡ₗ→⇓from-to
        (≡APPLY (sub3-followB≡ a g f) refl)
        (⇓-trans₂
          (APPLY-LAMBDA⇓  w' (followD (VAR 0) (shiftUp 0 ⌜ a ⌝) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)) (NUM k))
          (≡ₗ→⇓from-to
            (sub-followD≡ k a g f)
            (⇓-trans₂
               (DECIDE⇓ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
                        (lower (ca w' (⇓from-to→⊑ {w} {w'} {⌜ I ⌝} {⌜ #SUP a g ⌝} cI))))
               (⇓-trans₂
                  (DECIDE-INL⇓ w' ⌜ t ⌝ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)))
                  (≡ₗ→⇓from-to (sub-VAR0 ⌜ t ⌝) (snd cn'))))))))
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
      (≡ₗ→⇓from-to
        (≡APPLY (sub3-followB≡ a g f) refl)
        (⇓-trans₂
          (APPLY-LAMBDA⇓ w' (followD (VAR 0) (shiftUp 0 ⌜ a ⌝) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)) (NUM k))
          (≡ₗ→⇓from-to
            (sub-followD≡ k a g f)
            (⇓-trans₂
               (DECIDE⇓ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝))
                        (lower (ca w' e')))
               (⇓-trans₂
                  (DECIDE-INR⇓ w' ⌜ t ⌝ (VAR 0) (followDA (NUM k) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)))
                  (≡ₗ→⇓from-to
                    (sub-followDA≡ t f g k)
                    (⇓-trans₂
                      (LET⇓ (followDA2 (shiftUp 0 (NUM k)) (VAR 0) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)) (SUC-NUM⇓ w' k))
                      (⇓-trans₂
                        (LET-val⇓ w' (NUM (suc k)) (followDA2 (shiftUp 0 (NUM k)) (VAR 0) (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (shiftUp 0 ⌜ f ⌝)) tt)
                        (≡ₗ→⇓from-to
                          (sub-followDA2≡ (suc k) k f g)
                          (⇓-trans₂
                            (LET⇓ (APPLY2 (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (VAR 0) (NUM (suc k))) (lower (cj w' (⊑-refl· w'))))
                            (⇓-trans₂
                               (LET-val⇓ w' (NUM j) (APPLY2 (shiftUp 0 (WRECr (followB ⌜ f ⌝) ⌜ g ⌝)) (VAR 0) (NUM (suc k))) tt)
                               (≡ₗ→⇓from-to
                                 (sub-APPLY2-WRECr-followB j k f g)
                                 (⇓-trans₂
                                   (APPLY⇓ (NUM (suc k)) (APPLY-LAMBDA⇓ w' (WREC (APPLY (shiftUp 0 ⌜ g ⌝) (VAR 0)) (shiftUp 3 (followB ⌜ f ⌝))) (NUM j)))
                                   (≡ₗ→⇓from-to
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


INR→!≡∈Type-IndBarC : (i : ℕ) (w : 𝕎·) (x a b c : CTerm)
                     → x #⇛! #INR a at w
                     → equalInType i w (sub0 x #IndBarC) b c
                     → □· w (λ w' _ → #⇛!sameℕ w' b c)
INR→!≡∈Type-IndBarC i w x a b c comp j rewrite sub0-IndBarC≡ x =
  equalInType-NAT!→ i w b c j1
  where
    j1 : equalInType i w #NAT! b c
    j1 = equalInType-#⇛ (#DECIDE⇛INR-NAT⇛! w x a #[0]VOID comp) j


equalInType-#⇛-rev : {i : ℕ} {w : 𝕎·} {T U a b : CTerm}
                      → U #⇛! T at w
                      → equalInType i w T a b
                      → equalInType i w U a b
equalInType-#⇛-rev {i} {w} {T} {U} {a} {b} comp e =
  TSext-equalTypes-equalInType
    i w T U a b
    (equalTypes-#⇛-left-right-rev {i} {w} {T} {T} {U} {T} (#⇛-refl w T) (#⇛!→#⇛ {w} {U} {T} comp) (fst e))
    e


sub0-indBarC⇛INR-NAT⇛! : (w : 𝕎·) (x a : CTerm)
                           → x #⇛! #INR a at w
                           → sub0 x #IndBarC #⇛! #NAT! at w
sub0-indBarC⇛INR-NAT⇛! w x a comp rewrite #shiftUp 0 x | #shiftDown 0 x =
  #DECIDE⇛INR-NAT⇛! w x a #[0]VOID comp


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
                  → weq eqa eqb w (#APPLY f1 (#NUM j)) (#APPLY f2 (#NUM j))
                  → weq eqa eqb w (#APPLY f1 (#NUM j)) (#APPLY f1 (#NUM j))
#⇓SUP→weq-refl {eqa} {eqb} {w} {I} {a1} {a2} {f1} {f2} {j} c1 c2 h
  rewrite #SUPinj1 {a2} {f2} {a1} {f1} (#⇓-val-det {_} {I} tt tt c2 c1)
        | #SUPinj2 {a2} {f2} {a1} {f1} (#⇓-val-det {_} {I} tt tt c2 c1) = h


weq→follow-NATeq : (kb : K□) (i : ℕ) (w : 𝕎·) (I1 I2 f g : CTerm) (k : ℕ)
                     → weq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w I1 I2
                     → ((k : ℕ) → equalInType i w #NAT! (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
                     → NATeq {--#⇓sameℕ--} w (#follow f I1 k) (#follow g I2 k)
weq→follow-NATeq kb i w I1 I2 f g k (weqC a1 f1 a2 f2 e c1 c2 ind) eqf
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
        eqf0 : equalInType i w #NAT! (#APPLY f (#NUM k)) (#APPLY g (#NUM k))
        eqf0 = eqf k --APPLY-≡∈BAIRE!-NUM→ i w f g k eqf

        eqf1 : equalInType i w (sub0 a1 #IndBarC) (#APPLY f (#NUM k)) (#APPLY g (#NUM k))
        eqf1 = equalInType-#⇛-rev (sub0-indBarC⇛INR-NAT⇛! w a1 t d1) eqf0

        eqf2 : □· w (λ w' _ → #⇛!sameℕ w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        eqf2 = INR→!≡∈Type-IndBarC i w a1 t _ _ d1 eqf1

        eqf3 : #⇛!sameℕ w (#APPLY f (#NUM k)) (#APPLY g (#NUM k))
        eqf3 = kb eqf2 w (⊑-refl· w)

        j : ℕ
        j = fst eqf3

        cf : #APPLY f (#NUM k) #⇛! #NUM j at w
        cf = fst (snd eqf3)

        cg : #APPLY g (#NUM k) #⇛! #NUM j at w
        cg = snd (snd eqf3)

        eqj : equalInType i w (sub0 a1 #IndBarC) (#NUM j) (#NUM j)
        eqj = equalInType-#⇛-rev (sub0-indBarC⇛INR-NAT⇛! w a1 t d1) (NUM-equalInType-NAT! i w j)

        ind' : NATeq {--#⇓sameℕ--} w (#follow f (#APPLY f1 (#NUM j)) (suc k)) (#follow g (#APPLY f2 (#NUM j)) (suc k))
        ind' = weq→follow-NATeq kb i w (#APPLY f1 (#NUM j)) (#APPLY f2 (#NUM j)) f g (suc k) (ind (#NUM j) (#NUM j) eqj) eqf

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
  equalInType-FUN eqTypesNAT eqTypesNAT aw
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
            j2 = kb (equalInType-NAT!→ i w2 _ _ (equalInType-FUN→ f∈ w2 (⊑-trans· e1 e2) a₁ (#NUM k) (#⇛NUM→equalInType-NAT i w2 a₁ k c1))) w2 (⊑-refl· w2)

            j3 : #APPLY f a₁ #⇛! #NUM (s k) at w2
            j3 = #⇛!sameℕ→#⇛!NUMₗ {w2} {#APPLY f a₁} {#APPLY f (#NUM k)} j2 (∀𝕎-mon (⊑-trans· e1 e2) j1)



#⇛!sameℕ→NATeq : {w : 𝕎·} {a b : CTerm}
                    → #⇛!sameℕ w a b
                    → NATeq w a b
#⇛!sameℕ→NATeq {w} {a} {b} (k , c1 , c2) = k , #⇛!→#⇛ {w} {a} {#NUM k} c1 , #⇛!→#⇛ {w} {b} {#NUM k} c2


follow-NUM : (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm) (s : 𝕊) (k n : ℕ)
             → wmem (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w (#tab r F k (seq2list s k))
             → #APPLY F (#MSEQ s) #⇛ #NUM n at w
             → #follow (#MSEQ s) (#tab r F k (seq2list s k)) k #⇛ #NUM n at w
follow-NUM i w r F s k n wm h comp = ?


semCond : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
          (i : ℕ) (w : 𝕎·) (r : Name) (F f : CTerm)
          → compatible· r w Res⊤
          → ∈Type i w #FunBarP F
          → ∈Type i w #BAIRE! f
          → equalInType i w #NAT (#APPLY F f) (#follow f (#tab r F 0 #INIT) 0)
-- It's a #QNAT and not a #NAT because of the computation on #tab, which is a "time-dependent" computation
semCond kb cn can exb gc i w r F f compat F∈P f∈ =
  →equalInType-NAT
    i w (#APPLY F f) (#follow f I 0)
    (Mod.∀𝕎-□Func M aw (equalInType-W→ i w #IndBarB #IndBarC I I I∈))
  where
    nnF  : #¬Names F
    nnF = equalInType-TPURE→ₗ F∈P

    F∈ : ∈Type i w #FunBar F
    F∈ = equalInType-TPURE→ F∈P

    s : 𝕊
    s = BAIRE!2𝕊 kb f∈

    I : CTerm
    I = #tab r F 0 #INIT

    I∈ : ∈Type i w #IndBar I
    I∈ = sem kb cn can exb gc i w r F compat F∈P

    f≡1 : (k : ℕ) → equalInType i w #NAT! (#APPLY f (#NUM k)) (#APPLY (#MSEQ s) (#NUM k))
    f≡1 k = BAIRE!2𝕊-equalInNAT! kb {i} {w} {f} f∈ k

    f≡2 : equalInType i w #BAIRE f (#MSEQ (BAIRE!2𝕊 kb f∈))
    f≡2 = BAIRE!2𝕊-equalInBAIRE kb {i} {w} {f} f∈

    aw : ∀𝕎 w (λ w' e' → wmem (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a #IndBarC)) w' I
                        → NATeq {--#weakMonEq--} w' (#APPLY F f) (#follow f I 0))
    aw w1 e1 h =
      NATeq-trans {w1} {#APPLY F f} {#follow (#MSEQ s) I 0} {#follow f I 0}
        (NATeq-trans {w1} {#APPLY F f} {#APPLY F (#MSEQ s)} {#follow (#MSEQ s) I 0} neq1 neq2)
        (weq→follow-NATeq kb i w1 I I (#MSEQ s) f 0 h (λ k → equalInType-mon (equalInType-sym (f≡1 k)) w1 e1))
      where
        neq1 : NATeq w1 (#APPLY F f) (#APPLY F (#MSEQ s))
        neq1 = kb (equalInType-NAT→ i w1 _ _ (equalInType-FUN→ F∈ w1 e1 f (#MSEQ s) (equalInType-mon f≡2 w1 e1))) w1 (⊑-refl· w1)

        neq2 : NATeq w1 (#APPLY F (#MSEQ s)) (#follow (#MSEQ s) I 0)
        neq2 = fst neq1 , snd (snd neq1) , {!!}

\end{code}
