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

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
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


BAIRE2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} {f : CTerm} (f∈ : ∈Type i w #BAIRE f) → 𝕊
BAIRE2𝕊 kb {i} {w} {f} f∈ n = fst j
  where
    j : NATmem w (#APPLY f (#NUM n))
    j = kb (equalInType-NAT→ i w _ _ (APPLY-∈BAIRE-NUM→ i w f n f∈)) w (⊑-refl· w)


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


followDA : (k r s : Term) → Term
followDA k r s =
  LET (SUC k)
      (APPLY2 (shiftUp 0 r) -- r
              (APPLY (shiftUp 0 s) (shiftUp 0 k))
              (VAR 0)) -- k


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
                                                   (#[5]APPLY2 #[5]VAR5 -- r
                                                               (#[5]APPLY (#[5]shiftUp0 (#[4]shiftUp0 (#[3]shiftUp0 (#[2]shiftUp0 (#[1]shiftUp0 (#[0]shiftUp0 s))))))
                                                                          #[5]VAR2) --k
                                                               (#[5]VAR0)))))) -- k
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
         | #shiftDown 1 a
         | #shiftDown 4 g
         | #shiftDown 10 f
         | #subv 1 ⌜ g ⌝ ⌜ a ⌝ (CTerm.closed a)
         | #subv 3 ⌜ a ⌝ ⌜ f ⌝ (CTerm.closed f)
         | #shiftDown 1 a
         | #shiftDown 3 f
         | #subv 3 ⌜ g ⌝ ⌜ f ⌝ (CTerm.closed f)
         | #shiftDown 3 f
         | #subv 1 (LAMBDA (WREC (APPLY ⌜ g ⌝ (VAR 0)) (LAMBDA (DECIDE (VAR 2) (VAR 0) (LET (SUC (VAR 1)) (APPLY2 (VAR 6) (APPLY ⌜ f ⌝ (VAR 2)) (VAR 0))))))) ⌜ a ⌝ (CTerm.closed a)
         | #subv 3 (LAMBDA (WREC (APPLY ⌜ g ⌝ (VAR 0)) (LAMBDA (DECIDE (VAR 2) (VAR 0) (LET (SUC (VAR 1)) (APPLY2 (VAR 6) (APPLY ⌜ f ⌝ (VAR 2)) (VAR 0))))))) ⌜ f ⌝ (CTerm.closed f)
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
        | #shiftUp 7 f
        | #shiftUp 7 f
        | #shiftUp 7 f
        | #shiftUp 0 g
        | #shiftUp 1 g
        | #shiftUp 1 g
        | #shiftUp 1 g
        | #subv 0 ⌜ #NUM k ⌝ ⌜ a ⌝ (CTerm.closed a)
        | #subv 3 ⌜ #NUM k ⌝ ⌜ g ⌝ (CTerm.closed g)
        | #subv 2 ⌜ #NUM k ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #subv 9 ⌜ #NUM k ⌝ ⌜ f ⌝ (CTerm.closed f)
        | #shiftDown 0 a
        | #shiftDown 3 g
        | #shiftDown 9 f
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



-- INR case - this case depends on f
#follow-INR⇓ : (w : 𝕎·) (I a g f t : CTerm) (k : ℕ)
               → I #⇓ #SUP a g at w
               → a #⇛! #INR t at w
               → #follow f I k #⇓ #follow f (#APPLY g (#APPLY f (#NUM k))) (suc k) at w
#follow-INR⇓ w I a g f t k cI ca = {!!}
-- TODO:
-- (1) we don't get (suc k) but (#SUC (#NUM k)) so we need a cbv -- DONE
-- (2) add a cbv on the (#APPLY g (#APPLY f (#NUM k)))? -- No need


wmem→follow-NATeq : (kb : K□) (i : ℕ) (w : 𝕎·) (I J f g : CTerm) (k : ℕ)
                     → weq (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a #IndBarC)) w I J
                     → equalInType i w #BAIRE f g
                     → #⇓sameℕ w (#follow f I k) (#follow g J k)
wmem→follow-NATeq kb i w I J f g k (weqC a1 f1 a2 f2 e c1 c2 ind) eqf =
  d (kb (equalInType-IndBarB→ i w a1 a2 e) w (⊑-refl· w))
  where
    d : Σ CTerm (λ t → Σ CTerm (λ u → Σ ℕ (λ n → a1 #⇛! #INL t at w × a2 #⇛! #INL u at w × t #⇛ #NUM n at w × u #⇛ #NUM n at w)))
        ⊎ Σ CTerm (λ t → Σ CTerm (λ u → a1 #⇛! #INR t at w × a2 #⇛! #INR u at w))
        → #⇓sameℕ w (#follow f I k) (#follow g J k)
    d (inj₁ (t , u , n , d1 , d2 , x1 , x2)) = n , comp1 , comp2
      where
        comp1 : #follow f I k #⇓ #NUM n at w
        comp1 = #follow-INL⇓ w I a1 f1 f t k n c1 d1 x1

        comp2 : #follow g J k #⇓ #NUM n at w
        comp2 = #follow-INL⇓ w J a2 f2 g u k n c2 d2 x2
    d (inj₂ (t , u , d1 , d2)) = {!!}



{--
xxx : (k : ℕ)
      → wmem (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a #IndBarC)) w' (#tab r F k (BAIRE2list f k))
      → NATeq w' (#APPLY F f) (#follow f I k)
--}


semCond : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
          (i : ℕ) (w : 𝕎·) (r : Name) (F f : CTerm)
          → compatible· r w Res⊤
          → ∈Type i w #FunBarP F
          → ∈Type i w #BAIRE f
          → equalInType i w #QNAT (#APPLY F f) (#follow f (#tab r F 0 #INIT) 0)
-- It's a #QNAT and not a #NAT because of the computation on #tab, which is a "time-dependent" computation
semCond kb cn can exb gc i w r F f compat F∈ f∈ =
  →equalInType-QNAT
    i w (#APPLY F f) (#follow f I 0)
    (Mod.∀𝕎-□Func M aw (equalInType-W→ i w #IndBarB #IndBarC I I I∈))
  where
    s : 𝕊
    s = BAIRE2𝕊 kb f∈

    I : CTerm
    I = #tab r F 0 #INIT

    I∈ : ∈Type i w #IndBar I
    I∈ = sem kb cn can exb gc i w r F compat F∈

    aw : ∀𝕎 w (λ w' e' → wmem (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a #IndBarC)) w' I
                        → #weakMonEq w' (#APPLY F f) (#follow f I 0))
    aw w1 e1 h w2 e2 = lift {!!}
    -- use BAIRE2𝕊-equalInBAIRE to switch from (#APPLY F f) to (#APPLY F (#MSEQ s))
    -- Can we do the same with (#follow f I 0)?


\end{code}
