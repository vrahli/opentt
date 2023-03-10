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
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Induction.WellFounded
open import Axiom.Extensionality.Propositional


open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import progress
open import choiceExt
open import choiceVal
open import getChoice
open import newChoice
open import freeze
open import progress
open import choiceBar
open import mod


module mp_prop {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
               (C : Choice) (K : Compatible W C) (P : Progress {L} W C K)
               (G : GetChoice {L} W C K) (X : ChoiceExt {L} W C)
               (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
               (F : Freeze {L} W C K P G N)
               (E : Extensionality 0ℓ (lsuc(lsuc(L))))
               (CB : ChoiceBar W M C K P G X N V F E)
       where


open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)
open import computation(W)(C)(K)(G)(X)(N)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import lem_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(E)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import not_lem(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import typeC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import boolC(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import mp_props(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)




NAT!→U : ℕ → Term
NAT!→U i = FUN NAT! (UNIV i)


#NAT!→U : ℕ → CTerm
#NAT!→U i = ct (NAT!→U i) refl


DECℕ : Term → Term
DECℕ F = PI NAT! (SQUASH (UNION (APPLY (shiftUp 0 F) (VAR 0)) (NEG (APPLY (shiftUp 0 F) (VAR 0)))))


-- π (F : ℕ → 𝕌ᵢ). (Π (n : ℕ). F n ∨ ¬ F n) → ¬(Π (n : ℕ). ¬(F n)) → ||Σ (n : ℕ). F n||
MPℙ : ℕ → Term
MPℙ i = PI (NAT!→U i) (FUN (DECℕ (VAR 0))
                            (FUN (NEG (NEG (SQUASH (SUM NAT! (APPLY (VAR 1) (VAR 0))))))
                                 (SQUASH (SUM NAT! (APPLY (VAR 1) (VAR 0))))))


#[0]MPℙ-right : CTerm0
#[0]MPℙ-right = #[0]SQUASH (#[0]SUM #[0]NAT! (#[1]APPLY #[1]VAR1 #[1]VAR0))


#[0]MPℙ-left : CTerm0
#[0]MPℙ-left = #[0]NEG (#[0]NEG #[0]MPℙ-right)


fvars-CTerm1 : (a : CTerm1) → fvars ⌜ a ⌝ ⊆ 0 ∷ [ 1 ]
fvars-CTerm1 a = ⊆?→⊆ (CTerm1.closed a)


#[1]SQUASH : CTerm1 → CTerm1
#[1]SQUASH a = ct1 (SQUASH ⌜ a ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SQUASH ⌜ a ⌝
    c rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ = ⊆→⊆? {lowerVars (Data.List.map suc (fvars ⌜ a ⌝))} {0 ∷ [ 1 ]} s
      where
        s : lowerVars (Data.List.map suc (fvars ⌜ a ⌝)) ⊆ 0 ∷ [ 1 ]
        s {z} i = w
          where
            x : suc z ∈ Data.List.map suc (fvars ⌜ a ⌝)
            x = ∈lowerVars→ z (Data.List.map suc (fvars ⌜ a ⌝)) i

            y : Var
            y = fst (∈-map⁻ suc x)

            j : y ∈ fvars ⌜ a ⌝
            j = fst (snd (∈-map⁻ suc x))

            e : z ≡ y
            e = suc-injective (snd (snd (∈-map⁻ suc x)))

            w : z ∈ 0 ∷ [ 1 ]
            w rewrite e = fvars-CTerm1 a j


#[1]UNION : CTerm1 → CTerm1 → CTerm1
#[1]UNION a b = ct1 (UNION ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] UNION ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ [ 1 ]}
             (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                  (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ [ 1 ]} (CTerm1.closed b)))


#[1]SUM : CTerm1 → CTerm2 → CTerm1
#[1]SUM a b = ct1 (SUM ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUM ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
              (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                   (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[1]PI : CTerm1 → CTerm2 → CTerm1
#[1]PI a b = ct1 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ [ 1 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ [ 1 ]} (CTerm1.closed a))
                      (lowerVars-fvars-[0,1,2] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm2.closed b))))


#[2]PI : CTerm2 → CTerm3 → CTerm2
#[2]PI a b = ct2 (PI ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ [ 2 ] ] PI ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars ⌜ a ⌝ ++ lowerVars (fvars ⌜ b ⌝)} {0 ∷ 1 ∷ [ 2 ]}
                (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ [ 2 ]} (CTerm2.closed a))
                      (lowerVars-fvars-[0,1,2,3] {fvars ⌜ b ⌝} (⊆?→⊆ (CTerm3.closed b))))


#[3]EQ : CTerm3 → CTerm3 → CTerm3 → CTerm3
#[3]EQ a b c = ct3 (EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝) cl
  where
    cl : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] EQ ⌜ a ⌝ ⌜ b ⌝ ⌜ c ⌝
    cl = ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ ++ fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
                 (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                       (⊆++ (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b))
                             (⊆?→⊆ {fvars ⌜ c ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed c))))


#[0]BOOL : CTerm0
#[0]BOOL = ct0 BOOL refl


#[1]BOOL : CTerm1
#[1]BOOL = ct1 BOOL refl


#[2]BOOL : CTerm2
#[2]BOOL = ct2 BOOL refl


#[3]BOOL : CTerm3
#[3]BOOL = ct3 BOOL refl


#[3]FUN : CTerm3 → CTerm3 → CTerm3
#[3]FUN a b = ct3 (FUN ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ 0 ∷ 1 ∷ 2 ∷ [ 3 ] ] FUN ⌜ a ⌝ ⌜ b ⌝
    c rewrite fvars-FUN0 ⌜ a ⌝ ⌜ b ⌝ =
        ⊆→⊆? {fvars ⌜ a ⌝ ++ fvars ⌜ b ⌝ } {0 ∷ 1 ∷ 2 ∷ [ 3 ]}
               (⊆++ (⊆?→⊆ {fvars ⌜ a ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed a))
                     (⊆?→⊆ {fvars ⌜ b ⌝} {0 ∷ 1 ∷ 2 ∷ [ 3 ]} (CTerm3.closed b)))


#[0]DECℕ : CTerm0
#[0]DECℕ = #[0]PI #[0]NAT! (#[1]SQUASH (#[1]UNION (#[1]APPLY #[1]VAR1 #[1]VAR0) (#[1]NEG (#[1]APPLY #[1]VAR1 #[1]VAR0))))


#MPℙ-right : CTerm → CTerm
#MPℙ-right f = #SQUASH (#SUM #NAT! (#[0]APPLY ⌞ f ⌟ #[0]VAR))


#MPℙ-left : CTerm → CTerm
#MPℙ-left f = #NEG (#NEG (#MPℙ-right f))


#MPℙ : ℕ → CTerm
#MPℙ i = #PI (#NAT!→U i) (#[0]FUN #[0]DECℕ (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right))


-- sanity check
⌜#MPℙ⌝ : (i : ℕ) → ⌜ #MPℙ i ⌝ ≡ MPℙ i
⌜#MPℙ⌝ i = refl


sub0-fun-mpℙ : (a : CTerm) → sub0 a (#[0]FUN #[0]MPℙ-left #[0]MPℙ-right)
                              ≡ #FUN (#MPℙ-left a) (#MPℙ-right a)
sub0-fun-mpℙ a =
  ≡sub0-#[0]FUN
    a #[0]MPℙ-left #[0]MPℙ-right (#MPℙ-left a) (#MPℙ-right a)
    (CTerm≡ (≡NEG (≡NEG (≡SET refl (≡SUM refl (≡APPLY e1 refl))))))
    (≡sub0-#[0]SQUASH
      a (#[0]SUM #[0]NAT! (#[1]APPLY #[1]VAR1 #[1]VAR0)) (#SUM #NAT! (#[0]APPLY ⌞ a ⌟ #[0]VAR))
      (CTerm≡ (≡SUM refl (→≡APPLY e refl))))
  where
    e : shiftDown 1 (shiftUp 0 (shiftUp 0 ⌜ a ⌝)) ≡ ⌜ a ⌝
    e rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftDown 1 a = refl

    e1 : shiftDown 2 (shiftUp 0 (shiftUp 0 (shiftUp 0 (CTerm.cTerm a))))
         ≡ shiftUp 1 (CTerm0.cTerm (CTerm→CTerm0 a))
    e1 rewrite #shiftUp 0 a | #shiftUp 0 a | #shiftUp 0 a | #shiftUp 1 a | #shiftDown 2 a = refl


→equalTypes-#MPℙ-left : {n : ℕ} {w : 𝕎·} {a₁ a₂ : CTerm} {i : ℕ}
                         → equalInType n w (#NAT!→U i) a₁ a₂
                         → equalTypes n w (#MPℙ-left a₁) (#MPℙ-left a₂)
→equalTypes-#MPℙ-left {n} {w} {a₁} {a₂} {i} eqt =
  eqTypesNEG← (eqTypesNEG← {!!}) --(→equalTypes-#PI-NEG-ASSERT₂ eqt)



-- This is the axiom of unique choice
--     Π(R : ℕ→𝔹→ℙ).
--        (Π(n:ℕ).∃(b:𝔹).R n b)
--        → (Π(n:ℕ)(b₁:𝔹)(b₂:𝔹).R n b₁ → R n b₂ → b₁=b₂)
--        → ∃(f:ℕ→𝔹).Π(n:ℕ).R n (f n)
-- Could we prove that this is not valid using a choice δ and the relation
--     R n true  = ∀m≥n.δ(m)=0
--     R n false = ¬∀m≥n.δ(m)=0
-- ?
-- If that was the case, we would also be able to invalidate AC₀₀
#uniqueChoice : ℕ → CTerm
#uniqueChoice i =
  #PI (#FUN #NAT (#FUN #BOOL (#UNIV i))) -- R
      (#[0]FUN
        (#[0]PI #[0]NAT (#[1]SQUASH (#[1]SUM #[1]BOOL (#[2]APPLY2 #[2]VAR2 #[2]VAR1 #[2]VAR0)))) -- Condition
        (#[0]FUN
          (#[0]PI #[0]NAT (#[1]PI #[1]BOOL (#[2]PI #[2]BOOL (#[3]FUN (#[3]APPLY2 #[3]VAR3 #[3]VAR2 #[3]VAR1)
                                                                     (#[3]FUN (#[3]APPLY2 #[3]VAR3 #[3]VAR2 #[3]VAR0)
                                                                              (#[3]EQ #[3]VAR1 #[3]VAR0 #[3]BOOL))))))
          (#[0]SQUASH (#[0]SUM (#[0]FUN #[0]NAT #[0]BOOL) (#[1]PI #[1]NAT (#[2]APPLY2 #[2]VAR2 #[2]VAR0 (#[2]APPLY #[2]VAR1 #[2]VAR0)))))))


\end{code}
