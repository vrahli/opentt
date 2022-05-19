\begin{code}
{-# OPTIONS --rewriting #-}
--{-# OPTIONS --auto-inline #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
--open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning
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


open import util
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
open import choiceBar


module continuity7 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G) (V : ChoiceVal W C K G X N)
                   (F : Freeze {L} W C K P G N)
                   (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
                   (CB : ChoiceBar W M C K P G X N V F E) -- TODO - We won't need everything from there: use a different module
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)
open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
open import terms4(W)(C)(K)(G)(X)(N)
open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
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
open import choiceValDef(W)(C)(K)(G)(X)(N)(V)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

open import choiceBarDef(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)

{--
open import type_sys_props_nat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qnat(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_qlt(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_free(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_pi(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_sum(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_set(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_eq(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_union(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_tsquash(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_ffdefs(W)(M)(C)(K)(P)(G)(E)
open import type_sys_props_lift(W)(M)(C)(K)(P)(G)(E)
--}

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)


cont : Term
cont =
  PI BAIRE→NAT
     (FUN (FFDEFS BAIRE→NAT (VAR 0))
          (PI BAIRE
              (FUN (FFDEFS BAIRE (VAR 0))
                   (SUBSING (contBody (VAR 1) (VAR 0))))))


#cont : CTerm
#cont = ct cont c
  where
    c : # cont
    c = refl



#[0]BAIRE→NAT : CTerm0
#[0]BAIRE→NAT = ct0 BAIRE→NAT c
  where
    c : #[ [ 0 ] ] BAIRE→NAT
    c = refl



#[1]SUBSING : CTerm1 → CTerm1
#[1]SUBSING t = ct1 (SUBSING ⌜ t ⌝) c
  where
    c : #[ 0 ∷ [ 1 ] ] SUBSING ⌜ t ⌝
    c = CTerm1.closed t


#[0]SUBSING : CTerm0 → CTerm0
#[0]SUBSING t = ct0 (SUBSING ⌜ t ⌝) c
  where
    c : #[ [ 0 ] ] SUBSING ⌜ t ⌝
    c = CTerm0.closed t



≡++ : {L : Level} {A : Set(L)} {a b c d : List A}
      → a ≡ b → c ≡ d → a ++ c ≡ b ++ d
≡++ {L} {A} {a} {b} {c} {d} e f rewrite e | f = refl



++⊆ : {L : Level} {A : Set(L)} {a b c : List A}
      → a ⊆ c → b ⊆ c → a ++ b ⊆ c
++⊆ {L} {A} {a} {b} {c} i j {x} k with ∈-++⁻ a k
... | inj₁ z = i z
... | inj₂ z = j z


--fvars-contBody : (a b : Term) → fvars (contBody a b) ≡ fvars a ++ fvars a
--fvars-contBody a b = ≡++ {_} {_} {fvars a} {fvars a} {fvars b} {fvars b} {!!} {!!}


lowerVars++ : (a b : List Var) → lowerVars (a ++ b) ≡ lowerVars a ++ lowerVars b
lowerVars++ [] b = refl
lowerVars++ (0 ∷ a) b = lowerVars++ a b
lowerVars++ (suc x ∷ a) b rewrite lowerVars++ a b = refl



lowerVars-fvars-shiftUp1 : (t : Term) → lowerVars (fvars (shiftUp 1 t)) ≡ Data.List.map (sucIf≤ 0) (lowerVars (fvars t))
lowerVars-fvars-shiftUp1 t rewrite fvars-shiftUp≡ 1 t | lowerVars-map-sucIf≤-suc 0 (fvars t) = refl



lowerVars-fvars-[0,1,2,3] : {l : List Var}
                        → l ⊆ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
                        → lowerVars l ⊆ 0 ∷ 1 ∷ [ 2 ]
lowerVars-fvars-[0,1,2,3] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ [ 3 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ [ 3 ]) →  x₁ ∈ 0 ∷ 1 ∷ [ 2 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
lowerVars-fvars-[0,1,2,3] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3] (λ z → h (there z)) x



lowerVars-fvars-[0,1,2,3,4] : {l : List Var}
                        → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
                        → lowerVars l ⊆ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
lowerVars-fvars-[0,1,2,3,4] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3,4] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3,4] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]) →  x₁ ∈ 0 ∷ 1 ∷ 2 ∷ [ 3 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
    i (there (there (there (there (here px))))) = there (there (there (here (suc-injective px))))
lowerVars-fvars-[0,1,2,3,4] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3,4] (λ z → h (there z)) x



lowerVars-fvars-[0,1,2,3,4,5] : {l : List Var}
                        → l ⊆ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
                        → lowerVars l ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
lowerVars-fvars-[0,1,2,3,4,5] {0 ∷ l} h x = lowerVars-fvars-[0,1,2,3,4,5] (λ z → h (there z)) x
lowerVars-fvars-[0,1,2,3,4,5] {suc x₁ ∷ l} h (here px) rewrite px = i z
  where
    z : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ])
    z = h (here refl)

    i : suc x₁ ∈ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]) →  x₁ ∈ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
    i (there (here px)) = here (suc-injective px)
    i (there (there (here px))) = there (here (suc-injective px))
    i (there (there (there (here px)))) = there (there (here (suc-injective px)))
    i (there (there (there (there (here px))))) = there (there (there (here (suc-injective px))))
    i (there (there (there (there (there (here px)))))) = there (there (there (there (here (suc-injective px)))))
lowerVars-fvars-[0,1,2,3,4,5] {suc x₁ ∷ l} h (there x) = lowerVars-fvars-[0,1,2,3,4,5] (λ z → h (there z)) x


12⊆01234 : 1 ∷ [ 2 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ [ 4 ]
12⊆01234 {x} (here px) rewrite px = there (here refl)
12⊆01234 {x} (there (here px)) rewrite px = there (there (here refl))


23⊆012345 : 2 ∷ [ 3 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
23⊆012345 {x} (here px) rewrite px = there (there (here refl))
23⊆012345 {x} (there (here px)) rewrite px = there (there (there (here refl)))


2⊆012345 : [ 2 ] ⊆ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ [ 5 ]
2⊆012345 {x} (here px) rewrite px = there (there (here refl))



fvars-shiftUp0-CTerm1 : (a : CTerm1) → fvars (shiftUp 0 ⌜ a ⌝) ⊆ 1 ∷ [ 2 ]
fvars-shiftUp0-CTerm1 a {x} i rewrite fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ suc i
... | (z , j , e) rewrite e = q p
  where
    p : z ∈ 0 ∷ [ 1 ]
    p = ⊆?→⊆ (CTerm1.closed a) j

    q : z ∈ 0 ∷ [ 1 ] → suc z ∈ 1 ∷ 2 ∷ []
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)



fvars-shiftUp10-CTerm1 : (a : CTerm1) → fvars (shiftUp 1 (shiftUp 0 ⌜ a ⌝)) ⊆ 2 ∷ [ 3 ]
fvars-shiftUp10-CTerm1 a {x} i rewrite fvars-shiftUp≡ 1 (shiftUp 0 ⌜ a ⌝) with ∈-map⁻ (sucIf≤ 1) i
... | (z , j , e) rewrite e | fvars-shiftUp≡ 0 ⌜ a ⌝ with ∈-map⁻ (sucIf≤ 0) j
... | (z' , j' , e') rewrite e' = q p
  where
    p : z' ∈ 0 ∷ [ 1 ]
    p = ⊆?→⊆ (CTerm1.closed a) j'

    q : z' ∈ 0 ∷ [ 1 ] → suc (suc z') ∈ 2 ∷ 3 ∷ []
    q (here px) rewrite px = here refl
    q (there (here px)) rewrite px = there (here refl)



#[1]contBody : CTerm1 → CTerm1 → CTerm1
#[1]contBody a b = ct1 (contBody ⌜ a ⌝ ⌜ b ⌝) c
  where
    d : lowerVars
      (lowerVars
       (lowerVars
        ((fvars (shiftUp 0 (CTerm1.cTerm b)) ++ sucIf≤ 0 0 ∷ 2 ∷ []) ++
         lowerVars
         ((fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
           fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b))))
          ++
          (fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
           sucIf≤ 1 (sucIf≤ 0 0) ∷ [])
          ++ [])))) ⊆ 0 ∷ 1 ∷ []
    d rewrite sucIf≤00
            | ++[] (fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++ 2 ∷ [])
      = lowerVars-fvars-[0,1,2]
          {lowerVars
           (lowerVars
            ((fvars (shiftUp 0 (CTerm1.cTerm b)) ++ 1 ∷ 2 ∷ []) ++
             lowerVars
             ((fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
               fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b))))
              ++ fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++ 2 ∷ [])))}
          (lowerVars-fvars-[0,1,2,3]
             {lowerVars
              ((fvars (shiftUp 0 (CTerm1.cTerm b)) ++ 1 ∷ 2 ∷ []) ++
               lowerVars
               ((fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
                 fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b))))
                ++ fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++ 2 ∷ []))}
             (lowerVars-fvars-[0,1,2,3,4]
                {(fvars (shiftUp 0 (CTerm1.cTerm b)) ++ 1 ∷ 2 ∷ []) ++
                 lowerVars
                 ((fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
                   fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b))))
                  ++ fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++ 2 ∷ [])}
                (++⊆ {_} {_} {fvars (shiftUp 0 (CTerm1.cTerm b)) ++ 1 ∷ 2 ∷ []}
                   {lowerVars
                    ((fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
                      fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b))))
                     ++ fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++ 2 ∷ [])}
                   (++⊆ {_} {_} {fvars (shiftUp 0 (CTerm1.cTerm b))} {1 ∷ 2 ∷ []}
                        (⊆-trans (fvars-shiftUp0-CTerm1 b) 12⊆01234)
                        12⊆01234)
                   (lowerVars-fvars-[0,1,2,3,4,5]
                      {(fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
                        fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b))))
                       ++ fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++ 2 ∷ []}
                      (++⊆ {_} {_}
                         {fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++
                          fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b)))}
                         {fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a))) ++ 2 ∷ []}
                         (++⊆ {_} {_} {fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a)))}
                            {fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm b)))}
                              (⊆-trans (fvars-shiftUp10-CTerm1 a) 23⊆012345)
                              (⊆-trans (fvars-shiftUp10-CTerm1 b) 23⊆012345))
                         (++⊆ {_} {_} {fvars (shiftUp 1 (shiftUp 0 (CTerm1.cTerm a)))}
                            {[ 2 ]} (⊆-trans (fvars-shiftUp10-CTerm1 a) 23⊆012345) 2⊆012345))))))

    c : #[ 0 ∷ [ 1 ] ] contBody ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars (contBody ⌜ a ⌝ ⌜ b ⌝)} {0 ∷ [ 1 ]} d



#[0]contBody : CTerm0 → CTerm0 → CTerm0
#[0]contBody a b = ct0 (contBody ⌜ a ⌝ ⌜ b ⌝) c
  where
    c : #[ [ 0 ] ] contBody ⌜ a ⌝ ⌜ b ⌝
    c = ⊆→⊆? {fvars (contBody ⌜ a ⌝ ⌜ b ⌝)} {[ 0 ]} {!!}



#CONT : CTerm
#CONT =
  #PI #BAIRE→NAT
      (#[0]FUN (#[0]FFDEFS #[0]BAIRE→NAT #[0]VAR)
               (#[0]PI #[0]BAIRE
                       (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                (#[1]SUBSING (#[1]contBody #[1]VAR1 #[1]VAR0)))))



contExt : Term
contExt = LAMBDA (LAMBDA (LAMBDA (LAMBDA (PAIR (νtestM (VAR 3) (VAR 1)) lam3AX))))



#contExt : CTerm
#contExt = ct contExt c
  where
    c : # contExt
    c = refl


#cont≡ : #cont ≡ #CONT
#cont≡ = refl


isType-BAIRE→NAT : (i : ℕ) (w : 𝕎·) → isType i w #BAIRE→NAT
isType-BAIRE→NAT i w =
  eqTypesFUN← eqTypesBAIRE eqTypesNAT




sub0-cont-b1 : (F : CTerm)
               → sub0 F
                       (#[0]FUN (#[0]FFDEFS #[0]BAIRE→NAT #[0]VAR)
                                (#[0]PI #[0]BAIRE
                                        (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                 (#[1]SUBSING (#[1]contBody #[1]VAR1 #[1]VAR0)))))
                 ≡ #FUN (#FFDEFS #BAIRE→NAT F)
                        (#PI #BAIRE
                             (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                                 (#[0]SUBSING (#[0]contBody ⌞ F ⌟ #[0]VAR))))
sub0-cont-b1 F = CTerm≡ e0
  where
    e0 : sub ⌜ F ⌝ (FUN (FFDEFS BAIRE→NAT (VAR 0))
                    (PI BAIRE
                        (FUN (FFDEFS BAIRE (VAR 0))
                             (SUBSING (contBody (VAR 1) (VAR 0))))))
         ≡ FUN (FFDEFS BAIRE→NAT ⌜ F ⌝)
               (PI BAIRE
                   (FUN (FFDEFS BAIRE (VAR 0))
                        (SUBSING (contBody ⌜ F ⌝ (VAR 0)))))
    e0 rewrite #shiftUp 0 F | #shiftDown 0 F
             | #shiftUp 1 F | #shiftUp 4 F | #shiftUp 6 F = {!refl!} -- ?



continuity : (cn : comp→∀ℕ) (kb : K□) (gc : get-choose-ℕ)
             (i : ℕ) (w : 𝕎·)
             → ∈Type i w #cont #contExt
continuity cn kb gc i w =
  ≡CTerm→equalInType
    (sym #cont≡)
    (equalInType-PI
      (λ w' e' → isType-BAIRE→NAT i w')
      h1
      {!!})
  where
    h1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                       → equalInType i w' #BAIRE→NAT a₁ a₂
                       → equalTypes i w' (sub0 a₁ (#[0]FUN (#[0]FFDEFS #[0]BAIRE→NAT #[0]VAR)
                                                           (#[0]PI #[0]BAIRE
                                                                   (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                            (#[1]SUBSING (#[1]contBody #[1]VAR1 #[1]VAR0))))))
                                          (sub0 a₂ (#[0]FUN (#[0]FFDEFS #[0]BAIRE→NAT #[0]VAR)
                                                           (#[0]PI #[0]BAIRE
                                                                   (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                            (#[1]SUBSING (#[1]contBody #[1]VAR1 #[1]VAR0)))))))
    h1 w1 e1 F₁ F₂ eF = {!!}

\end{code}
