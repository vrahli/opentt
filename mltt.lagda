\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Data.Nat using (s≤s) renaming (_<_ to _<ℕ_ ; _≤_ to _≤ℕ_)
open import Data.Nat.Properties
open import Agda.Builtin.Nat
open import Data.Fin using (Fin ; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Agda.Builtin.Equality renaming (_≡_ to _≣_)
open import Agda.Builtin.Sigma renaming (fst to π₁ ; snd to π₂)
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
  using (⊆-refl ; ⊆-trans ; xs⊆x∷xs)
open import Relation.Binary.PropositionalEquality
  using (cong ; cong₂ ; subst₂) renaming (trans to ≣trans ; sym to ≣sym ; subst to ≣subst)
open import Data.List using () renaming ([] to nil ; _∷_ to cons)
open import Data.List.Relation.Unary.Any
open import Data.List.Properties
open import Data.Product
open import Data.Empty
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.Sum
open import Relation.Nullary
open import Axiom.Extensionality.Propositional

-- MLTT imports
open import Tools.Nat using (1+)
open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties using (wk-β ; wk1-sgSubst ; subst-wk)
open import Definition.Typed
--open import Definition.Typed.Properties using (subset*Term ; noNe)
open import Definition.Typed.Weakening renaming (wk to wk⊢)
open import Definition.Typed.Consequences.Substitution using (substType ; substTerm)
--open import Definition.Typed.Consequences.Syntactic using (syntacticEq)
--open import Definition.Typed.Consequences.Canonicity using (sucᵏ)
open import Definition.Typed.EqRelInstance
open import Definition.LogicalRelation --using (Natural-prop)

-- BoxTT imports
open import calculus renaming (Term to BTerm)
open import terms -- renaming (Term to BTerm)
open import util
open import world
open import mod
open import encode
open import choice
open import compatible
open import progress
open import getChoice
open import choiceExt
open import newChoice

module mltt {L : Level}
            (W : PossibleWorlds {L})
            (M : Mod W)
            (C : Choice)
            (K : Compatible {L} W C)
            (P : Progress {L} W C K)
            (G : GetChoice {L} W C K)
            (X : ChoiceExt W C)
            (N : NewChoice W C K G)
            (E : Extensionality 0ℓ (lsuc(lsuc(L))))
            (EC : Encode)
       where

open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
  using (#⇛!sameℕ ; _⇛!_at_ ; _⇓!_at_ ; _#⇛!_at_ ; #⇛!-trans ; ⇛!-trans ; #⇛!-refl)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
  using (→∧≡true)
open import terms8(W)(C)(K)(G)(X)(N)(EC)
  using (⇓NUM→SUC⇓NUM ; #APPLY2 ; #FST ; #SND ; SUM! ; #SUM! ; #⇛!-FST-PAIR ; #⇛!-SND-PAIR)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (TSext-equalTypes-equalInType ; TEQsym-equalTypes ; TEQrefl-equalTypes ; TEQtrans-equalTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (isTypeNAT! ; eqTypesUniv ; equalTypes→equalInType-UNIV ; equalInType→equalTypes-aux ; eqTypesPI← ; eqTypesSUM← ;
         ≡CTerm→eqTypes ; ≡CTerm→equalInType ; eqTypesFALSE ; eqTypesTRUE ; ¬equalInType-FALSE ; NUM-equalInType-NAT! ;
         equalInType-NAT!→ ; equalInType-local ; equalInType-mon ; equalInType-PI→ ; equalInType-PI ; isFam ;
         equalInType-FUN→ ; equalInType-refl ; equalInType-sym ; equalInType-SUM→ ; eqTypesEQ← ; equalInType-EQ)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-TRUE ; equalInType-EQ→₁)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (→equalInType-NAT!)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (≡→equalInType ; eqTypesEQ→ᵣ)
open import props6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (_#⇛ₚ_at_ ; equalInType-#⇛ₚ-left-right-rev ; presPure ; →presPure-NATREC₁ ; →presPure-NATREC₂ ; →presPure-NATREC₃ ;
         equalTypesPI→ₗ ; equalTypesPI→ᵣ ; eqTypesSUM!← ; SUMeq! ; equalInType-SUM!→ ; equalInType-SUM!)
open import uniMon(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalTypes-uni-mon ; equalInType-uni-mon)

open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import sequent2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (valid∈𝕎→valid≡𝕎-UNIV ; valid≡𝕎-sym ; valid≡𝕎-trans ; valid≡𝕎-PI ; valid≡𝕎-SUM! ; valid∈𝕎-mon ; valid≡𝕎-mon ;
         valid∈𝕎→valid≡𝕎 ; valid∈-UNIV)
open import sequent3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (valid∈-PI ; valid∈-SUM! ; valid∈-NAT! ; valid∈-FALSE ; valid∈-UNIT ; valid∈LAMBDA ; valid∈APPLY ; valid∈N0-NAT ;
         valid∈SUC-NAT ; valid∈NATREC ; valid∈-FALSE→ ; valid∈-AX-UNIT ; valid∈-change-type ; valid≡-change-type ;
         valid≡APPLY ; valid≡LAMBDA ; valid≡SUC-NAT ; valid≡-FALSE→ ; valid≡-UNIT)
open import sequent4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (valid∈FST ; valid∈SND ; valid∈PAIR)

∈→ℕ : {n : Nat} {x : Fin n} {A : Term n} {Γ : Con Term n}
    → x ∷ A ∈ Γ
    → Nat
∈→ℕ {.(Nat.suc _)} {.Fin.zero} {.(wk1 _)} {.(_ ∙ _)} here = 0
∈→ℕ {.(Nat.suc _)} {.(Fin.suc _)} {.(wk1 _)} {.(_ ∙ _)} (there i) = Nat.suc (∈→ℕ i)


⟦_⟧T : {n : Nat} {Γ : Con Term n} {σ : Term n}
     → Γ ⊢ σ
     → BTerm
⟦_⟧T {n} {Γ} {.U} (Uⱼ x) = UNIV 1
⟦_⟧T {n} {Γ} {.ℕ} (ℕⱼ x) = NAT!
⟦_⟧T {n} {Γ} {.Empty} (Emptyⱼ x) = FALSE
⟦_⟧T {n} {Γ} {.Unit} (Unitⱼ x) = UNIT
⟦_⟧T {n} {Γ} {.(Π _ ▹ _)} ((Πⱼ_▹_) {F} {G} i j) = PI ⟦ i ⟧T ⟦ j ⟧T
⟦_⟧T {n} {Γ} {.(Σ _ ▹ _)} ((Σⱼ_▹_) {F} {G} i j) = SUM! ⟦ i ⟧T ⟦ j ⟧T
⟦_⟧T {n} {Γ} {σ} (univ x) = UNIV 1


∈→⊢ : {n : Nat} {Γ : Con Term n} {x : Fin n} {σ : Term n}
    → ⊢ Γ
    → x ∷ σ ∈ Γ
    → Γ ⊢ σ
∈→⊢ {Nat.suc n} {Γ ∙ A} {.Fin.zero} {.(wk1 _)} (i ∙ x₁) here = wk⊢ (step id) (i ∙ x₁) x₁
∈→⊢ {Nat.suc n} {Γ ∙ B} {Fin.suc k} {.(wk1 _)} (i ∙ x₁) (there {n} {k} {A} j) = wk⊢ (step id) (i ∙ x₁) z
  where
    z : Γ ⊢ A
    z = ∈→⊢ i j


mutual
  ⊢Π[] : {n : Nat} {Γ : Con Term n} {G : Term (1+ n)} {F a : Term n}
       → Γ ⊢ Π F ▹ G
       → Γ ⊢ a ∷ F
       → Γ ⊢ (G [ a ])
  ⊢Π[] {n} {Γ} {G} {F} {a} (Πⱼ i ▹ i₁) j = substType i₁ j
  ⊢Π[] {n} {Γ} {G} {F} {a} (univ x) j = ⊢Π∷[] x j

  ⊢Π∷[] : {n : Nat} {Γ : Con Term n} {G : Term (1+ n)} {F a A : Term n}
        → Γ ⊢ Π F ▹ G ∷ A
        → Γ ⊢ a ∷ F
        → Γ ⊢ (G [ a ])
  ⊢Π∷[] {n} {Γ} {G} {F} {a} {.U} (Πⱼ i ▹ i₁) j = univ (substTerm i₁ j)
  ⊢Π∷[] {n} {Γ} {G} {F} {a} {A} (conv i x) j = ⊢Π∷[] i j


mutual
  ⊢Σ[] : {n : Nat} {Γ : Con Term n} {G : Term (1+ n)} {F a : Term n}
       → Γ ⊢ Σ F ▹ G
       → Γ ⊢ a ∷ F
       → Γ ⊢ (G [ a ])
  ⊢Σ[] {n} {Γ} {G} {F} {a} (Σⱼ i ▹ i₁) j = substType i₁ j
  ⊢Σ[] {n} {Γ} {G} {F} {a} (univ x) j = ⊢Σ∷[] x j

  ⊢Σ∷[] : {n : Nat} {Γ : Con Term n} {G : Term (1+ n)} {F a A : Term n}
        → Γ ⊢ Σ F ▹ G ∷ A
        → Γ ⊢ a ∷ F
        → Γ ⊢ (G [ a ])
  ⊢Σ∷[] {n} {Γ} {G} {F} {a} {.U} (Σⱼ i ▹ i₁) j = univ (substTerm i₁ j)
  ⊢Σ∷[] {n} {Γ} {G} {F} {a} {A} (conv i x) j = ⊢Σ∷[] i j


mutual
  →▹▹[]ᵣ : {n : Nat} {Γ : Con Term n} {a F G : Term n}
         → Γ ⊢ a ∷ F
         → Γ ⊢ F ▹▹ G
         → Γ ⊢ G
  →▹▹[]ᵣ {n} {Γ} {a} {F} {G} j (Πⱼ i ▹ i₁) = ≣subst (λ x → Γ ⊢ x) (wk1-sgSubst G a) z
    where
      z : Γ ⊢ (wk1 G [ a ])
      z = substType i₁ j
  →▹▹[]ᵣ {n} {Γ} {a} {F} {G} j (univ x) = →▹▹∷[]ᵣ j x

  →▹▹∷[]ᵣ : {n : Nat} {Γ : Con Term n} {a F G A : Term n}
          → Γ ⊢ a ∷ F
          → Γ ⊢ F ▹▹ G ∷ A
          → Γ ⊢ G
  →▹▹∷[]ᵣ {n} {Γ} {a} {F} {G} j (Πⱼ i ▹ i₁) = ≣subst (λ x → Γ ⊢ x) (wk1-sgSubst G a) z
    where
      z : Γ ⊢ (wk1 G [ a ])
      z = univ (substTerm i₁ j)
  →▹▹∷[]ᵣ {n} {Γ} {a} {F} {G} j (conv i x) = →▹▹∷[]ᵣ j i


≣liftSubst : {m n : Nat} {σ τ : Subst m n}
           → ((x : Fin n) → σ x ≣ τ x)
           → (x : Fin (1+ n)) → liftSubst σ x ≣ liftSubst τ x
≣liftSubst {m} {n} {σ} {τ} i Fin.zero = refl
≣liftSubst {m} {n} {σ} {τ} i (Fin.suc x) = cong wk1 (i x)


≣liftSubstn : {m n b : Nat} {σ τ : Subst m n}
            → ((x : Fin n) → σ x ≣ τ x)
            → (x : Fin (b + n)) → liftSubstn σ b x ≣ liftSubstn τ b x
≣liftSubstn {m} {n} {Nat.zero} {σ} {τ} i x = i x
≣liftSubstn {m} {n} {1+ b} {σ} {τ} i x = ≣liftSubst (≣liftSubstn i) x


mutual
  subst-eta : {m n : Nat} {σ τ : Subst m n} {t : Term n}
            → ((x : Fin n) → σ x ≣ τ x)
            → subst σ t ≣ subst τ t
  subst-eta {m} {n} {σ} {τ} {var x} i = i x
  subst-eta {m} {n} {σ} {τ} {gen {bs} k c} i = cong (gen k) (subst-eta-gen i)

  subst-eta-gen : {m n : Nat} {σ τ : Subst m n} {bs : Data.List.List Nat} {c : GenTs Term n bs}
                 → ((x : Fin n) → σ x ≣ τ x)
                 → substGen σ c ≣ substGen τ c
  subst-eta-gen {m} {n} {σ} {τ} {.nil} {[]} i = refl
  subst-eta-gen {m} {n} {σ} {τ} {cons _ _} {GenTs._∷_ {_} {b} t c} i =
    cong₂ GenTs._∷_
      (subst-eta {b + m} {b + n} {liftSubstn σ b} {liftSubstn τ b} {t} (≣liftSubstn {m} {n} {b} {σ} {τ} i))
      (subst-eta-gen i)


▹▹[] : {n : Nat} (F G : Term (1+ n)) (t : Term n)
       → (F ▹▹ G) [ t ] ≣ (F [ t ]) ▹▹ (G [ t ])
▹▹[] {n} F G t = cong₂ Π_▹_ refl (≣trans z (≣sym (wk-β G)))
  where
    i : (x : Fin (1+ n)) → (liftSubst (sgSubst t) ₛ• step id) x ≣ (sgSubst (wk (step id) t) ₛ• lift (step id)) x
    i Fin.zero = refl
    i (Fin.suc x) = refl

    z : subst (liftSubst (sgSubst t)) (wk (step id) G)
      ≣ subst (sgSubst (wk (step id) t)) (wk (lift (step id)) G)
    z = ≣trans (subst-wk G)
               (≣trans (subst-eta
                         {_} {_}
                         {liftSubst (sgSubst t) ₛ• step id}
                         {sgSubst (wk (step id) t) ₛ• lift (step id)} {G} i)
                       (≣sym (subst-wk G)))


{--
-- a variant of canonicity″
-- not true?
canonicity2 : {n : Nat} {Γ : Con Term n} {t : Term n}
            → ⊢ Γ
            → Natural-prop Γ t --Natural-prop Γ {!t!} --Γ t
            → ∃ λ k → Γ ⊢ t ≡ sucᵏ k ∷ ℕ
canonicity2 {n} {Γ} {t} g (sucᵣ (ℕₜ n₁ d n≡n prop)) =
  let a , b = canonicity2 g prop
  in  1+ a , suc-cong (trans (subset*Term (redₜ d)) b)
canonicity2 {n} {Γ} {t} g zeroᵣ = 0 , refl (zeroⱼ g)
canonicity2 {n} {Γ} {t} g (ne (neNfₜ neK ⊢k k≡k)) = {!⊥-elim (noNe ⊢k neK)!}
--}


{--
∷→⊢ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
   → Γ ⊢ t ∷ σ
   → Γ ⊢ σ
∷→⊢ {n} {Γ} {.(Π _ ▹ _)} {.U} (Πⱼ i ▹ i₁) = ∷→⊢ i
∷→⊢ {n} {Γ} {.(Σ _ ▹ _)} {.U} (Σⱼ i ▹ i₁) = ∷→⊢ i
∷→⊢ {n} {Γ} {.ℕ} {.U} (ℕⱼ x) = Uⱼ x
∷→⊢ {n} {Γ} {.Empty} {.U} (Emptyⱼ x) = Uⱼ x
∷→⊢ {n} {Γ} {.Unit} {.U} (Unitⱼ x) = Uⱼ x
∷→⊢ {n} {Γ} {.(var _)} {σ} (var x x₁) = ∈→⊢ x x₁
∷→⊢ {n} {Γ} {.(lam _)} {.(Π _ ▹ _)} (lamⱼ x i) = Πⱼ x ▹ ∷→⊢ i
∷→⊢ {n} {Γ} {.(_ ∘ _)} {.(G [ a ])} ((_∘ⱼ_) {g} {a} {F} {G} i i₁) =
  ⊢Π[] x i₁
  where
    x : Γ ⊢ Π F ▹ G
    x = ∷→⊢ i
∷→⊢ {n} {Γ} {.(prod _ _)} {.(Σ _ ▹ _)} (prodⱼ x x₁ i i₁) = Σⱼ x ▹ x₁
∷→⊢ {n} {Γ} {.(fst _)} {σ} (fstⱼ x x₁ i) = x
∷→⊢ {n} {Γ} {.(snd _)} {.(G [ fst t ])} (sndⱼ{F} {G} {t} x x₁ i) =
  ⊢Σ[] z (fstⱼ x x₁ i)
  where
    z : Γ ⊢ Σ F ▹ G
    z = ∷→⊢ i
∷→⊢ {n} {Γ} {.Definition.Untyped.zero} {.ℕ} (zeroⱼ x) = ℕⱼ x
∷→⊢ {n} {Γ} {.(Definition.Untyped.suc _)} {.ℕ} (sucⱼ i) = ∷→⊢ i
∷→⊢ {n} {Γ} {.(natrec _ _ _ _)} {.(G [ k ])} (natrecⱼ {G} {s} {z} {k} x i i₁ i₂) = {!|!}
  -- canonicity could be useful, but it's only for empty contexts
{--  where
    -- not the way to go
    y1 : Γ ⊢ Π ℕ ▹ (G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑)
    y1 = ∷→⊢ i₁

    y2 : Γ ⊢ ((G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑) [ k ])
    y2 = ⊢Π[] y1 i₂

    y3 : Γ ⊢ G [ k ] ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑ [ k ]
    y3 = ≣subst (λ z → Γ ⊢ z) (▹▹[] G (G [ Definition.Untyped.suc (var Fin.zero) ]↑) k) y2

    y4 : Γ ⊢ (G [ Definition.Untyped.suc (var Fin.zero) ]↑) [ k ]
    y4 = →▹▹[]ᵣ {!!} y3--}
∷→⊢ {n} {Γ} {.(Emptyrec σ _)} {σ} (Emptyrecⱼ x i) = x
∷→⊢ {n} {Γ} {.star} {.Unit} (starⱼ x) = Unitⱼ x
∷→⊢ {n} {Γ} {t} {σ} (conv {t} {A} {B} i x) =
  π₂ (syntacticEq x)
  where
    y : Γ ⊢ A
    y = ∷→⊢ i
--}


-- Conversion of an untyped term
-- TODO: replace the recursive functions below by a call to this function
⟦_⟧ᵤ : {n : Nat} (t : Term n)
     → BTerm
⟦_⟧ᵤ {n} (var x) = VAR (toℕ x)
⟦_⟧ᵤ {n} (gen {.nil} Ukind c) = UNIV 1
⟦_⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) = PI ⟦ t ⟧ᵤ ⟦ t₁ ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) = LAMBDA ⟦ t ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) = APPLY ⟦ t ⟧ᵤ ⟦ t₁ ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) = SUM! ⟦ t ⟧ᵤ ⟦ t₁ ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) = PAIR ⟦ t ⟧ᵤ ⟦ t₁ ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) = FST ⟦ t ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) = SND ⟦ t ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.nil} Natkind []) = NAT!
⟦_⟧ᵤ {n} (gen {.nil} Zerokind []) = N0
⟦_⟧ᵤ {n} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) = SUC ⟦ t ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) = NATREC ⟦ t₃ ⟧ᵤ ⟦ t₁ ⟧ᵤ ⟦ t₂ ⟧ᵤ
⟦_⟧ᵤ {n} (gen {.nil} Unitkind []) = UNIT
⟦_⟧ᵤ {n} (gen {.nil} Starkind []) = AX
⟦_⟧ᵤ {n} (gen {.nil} Emptykind []) = FALSE
⟦_⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) = ⟦ t₁ ⟧ᵤ


¬names-FST : (t : BTerm) → ¬names (FST t) ≣ ¬names t
¬names-FST t with ¬names t
... | true = refl
... | false = refl


¬names-SND : (t : BTerm) → ¬names (SND t) ≣ ¬names t
¬names-SND t with ¬names t
... | true = refl
... | false = refl


noseq-FST : (t : BTerm) → noseq (FST t) ≣ noseq t
noseq-FST t with noseq t
... | true = refl
... | false = refl


noseq-SND : (t : BTerm) → noseq (SND t) ≣ noseq t
noseq-SND t with noseq t
... | true = refl
... | false = refl


¬enc-FST : (t : BTerm) → ¬enc (FST t) ≣ ¬enc t
¬enc-FST t with ¬enc t
... | true = refl
... | false = refl


¬enc-SND : (t : BTerm) → ¬enc (SND t) ≣ ¬enc t
¬enc-SND t with ¬enc t
... | true = refl
... | false = refl


→¬Names-SUM! : {a b : BTerm}
             → ¬Names a
             → ¬Names b
             → ¬Names (SUM! a b)
→¬Names-SUM! {a} {b} na nb
  rewrite na | nb = refl


→¬Seq-SUM! : {a b : BTerm}
           → ¬Seq a
           → ¬Seq b
           → ¬Seq (SUM! a b)
→¬Seq-SUM! {a} {b} na nb
  rewrite na | nb = refl


→¬Enc-SUM! : {a b : BTerm}
           → ¬Enc a
           → ¬Enc b
           → ¬Enc (SUM! a b)
→¬Enc-SUM! {a} {b} na nb
  rewrite na | nb = refl


¬Names⟦⟧ᵤ : {n : Nat} (t : Term n)
          → ¬Names ⟦ t ⟧ᵤ
¬Names⟦⟧ᵤ {n} (var x) = refl
¬Names⟦⟧ᵤ {n} (gen {.nil} Ukind c) = refl
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Names⟦⟧ᵤ t) (¬Names⟦⟧ᵤ t₁)
¬Names⟦⟧ᵤ {n} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) = ¬Names⟦⟧ᵤ t
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Names⟦⟧ᵤ t) (¬Names⟦⟧ᵤ t₁)
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →¬Names-SUM! {⟦ t ⟧ᵤ} {⟦ t₁ ⟧ᵤ} (¬Names⟦⟧ᵤ t) (¬Names⟦⟧ᵤ t₁)
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Names⟦⟧ᵤ t) (¬Names⟦⟧ᵤ t₁)
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) =
  ≣trans (¬names-FST ⟦ t ⟧ᵤ) (¬Names⟦⟧ᵤ t)
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) =
  ≣trans (¬names-SND ⟦ t ⟧ᵤ) (¬Names⟦⟧ᵤ t)
¬Names⟦⟧ᵤ {n} (gen {.nil} Natkind []) = refl
¬Names⟦⟧ᵤ {n} (gen {.nil} Zerokind []) = refl
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) = ¬Names⟦⟧ᵤ t
¬Names⟦⟧ᵤ {n} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) =
  →∧≡true (¬Names⟦⟧ᵤ t₃) (→∧≡true (¬Names⟦⟧ᵤ t₁) (¬Names⟦⟧ᵤ t₂))
¬Names⟦⟧ᵤ {n} (gen {.nil} Unitkind []) = refl
¬Names⟦⟧ᵤ {n} (gen {.nil} Starkind []) = refl
¬Names⟦⟧ᵤ {n} (gen {.nil} Emptykind []) = refl
¬Names⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) = ¬Names⟦⟧ᵤ t₁


¬Seq⟦⟧ᵤ : {n : Nat} (t : Term n)
        → ¬Seq ⟦ t ⟧ᵤ
¬Seq⟦⟧ᵤ {n} (var x) = refl
¬Seq⟦⟧ᵤ {n} (gen {.nil} Ukind c) = refl
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Seq⟦⟧ᵤ t) (¬Seq⟦⟧ᵤ t₁)
¬Seq⟦⟧ᵤ {n} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) = ¬Seq⟦⟧ᵤ t
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Seq⟦⟧ᵤ t) (¬Seq⟦⟧ᵤ t₁)
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →¬Seq-SUM! {⟦ t ⟧ᵤ} {⟦ t₁ ⟧ᵤ} (¬Seq⟦⟧ᵤ t) (¬Seq⟦⟧ᵤ t₁)
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Seq⟦⟧ᵤ t) (¬Seq⟦⟧ᵤ t₁)
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) =
  ≣trans (noseq-FST ⟦ t ⟧ᵤ) (¬Seq⟦⟧ᵤ t)
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) =
  ≣trans (noseq-SND ⟦ t ⟧ᵤ) (¬Seq⟦⟧ᵤ t)
¬Seq⟦⟧ᵤ {n} (gen {.nil} Natkind []) = refl
¬Seq⟦⟧ᵤ {n} (gen {.nil} Zerokind []) = refl
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) = ¬Seq⟦⟧ᵤ t
¬Seq⟦⟧ᵤ {n} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) =
  →∧≡true (¬Seq⟦⟧ᵤ t₃) (→∧≡true (¬Seq⟦⟧ᵤ t₁) (¬Seq⟦⟧ᵤ t₂))
¬Seq⟦⟧ᵤ {n} (gen {.nil} Unitkind []) = refl
¬Seq⟦⟧ᵤ {n} (gen {.nil} Starkind []) = refl
¬Seq⟦⟧ᵤ {n} (gen {.nil} Emptykind []) = refl
¬Seq⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) = ¬Seq⟦⟧ᵤ t₁


¬Enc⟦⟧ᵤ : {n : Nat} (t : Term n)
        → ¬Enc ⟦ t ⟧ᵤ
¬Enc⟦⟧ᵤ {n} (var x) = refl
¬Enc⟦⟧ᵤ {n} (gen {.nil} Ukind c) = refl
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Enc⟦⟧ᵤ t) (¬Enc⟦⟧ᵤ t₁)
¬Enc⟦⟧ᵤ {n} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) = ¬Enc⟦⟧ᵤ t
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Enc⟦⟧ᵤ t) (¬Enc⟦⟧ᵤ t₁)
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →¬Enc-SUM! {⟦ t ⟧ᵤ} {⟦ t₁ ⟧ᵤ} (¬Enc⟦⟧ᵤ t) (¬Enc⟦⟧ᵤ t₁)
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  →∧≡true (¬Enc⟦⟧ᵤ t) (¬Enc⟦⟧ᵤ t₁)
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) =
  ≣trans (¬enc-FST ⟦ t ⟧ᵤ) (¬Enc⟦⟧ᵤ t)
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) =
  ≣trans (¬enc-SND ⟦ t ⟧ᵤ) (¬Enc⟦⟧ᵤ t)
¬Enc⟦⟧ᵤ {n} (gen {.nil} Natkind []) = refl
¬Enc⟦⟧ᵤ {n} (gen {.nil} Zerokind []) = refl
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) = ¬Enc⟦⟧ᵤ t
¬Enc⟦⟧ᵤ {n} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) =
  →∧≡true (¬Enc⟦⟧ᵤ t₃) (→∧≡true (¬Enc⟦⟧ᵤ t₁) (¬Enc⟦⟧ᵤ t₂))
¬Enc⟦⟧ᵤ {n} (gen {.nil} Unitkind []) = refl
¬Enc⟦⟧ᵤ {n} (gen {.nil} Starkind []) = refl
¬Enc⟦⟧ᵤ {n} (gen {.nil} Emptykind []) = refl
¬Enc⟦⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) = ¬Enc⟦⟧ᵤ t₁


⟦_⟧Γ : {n : Nat} (Γ : Con Term n) → hypotheses
⟦_⟧Γ {.0} ε = Data.List.[]
⟦_⟧Γ {.(1+ _)} (Γ ∙ x) = ⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ x ⟧ᵤ


{--
-- intreptation of σ as a BoxTT type
⟦_⟧∈ₜ : {n : Nat} {Γ : Con Term n} {j : Fin n} {σ : Term n}
       → ⊢ Γ
       → j ∷ σ ∈ Γ
       → BTerm
⟦_⟧∈ₜ {n} {Γ} {j} {σ} i k = {!!}
--}


-- Converts an MLTT type (σ here) to its BoxTT type
⟦_⟧ₜ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
     → Γ ⊢ t ∷ σ
     → BTerm
⟦_⟧ₜ {n} {Γ} {t} {σ} i = ⟦ σ ⟧ᵤ
{--
⟦_⟧ₜ {n} {Γ} {.(Π _ ▹ _)} {.U} ((Πⱼ_▹_) {F} {G} A B) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.(Σ _ ▹ _)} {.U} ((Σⱼ_▹_) {F} {G} A B) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.ℕ} {.U} (ℕⱼ x) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.Empty} {.U} (Emptyⱼ x) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.Unit} {.U} (Unitⱼ x) = UNIV 1
⟦_⟧ₜ {n} {Γ} {var j} {σ} (var x x₁) = {!!} --VAR (toℕ j)
⟦_⟧ₜ {n} {Γ} {.(lam _)} {.(Π _ ▹ _)} (lamⱼ {F} {G} {u} x i) = PI ⟦ i ⟧ₜ ⟦ i ⟧ₜ
⟦_⟧ₜ {n} {Γ} {.(_ ∘ _)} {.(G [ a ])} ((_∘ⱼ_) {g} {a} {F} {G} i i₁) = ⟦ i₁ ⟧ₜ
⟦_⟧ₜ {n} {Γ} {.(prod _ _)} {.(Σ _ ▹ _)} (prodⱼ x x₁ i i₁) = SUM ⟦ i ⟧ₜ ⟦ i₁ ⟧ₜ
⟦_⟧ₜ {n} {Γ} {.(fst _)} {σ} (fstⱼ x x₁ i) = ⟦ i ⟧ₜ
⟦_⟧ₜ {n} {Γ} {.(snd _)} {.(G [ fst t ])} (sndⱼ {F} {G} {t} x x₁ i) = ⟦ i ⟧ₜ
⟦_⟧ₜ {n} {Γ} {.Definition.Untyped.zero} {.ℕ} (zeroⱼ x) = NAT!
⟦_⟧ₜ {n} {Γ} {.(Definition.Untyped.suc _)} {.ℕ} (sucⱼ i) = NAT!
⟦_⟧ₜ {n} {Γ} {.(natrec _ _ _ _)} {.(G [ k ])} (natrecⱼ {G} {s} {z} {k} x i i₁ i₂) = ⟦ i₂ ⟧ₜ
⟦_⟧ₜ {n} {Γ} {.(Emptyrec σ _)} {σ} (Emptyrecⱼ x i) = ⟦ i ⟧ₜ
⟦_⟧ₜ {n} {Γ} {.star} {.Unit} (starⱼ x) = VAR n
⟦_⟧ₜ {n} {Γ} {t} {σ} (conv i x) = ⟦ i ⟧ₜ
--}


∈fvars-SUM!→ : {v : Var} {a b : BTerm}
             → v ∈ fvars (SUM! a b)
             → v ∈ fvars a ⊎ v ∈ lowerVars (fvars b)
∈fvars-SUM!→ {v} {a} {b} i
  with ∈-++⁻ ((fvars a Data.List.++ lowerVars (fvars b)) Data.List.++ nil) i
∈fvars-SUM!→ {v} {a} {b} i | inj₁ p
  with ∈-++⁻ (fvars a Data.List.++ lowerVars (fvars b)) p
∈fvars-SUM!→ {v} {a} {b} i | inj₁ p | inj₁ q
  with ∈-++⁻ (fvars a) q
... | inj₁ r = inj₁ r
... | inj₂ r = inj₂ r
∈fvars-SUM!→ {v} {a} {b} i | inj₁ p | inj₂ ()
∈fvars-SUM!→ {v} {a} {b} i | inj₂ ()


fvarsᵤ : {n : Nat} (t : Term n)
        → (v : Var) → v ∈ fvars (⟦ t ⟧ᵤ) → v <ℕ n
fvarsᵤ {n} (var x) v (here px) rewrite px = toℕ<n x
fvarsᵤ {n} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) v i
  with ∈-++⁻ (fvars ⟦ t ⟧ᵤ) i
... | inj₁ k = fvarsᵤ t _ k
... | inj₂ k = s≤s-inj (fvarsᵤ t₁ _ (∈lowerVars→ v (fvars ⟦ t₁ ⟧ᵤ) k))
fvarsᵤ {n} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) v i =
  s≤s-inj (fvarsᵤ t _ (∈lowerVars→ v (fvars ⟦ t ⟧ᵤ) i))
fvarsᵤ {n} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) v i
  with ∈-++⁻ (fvars ⟦ t ⟧ᵤ) i
... | inj₁ k = fvarsᵤ t _ k
... | inj₂ k = fvarsᵤ t₁ _ k
fvarsᵤ {n} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) v i
  with ∈fvars-SUM!→ {v} {⟦ t ⟧ᵤ} {⟦ t₁ ⟧ᵤ} i
... | inj₁ k = fvarsᵤ t _ k
... | inj₂ k = s≤s-inj (fvarsᵤ t₁ _ (∈lowerVars→ v (fvars ⟦ t₁ ⟧ᵤ) k))
fvarsᵤ {n} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) v i
  with ∈-++⁻ (fvars ⟦ t ⟧ᵤ) i
... | inj₁ k = fvarsᵤ t _ k
... | inj₂ k = fvarsᵤ t₁ _ k
fvarsᵤ {n} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) v i
  with ∈-++⁻ (fvars ⟦ t ⟧ᵤ) i
... | inj₁ k = fvarsᵤ t _ k
... | inj₂ ()
fvarsᵤ {n} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) v i
  with ∈-++⁻ (fvars ⟦ t ⟧ᵤ) i
... | inj₁ k = fvarsᵤ t _ k
... | inj₂ ()
fvarsᵤ {n} (gen {.nil} Natkind []) v ()
fvarsᵤ {n} (gen {.nil} Zerokind []) v ()
fvarsᵤ {n} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) v i = fvarsᵤ t _ i
fvarsᵤ {n} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) v i
  with ∈-++⁻ (fvars ⟦ t₃ ⟧ᵤ) i
... | inj₁ k = fvarsᵤ t₃ _ k
... | inj₂ k with ∈-++⁻ (fvars ⟦ t₁ ⟧ᵤ) k
... |   inj₁ k₁ = fvarsᵤ t₁ _ k₁
... |   inj₂ k₁ = fvarsᵤ t₂ _ k₁
fvarsᵤ {n} (gen {.nil} Unitkind []) v ()
fvarsᵤ {n} (gen {.nil} Starkind []) v ()
fvarsᵤ {n} (gen {.nil} Emptykind []) v ()
fvarsᵤ {n} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) v i = fvarsᵤ t₁ _ i
{--
fvarsᵤ {n} {Γ} {.(Π _ ▹ _)} {.U} (Πⱼ i ▹ i₁) v ()
fvarsᵤ {n} {Γ} {.(Σ _ ▹ _)} {.U} (Σⱼ i ▹ i₁) v ()
fvarsᵤ {n} {Γ} {.ℕ} {.U} (ℕⱼ x) v ()
fvarsᵤ {n} {Γ} {.Empty} {.U} (Emptyⱼ x) v ()
fvarsᵤ {n} {Γ} {.Unit} {.U} (Unitⱼ x) v ()
fvarsᵤ {n} {Γ} {.(var _)} {σ} (var x x₁) v (here px) rewrite px = {!!}
fvarsᵤ {n} {Γ} {.(lam _)} {.(Π _ ▹ _)} (lamⱼ x i) = {!!}
fvarsᵤ {n} {Γ} {.(_ ∘ _)} {.(_ [ _ ])} (i ∘ⱼ i₁) = {!!}
fvarsᵤ {n} {Γ} {.(prod _ _)} {.(Σ _ ▹ _)} (prodⱼ x x₁ i i₁) = {!!}
fvarsᵤ {n} {Γ} {.(fst _)} {σ} (fstⱼ x x₁ i) = {!!}
fvarsᵤ {n} {Γ} {.(snd _)} {.(_ [ fst _ ])} (sndⱼ x x₁ i) = {!!}
fvarsᵤ {n} {Γ} {.Definition.Untyped.zero} {.ℕ} (zeroⱼ x) = {!!}
fvarsᵤ {n} {Γ} {.(Definition.Untyped.suc _)} {.ℕ} (sucⱼ i) = {!!}
fvarsᵤ {n} {Γ} {.(natrec _ _ _ _)} {.(_ [ _ ])} (natrecⱼ x i i₁ i₂) = {!!}
fvarsᵤ {n} {Γ} {.(Emptyrec σ _)} {σ} (Emptyrecⱼ x i) = {!!}
fvarsᵤ {n} {Γ} {.star} {.Unit} (starⱼ x) = {!!}
fvarsᵤ {n} {Γ} {t} {σ} (conv i x) = {!!}
--}


¬∈[]→ : {A : Set} (l : Data.List.List A) → ((v : A) → ¬ (v ∈ l)) → l ≣ Data.List.[]
¬∈[]→ {A} Data.List.[] i = refl
¬∈[]→ {A} (x Data.List.∷ l) i = ⊥-elim (i x (here refl))


⟦_⟧ₜ₀ : {t : Term 0} {σ : Term 0}
      → ε ⊢ t ∷ σ
      → CTerm
⟦_⟧ₜ₀ {t} {σ} i =
  ct ⟦ σ ⟧ᵤ (¬∈[]→ (fvars ⟦ σ ⟧ᵤ) j)
  where
  j : (v : Var) → ¬ v ∈ fvars ⟦ σ ⟧ᵤ
  j v k = m<n⇒n≢0 z refl
    where
    z : v <ℕ 0
    z = fvarsᵤ σ v k


⟦_⟧≡ₜ₀ : {t u : Term 0} {σ : Term 0}
      → ε ⊢ t ≡ u ∷ σ
      → CTerm
⟦_⟧≡ₜ₀ {t} {u} {σ} i =
  ct ⟦ σ ⟧ᵤ (¬∈[]→ (fvars ⟦ σ ⟧ᵤ) j)
  where
  j : (v : Var) → ¬ v ∈ fvars ⟦ σ ⟧ᵤ
  j v k = m<n⇒n≢0 z refl
    where
    z : v <ℕ 0
    z = fvarsᵤ σ v k


-- Converts an MLTT term (t here) into a BoxTT term
⟦_⟧ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
    → Γ ⊢ t ∷ σ
    → BTerm
⟦_⟧ {n} {Γ} {t} {σ} i = ⟦ t ⟧ᵤ
{--
⟦_⟧ {n} {Γ} {.(Π _  ▹ _)} {U} ((Πⱼ_▹_) {F} {G} A B) = PI ⟦ A ⟧ ⟦ B ⟧
⟦_⟧ {n} {Γ} {.(Σ _ ▹ _)}  {U} ((Σⱼ_▹_) {F} {G} A B) = SUM ⟦ A ⟧ ⟦ B ⟧
⟦_⟧ {n} {Γ} {ℕ}           {U} (ℕⱼ x)     = NAT!
⟦_⟧ {n} {Γ} {Empty}       {U} (Emptyⱼ x) = FALSE
⟦_⟧ {n} {Γ} {Unit}        {U} (Unitⱼ x)  = UNIT
⟦_⟧ {n} {Γ} {var _}       {σ} (var x i) = VAR (∈→ℕ i)
⟦_⟧ {n} {Γ} {.(lam _)} {.(Π _ ▹ _)} (lamⱼ {F} {G} {u} x i) = LAMBDA ⟦ i ⟧
⟦_⟧ {n} {Γ} {.(_ ∘ _)} {.(G [ a ])} ((_∘ⱼ_) {g} {a} {F} {G} x x₁) = APPLY ⟦ x ⟧ ⟦ x₁ ⟧
⟦_⟧ {n} {Γ} {.(prod _ _)} {.(Σ _ ▹ _)} (prodⱼ x x₁ x₂ x₃) = PAIR ⟦ x₂ ⟧ ⟦ x₃ ⟧
⟦_⟧ {n} {Γ} {.(fst _)} {σ} (fstⱼ x x₁ x₂) = FST ⟦ x₂ ⟧
⟦_⟧ {n} {Γ} {.(snd _)} {.(G [ fst u ])} (sndⱼ {F} {G} {u} x x₁ x₂) = SND ⟦ x₂ ⟧
⟦_⟧ {n} {Γ} {.Definition.Untyped.zero} {.ℕ} (zeroⱼ x) = NUM 0
⟦_⟧ {n} {Γ} {.(Definition.Untyped.suc _)} {.ℕ} (sucⱼ x) = SUC ⟦ x ⟧
⟦_⟧ {n} {Γ} {.(natrec _ _ _ _)} {.(G [ k ])} (natrecⱼ {G} {s} {z} {k} x x₁ x₂ x₃) = NATREC ⟦ x₃ ⟧ ⟦ x₁ ⟧ ⟦ x₂ ⟧
⟦_⟧ {n} {Γ} {.(Emptyrec σ _)} {σ} (Emptyrecⱼ x x₁) = BOT
⟦_⟧ {n} {Γ} {.star} {.Unit} (starⱼ x) = AX
⟦_⟧ {n} {Γ} {t} {σ} (conv x x₁) = ⟦ x ⟧
--}


⟦_⟧₀ : {t : Term 0} {σ : Term 0}
     → ε ⊢ t ∷ σ
     → CTerm
⟦_⟧₀ {t} {σ} i =
  ct ⟦ t ⟧ᵤ (¬∈[]→ (fvars ⟦ t ⟧ᵤ) j)
  where
  j : (v : Var) → ¬ v ∈ fvars ⟦ t ⟧ᵤ
  j v k = m<n⇒n≢0 z refl
    where
    z : v <ℕ 0
    z = fvarsᵤ t v k


⟦_⟧≡ₗ₀ : {t u : Term 0} {σ : Term 0}
     → ε ⊢ t ≡ u ∷ σ
     → CTerm
⟦_⟧≡ₗ₀ {t} {u} {σ} i =
  ct ⟦ t ⟧ᵤ (¬∈[]→ (fvars ⟦ t ⟧ᵤ) j)
  where
  j : (v : Var) → ¬ v ∈ fvars ⟦ t ⟧ᵤ
  j v k = m<n⇒n≢0 z refl
    where
    z : v <ℕ 0
    z = fvarsᵤ t v k


⟦_⟧≡ᵣ₀ : {t u : Term 0} {σ : Term 0}
     → ε ⊢ t ≡ u ∷ σ
     → CTerm
⟦_⟧≡ᵣ₀ {t} {u} {σ} i =
  ct ⟦ u ⟧ᵤ (¬∈[]→ (fvars ⟦ u ⟧ᵤ) j)
  where
  j : (v : Var) → ¬ v ∈ fvars ⟦ u ⟧ᵤ
  j v k = m<n⇒n≢0 z refl
    where
    z : v <ℕ 0
    z = fvarsᵤ u v k


{--
NAT!∈UNIV : (i : Nat) (w : 𝕎·) (j : Nat)
          → equalInType i w (#UNIV j) #NAT! #NAT!
NAT!∈UNIV i w j = {!!}
--}




length⟦⟧Γ : {n : Nat} {Γ : Con Term n}
          → Data.List.length ⟦ Γ ⟧Γ ≣ n
length⟦⟧Γ {0} {ε} = refl
length⟦⟧Γ {1+ n} {Γ ∙ x} =
  ≣trans (length-++ ⟦ Γ ⟧Γ)
         (≣trans (+-comm (Data.List.length ⟦ Γ ⟧Γ) 1)
                 (cong Nat.suc (length⟦⟧Γ {n} {Γ})))


coveredΓ : {n : Nat} (Γ : Con Term n) (σ : Term n)
          → coveredH ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ
coveredΓ {n} Γ σ {x} i = →∈hdom q
  where
  h : x <ℕ n
  h = fvarsᵤ {n} σ x i

  q : x <ℕ Data.List.length ⟦ Γ ⟧Γ
  q rewrite length⟦⟧Γ {n} {Γ} = h



sub-VAR0 : (t : BTerm) → sub t (VAR 0) ≣ t
sub-VAR0 t = shiftDownUp t 0


sub-VAR+ : (t : BTerm) (n : Nat) → sub t (VAR (1+ n)) ≣ VAR n
sub-VAR+ t n = refl


shiftUpN : (m n : Nat) (t : BTerm) → BTerm
shiftUpN m 0 t = t
shiftUpN m (Nat.suc n) t = shiftUp m (shiftUpN m n t)


shiftUpN-UNIV : (k m : Nat) (i : Nat) → shiftUpN k m (UNIV i) ≣ UNIV i
shiftUpN-UNIV k 0 i = refl
shiftUpN-UNIV k (Nat.suc m) i rewrite shiftUpN-UNIV k m i = refl


shiftUpN-PI : (k m : Nat) (a b : BTerm) → shiftUpN k m (PI a b) ≣ PI (shiftUpN k m a) (shiftUpN (Nat.suc k) m b)
shiftUpN-PI k 0 a b = refl
shiftUpN-PI k (Nat.suc m) a b rewrite shiftUpN-PI k m a b = refl


⟦wk⟧ᵤ-var1 : (m n : Nat) (x  : Fin (m + n))
           → 1+ (toℕ x) ≤ℕ m
           → toℕ (wkVar (liftn (step id) m) x) ≣ toℕ x
⟦wk⟧ᵤ-var1 (1+ m) n Fin.zero p = refl
⟦wk⟧ᵤ-var1 (1+ m) n (Fin.suc x) p = cong 1+ (⟦wk⟧ᵤ-var1 m n x (s≤s-inj p))


⟦wk⟧ᵤ-var2 : (m n : Nat) (x  : Fin (m + n))
           → m <ℕ 1+ (toℕ x)
           → toℕ (wkVar (liftn (step id) m) x) ≣ 1+ (toℕ x)
⟦wk⟧ᵤ-var2 Nat.zero n x p = refl
⟦wk⟧ᵤ-var2 (1+ m) n Fin.zero p = ⊥-elim (m+n≮m 1 m p)
⟦wk⟧ᵤ-var2 (1+ m) n (Fin.suc x) p = cong 1+ (⟦wk⟧ᵤ-var2 m n x (s≤s-inj p))


⟦wk⟧ᵤ : {n m : Nat} (t : Term (m + n)) → ⟦ wk (liftn (step id) m) t ⟧ᵤ ≣ shiftUp m ⟦ t ⟧ᵤ
⟦wk⟧ᵤ {n} {m} (var x) with toℕ x <? m
... | yes p = cong VAR (⟦wk⟧ᵤ-var1 m n x p)
... | no  p = cong VAR (⟦wk⟧ᵤ-var2 m n x (≰⇒> p))
⟦wk⟧ᵤ {n} {m} (gen {.nil} Ukind []) = refl
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  cong₂ PI (⟦wk⟧ᵤ {n} {m} t) (⟦wk⟧ᵤ {n} {1+ m} t₁)
⟦wk⟧ᵤ {n} {m} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) =
  cong LAMBDA (⟦wk⟧ᵤ t)
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  cong₂ APPLY (⟦wk⟧ᵤ {n} {m} t) (⟦wk⟧ᵤ {n} {m} t₁)
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  cong₂ SUM! (⟦wk⟧ᵤ {n} {m} t) (⟦wk⟧ᵤ {n} {1+ m} t₁)
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) =
  cong₂ PAIR (⟦wk⟧ᵤ {n} {m} t) (⟦wk⟧ᵤ {n} {m} t₁)
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) =
  cong FST (⟦wk⟧ᵤ t)
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) =
  cong SND (⟦wk⟧ᵤ t)
⟦wk⟧ᵤ {n} {m} (gen {.nil} Natkind []) = refl
⟦wk⟧ᵤ {n} {m} (gen {.nil} Zerokind []) = refl
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) =
  cong SUC (⟦wk⟧ᵤ {n} {m} t)
⟦wk⟧ᵤ {n} {m} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) =
  cong₃ NATREC (⟦wk⟧ᵤ {n} {m} t₃) (⟦wk⟧ᵤ {n} {m} t₁) (⟦wk⟧ᵤ {n} {m} t₂)
⟦wk⟧ᵤ {n} {m} (gen {.nil} Unitkind []) = refl
⟦wk⟧ᵤ {n} {m} (gen {.nil} Starkind []) = refl
⟦wk⟧ᵤ {n} {m} (gen {.nil} Emptykind []) = refl
⟦wk⟧ᵤ {n} {m} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) = ⟦wk⟧ᵤ t₁


⟦[]⟧ᵤ'-var1 : {n m : Nat} (x : Fin (m + 1+ n)) (u : Term n)
            → toℕ x ≣ m
            → ⟦ liftSubstn (consSubst var u) m x ⟧ᵤ ≣ shiftUpN 0 m ⟦ u ⟧ᵤ
⟦[]⟧ᵤ'-var1 {n} {0} Fin.zero u e = refl
⟦[]⟧ᵤ'-var1 {n} {1+ m} (Fin.suc x) u e
  rewrite ≣sym (⟦[]⟧ᵤ'-var1 x u (suc-injective e))
  = ⟦wk⟧ᵤ (liftSubstn (consSubst var u) m x)


sucIf≤-predIf≤-prop1 : (x m : Nat)
                     → ¬ x ≣ m
                     → x ≤ℕ m
                     → sucIf≤ 0 (predIf≤ m x) ≣ 1+ x
sucIf≤-predIf≤-prop1 0 m p q with 0 <? 0
... | yes a = refl
... | no  a = refl
sucIf≤-predIf≤-prop1 (1+ x) m p q with 1+ x ≤? m
... | yes a = refl
... | no  a = ⊥-elim (a q)


sucIf≤-predIf≤-prop2 : (x m : Nat)
                     → ¬ x ≣ m
                     → m <ℕ x
                     → sucIf≤ 0 (predIf≤ m x) ≣ x
sucIf≤-predIf≤-prop2 0 m p q with 0 <? 0
... | yes a = ⊥-elim (n≮n 0 a)
... | no  a = ⊥-elim (m+n≮m 0 m q)
sucIf≤-predIf≤-prop2 (1+ x) m p q with 1+ x ≤? m
... | yes a = ⊥-elim (n≮n m (≤-trans q a))
... | no  a = refl


⟦[]⟧ᵤ'-var2 : {n m : Nat} (x : Fin (m + 1+ n)) (u : Term n)
            → ¬ toℕ x ≣ m
            → ⟦ liftSubstn (consSubst var u) m x ⟧ᵤ ≣ VAR (predIf≤ m (toℕ x))
⟦[]⟧ᵤ'-var2 {n} {0} Fin.zero u p = ⊥-elim (p refl)
⟦[]⟧ᵤ'-var2 {n} {0} (Fin.suc x) u p = refl
⟦[]⟧ᵤ'-var2 {n} {1+ m} Fin.zero u p = refl
⟦[]⟧ᵤ'-var2 {n} {1+ m} (Fin.suc x) u p with 1+ (toℕ x) ≤? 1+ m
... | yes q =
  ≣trans (⟦wk⟧ᵤ {_} {0} (liftSubstn (consSubst var u) m x))
         (≣trans (cong (shiftUp 0) (⟦[]⟧ᵤ'-var2 x u λ z → p (cong 1+ z)))
                 (cong VAR (sucIf≤-predIf≤-prop1 (toℕ x) m (λ z → p (cong 1+ z)) (s≤s-inj q))))
... | no  q =
  ≣trans (⟦wk⟧ᵤ {_} {0} (liftSubstn (consSubst var u) m x))
         (≣trans (cong (shiftUp 0) (⟦[]⟧ᵤ'-var2 x u λ z → p (cong 1+ z)))
                 (cong VAR (sucIf≤-predIf≤-prop2 (toℕ x) m (λ z → p (cong 1+ z)) (≰⇒> (λ z → q (s≤s z))))))


⟦[]⟧ᵤ' : {n m : Nat} (G : Term (m + 1+ n)) (u : Term n)
      → ⟦ subst (liftSubstn (sgSubst u) m) G ⟧ᵤ ≣ subn m (shiftUpN 0 m ⟦ u ⟧ᵤ) ⟦ G ⟧ᵤ
⟦[]⟧ᵤ' {n} {m} (var x) u with toℕ x ≟ m
... | yes p = ⟦[]⟧ᵤ'-var1 x u p
... | no p = ⟦[]⟧ᵤ'-var2 x u p
⟦[]⟧ᵤ' {n} {m} (gen {.nil} Ukind []) u = refl
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ PI (⟦[]⟧ᵤ' t u) (⟦[]⟧ᵤ' {n} {1+ m} t₁ u)
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) u =
  cong LAMBDA (⟦[]⟧ᵤ' {n} {1+ m} t u)
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ APPLY (⟦[]⟧ᵤ' t u) (⟦[]⟧ᵤ' t₁ u)
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ SUM! (⟦[]⟧ᵤ' t u) (⟦[]⟧ᵤ' {n} {1+ m} t₁ u)
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ PAIR (⟦[]⟧ᵤ' t u) (⟦[]⟧ᵤ' t₁ u)
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) u =
  cong FST (⟦[]⟧ᵤ' t u)
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) u =
  cong SND (⟦[]⟧ᵤ' t u)
⟦[]⟧ᵤ' {n} {m} (gen {.nil} Natkind []) u = refl
⟦[]⟧ᵤ' {n} {m} (gen {.nil} Zerokind []) u = refl
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) u =
  cong SUC (⟦[]⟧ᵤ' t u)
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) u =
  cong₃ NATREC (⟦[]⟧ᵤ' t₃ u) (⟦[]⟧ᵤ' t₁ u) (⟦[]⟧ᵤ' t₂ u)
⟦[]⟧ᵤ' {n} {m} (gen {.nil} Unitkind []) u = refl
⟦[]⟧ᵤ' {n} {m} (gen {.nil} Starkind []) u = refl
⟦[]⟧ᵤ' {n} {m} (gen {.nil} Emptykind []) u = refl
⟦[]⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) u = ⟦[]⟧ᵤ' t₁ u


⟦[]⟧ᵤ-as-subn : {n : Nat} (G : Term (1+ n)) (u : Term n)
              → ⟦ G [ u ] ⟧ᵤ ≣ subn 0 ⟦ u ⟧ᵤ ⟦ G ⟧ᵤ
⟦[]⟧ᵤ-as-subn {n} G u = ⟦[]⟧ᵤ' {n} {0} G u


⟦[]⟧ᵤ-as-sub : {n : Nat} (G : Term (1+ n)) (u : Term n)
             → ⟦ G [ u ] ⟧ᵤ ≣ sub ⟦ u ⟧ᵤ ⟦ G ⟧ᵤ
⟦[]⟧ᵤ-as-sub {n} G u = ≣trans (⟦[]⟧ᵤ-as-subn G u) (≣sym (sub≡subn ⟦ u ⟧ᵤ ⟦ G ⟧ᵤ))


⟦[]↑⟧ᵤ'-var1 : {n m : Nat} (x : Fin (m + 1+ n)) (u : Term (1+ n))
            → toℕ x ≣ m
            → ⟦ liftSubstn (consSubst (λ z → var (Fin.suc z)) u) m x ⟧ᵤ ≣ shiftUpN 0 m ⟦ u ⟧ᵤ
⟦[]↑⟧ᵤ'-var1 {n} {0} Fin.zero u e = refl
⟦[]↑⟧ᵤ'-var1 {n} {1+ m} (Fin.suc x) u e
  rewrite ≣sym (⟦[]↑⟧ᵤ'-var1 x u (suc-injective e))
  = ⟦wk⟧ᵤ {m + 1+ n} {0} (liftSubstn (consSubst (λ z → var (Fin.suc z)) u) m x)


sucIf≤0 : (n : Nat) → sucIf≤ 0 n ≣ 1+ n
sucIf≤0 n with n <? 0
... | no p = refl


⟦[]↑⟧ᵤ'-var2 : {n m : Nat} (x : Fin (m + 1+ n)) (u : Term (1+ n))
            → ¬ toℕ x ≣ m
            → ⟦ liftSubstn (consSubst (λ z → var (Fin.suc z)) u) m x ⟧ᵤ ≣ VAR (toℕ x)
⟦[]↑⟧ᵤ'-var2 {n} {0} Fin.zero u p = ⊥-elim (p refl)
⟦[]↑⟧ᵤ'-var2 {n} {0} (Fin.suc x) u p = refl
⟦[]↑⟧ᵤ'-var2 {n} {1+ m} Fin.zero u p = refl
⟦[]↑⟧ᵤ'-var2 {n} {1+ m} (Fin.suc x) u p =
  ≣trans (⟦wk⟧ᵤ {_} {0} (liftSubstn (consSubst (λ z → var (Fin.suc z)) u) m x))
         (≣trans (cong (shiftUp 0) (⟦[]↑⟧ᵤ'-var2 x u (λ z → p (cong 1+ z))))
                 (cong VAR (sucIf≤0 (toℕ x))))


⟦[]↑⟧ᵤ' : {n m : Nat} (G : Term (m + 1+ n)) (u : Term (1+ n))
        → ⟦ subst (liftSubstn (consSubst (wk1Subst idSubst) u) m) G ⟧ᵤ ≣ subi m (shiftUpN 0 m ⟦ u ⟧ᵤ) ⟦ G ⟧ᵤ
⟦[]↑⟧ᵤ' {n} {m} (var x) u with toℕ x ≟ m
... | yes p = ⟦[]↑⟧ᵤ'-var1 x u p
... | no  p = ⟦[]↑⟧ᵤ'-var2 x u p
⟦[]↑⟧ᵤ' {n} {m} (gen {.nil} Ukind []) u = refl
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 1 nil))} Pikind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ PI (⟦[]↑⟧ᵤ' t u) (⟦[]↑⟧ᵤ' {n} {1+ m} t₁ u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 1 nil)} Lamkind (t GenTs.∷ [])) u =
  cong LAMBDA (⟦[]↑⟧ᵤ' {n} {1+ m} t u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 0 nil))} Appkind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ APPLY (⟦[]↑⟧ᵤ' t u) (⟦[]↑⟧ᵤ' t₁ u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ SUM! (⟦[]↑⟧ᵤ' t u) (⟦[]↑⟧ᵤ' {n} {1+ m} t₁ u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 0 nil))} Prodkind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  cong₂ PAIR (⟦[]↑⟧ᵤ' t u) (⟦[]↑⟧ᵤ' t₁ u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 nil)} Fstkind (t GenTs.∷ [])) u =
  cong FST (⟦[]↑⟧ᵤ' t u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 nil)} Sndkind (t GenTs.∷ [])) u =
  cong SND (⟦[]↑⟧ᵤ' t u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.nil} Natkind []) u = refl
⟦[]↑⟧ᵤ' {n} {m} (gen {.nil} Zerokind []) u = refl
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 nil)} Suckind (t GenTs.∷ [])) u =
  cong SUC (⟦[]↑⟧ᵤ' t u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 1 (cons 0 (cons 0 (cons 0 nil))))} Natreckind (t GenTs.∷ (t₁ GenTs.∷ (t₂ GenTs.∷ (t₃ GenTs.∷ []))))) u =
  cong₃ NATREC (⟦[]↑⟧ᵤ' t₃ u) (⟦[]↑⟧ᵤ' t₁ u) (⟦[]↑⟧ᵤ' t₂ u)
⟦[]↑⟧ᵤ' {n} {m} (gen {.nil} Unitkind []) u = refl
⟦[]↑⟧ᵤ' {n} {m} (gen {.nil} Starkind []) u = refl
⟦[]↑⟧ᵤ' {n} {m} (gen {.nil} Emptykind []) u = refl
⟦[]↑⟧ᵤ' {n} {m} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) u =
  ⟦[]↑⟧ᵤ' t₁ u


⟦[]↑⟧ᵤ : {n m : Nat} (G : Term (1+ n)) (u : Term (1+ n))
        → ⟦ G [ u ]↑ ⟧ᵤ ≣ subi 0 ⟦ u ⟧ᵤ ⟦ G ⟧ᵤ
⟦[]↑⟧ᵤ {n} {m} G u = ⟦[]↑⟧ᵤ' {n} {0} G u


⟦▹▹⟧ᵤ : {n : Nat} (A B : Term n)
      → ⟦ A ▹▹ B ⟧ᵤ ≣ FUN ⟦ A ⟧ᵤ ⟦ B ⟧ᵤ
⟦▹▹⟧ᵤ {n} A B = cong₂ PI refl (⟦wk⟧ᵤ {n} {0} B)


shiftDown-subv-subsN1# : (s : Sub) (u t : BTerm) (#u : # u)
                       → shiftDown 0 (subv 0 u (subsN 1 s t))
                       ≣ subs (s Data.List.∷ʳ ct u #u) t
shiftDown-subv-subsN1# s u t #u =
  ≣trans c (sub-subsN1 (ct u #u) s t)
  where
  c : shiftDown 0 (subv 0 u (subsN 1 s t)) ≣ shiftDown 0 (subv 0 (shiftUp 0 u) (subsN 1 s t))
  c rewrite #shiftUp 0 (ct u #u) = refl


⟦wk1⟧ᵤ : {n : Nat} (t : Term n) → ⟦ wk1 t ⟧ᵤ ≣ shiftUp 0 ⟦ t ⟧ᵤ
⟦wk1⟧ᵤ {n} t = ⟦wk⟧ᵤ {n} {0} t


valid∈VAR : {n : Nat} {Γ : Con Term n} {σ : Term n} {x : Fin n}
          → x ∷ σ ∈ Γ
          → (i : Nat) (w : 𝕎·) → valid∈ i w ⟦ Γ ⟧Γ (VAR (toℕ x)) ⟦ σ ⟧ᵤ
valid∈VAR {1+ n} {Γ ∙ A} {.(wk1 A)} {.Fin.zero} here i w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite ⟦wk1⟧ᵤ {n} A =
  c1 , c2
  where
  c1 : equalTypes i w (#subs s1 (shiftUp 0 ⟦ A ⟧ᵤ) cc1) (#subs s2 (shiftUp 0 ⟦ A ⟧ᵤ) cc2)
  c1 with ≡hyps∷ʳ→ i w s1 s2 ⟦ Γ ⟧Γ ⟦ Γ ⟧Γ ⟦ A ⟧ᵤ ⟦ A ⟧ᵤ eh
  ... | t1 , t2 , ss1 , ss2 , cA , cB , e1 , e2 , eH , eT
    rewrite e1 | e2
    = ≡CTerm→eqTypes (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss1 t1 ⟦ A ⟧ᵤ))) (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss2 t2 ⟦ A ⟧ᵤ))) eT

  c2 : equalInType i w (#subs s1 (shiftUp 0 ⟦ A ⟧ᵤ) cc1) (#subs s1 (VAR 0) ce1) (#subs s2 (VAR 0) ce2)
  c2 with ≡subs∷ʳ→ i w s1 s2 ⟦ Γ ⟧Γ ⟦ A ⟧ᵤ es
  ... | t1 , t2 , ss1 , ss2 , cA , e1 , e2 , eS , eT
    rewrite e1 | e2
    = ≡→equalInType (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss1 t1 ⟦ A ⟧ᵤ)))
                    (≣sym (CTerm≡ (subs∷ʳ-VAR0 ss1 t1)))
                    (≣sym (CTerm≡ (subs∷ʳ-VAR0 ss2 t2)))
                    eT
valid∈VAR {1+ n} {Γ ∙ B} {.(wk1 _)} {Fin.suc x} (there {_} {_} {A} j) i w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite ⟦wk1⟧ᵤ {n} A
  with ≡hyps∷ʳ→ i w s1 s2 ⟦ Γ ⟧Γ ⟦ Γ ⟧Γ ⟦ B ⟧ᵤ ⟦ B ⟧ᵤ eh
... | t1 , t2 , ss1 , ss2 , cB1 , cB2 , e1 , e2 , eH , eT
  rewrite e1 | e2
  with ≡subs∷ʳ→₂ i w ss1 ss2 t1 t2 ⟦ Γ ⟧Γ ⟦ B ⟧ᵤ es
... | cB , eS , eT'
  = c1 , c2
  where
  ind : valid∈ i w ⟦ Γ ⟧Γ (VAR (toℕ x)) ⟦ A ⟧ᵤ
  ind = valid∈VAR {n} {Γ} {A} {x} j i w

  cA1 : covered ss1 ⟦ A ⟧ᵤ
  cA1 = covered∷ʳ-shiftUp→ ss1 t1 ⟦ A ⟧ᵤ cc1

  cA2 : covered ss2 ⟦ A ⟧ᵤ
  cA2 = covered∷ʳ-shiftUp→ ss2 t2 ⟦ A ⟧ᵤ cc2

  cV1 : covered ss1 (VAR (toℕ x))
  cV1 = covered∷ʳ-shiftUp→ ss1 t1 (VAR (toℕ x)) ce1

  cV2 : covered ss2 (VAR (toℕ x))
  cV2 = covered∷ʳ-shiftUp→ ss2 t2 (VAR (toℕ x)) ce2

  c1 : equalTypes i w (#subs (ss1 Data.List.∷ʳ t1) (shiftUp 0 ⟦ A ⟧ᵤ) cc1)
                      (#subs (ss2 Data.List.∷ʳ t2) (shiftUp 0 ⟦ A ⟧ᵤ) cc2)
  c1 = ≡CTerm→eqTypes (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss1 t1 ⟦ A ⟧ᵤ)))
                      (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss2 t2 ⟦ A ⟧ᵤ)))
                      (π₁ (ind ss1 ss2 cA1 cA2 cV1 cV2 eS eH))

  c2 : equalInType i w (#subs (ss1 Data.List.∷ʳ t1) (shiftUp 0 ⟦ A ⟧ᵤ) cc1)
                       (#subs (ss1 Data.List.∷ʳ t1) (VAR (1+ (toℕ x))) ce1)
                       (#subs (ss2 Data.List.∷ʳ t2) (VAR (1+ (toℕ x))) ce2)
  c2 = ≡→equalInType (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss1 t1 ⟦ A ⟧ᵤ)))
                     (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss1 t1 (VAR (toℕ x)))))
                     (CTerm≡ (≣sym (subs∷ʳ-shiftUp ss2 t2 (VAR (toℕ x)))))
                     (π₂ (ind ss1 ss2 cA1 cA2 cV1 cV2 eS eH))


{--
⊢≡∷ : {n : Nat} {Γ : Con Term n} {σ τ : Term n}
    → Γ ⊢ σ ≡ τ ∷ U
    → Γ ⊢ σ × Γ ⊢ τ
⊢≡∷ {n} {Γ} {σ} {τ} i = {!!}


-- Isn't that proved somewhere?
⊢≡ : {n : Nat} {Γ : Con Term n} {σ τ : Term n}
   → Γ ⊢ σ ≡ τ
   → Γ ⊢ σ × Γ ⊢ τ
⊢≡ {n} {Γ} {σ} {τ} (univ x) = {!!}
⊢≡ {n} {Γ} {σ} {.σ} (refl x) = x , x
⊢≡ {n} {Γ} {σ} {τ} (sym i) = π₂ (⊢≡ i) , π₁ (⊢≡ i)
⊢≡ {n} {Γ} {σ} {τ} (trans i i₁) = π₁ (⊢≡ i) , π₂ (⊢≡ i₁)
⊢≡ {n} {Γ} {.(Π _ ▹ _)} {.(Π _ ▹ _)} (Π-cong x i i₁) =
  Πⱼ x ▹ (π₁ (⊢≡ i₁)) , Πⱼ π₂ (⊢≡ i) ▹ {!!}
⊢≡ {n} {Γ} {.(Σ _ ▹ _)} {.(Σ _ ▹ _)} (Σ-cong x i i₁) =
  Σⱼ x ▹ (π₁ (⊢≡ i₁)) , Σⱼ π₂ (⊢≡ i) ▹ {!!}
--}


1+<→ : {a b : Nat} → 1+ a <ℕ b → a <ℕ b
1+<→ {a} {b} h = <-trans ≤-refl h


mutual

  ⟦_⟧Γ≡ : {n : Nat} {Γ : Con Term n} {σ τ : Term n}
          (j : Γ ⊢ σ ≡ τ)
          (i k : Nat) (ltk : 1 <ℕ k) (lti : k <ℕ i)
        → valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ ⟦ τ ⟧ᵤ (UNIV k)
  ⟦_⟧Γ≡ {n} {Γ} {σ} {τ} (univ x) i k ltk lti =
    valid≡𝕎-mon ltk lti h1
    where
    h1 : valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ ⟦ τ ⟧ᵤ (UNIV 1)
    h1 = ⟦_⟧Γ≡∈ x i (≤-trans (s≤s ltk) lti)
  ⟦_⟧Γ≡ {n} {Γ} {σ} {.σ} (refl x) i k ltk lti =
    valid∈𝕎→valid≡𝕎-UNIV i k ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ h1
    where
    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ (UNIV k)
    h1 = ⟦_⟧⊢ x i k ltk lti
  ⟦_⟧Γ≡ {n} {Γ} {σ} {τ} (sym j) i k ltk lti =
    valid≡𝕎-sym i ⟦ Γ ⟧Γ ⟦ τ ⟧ᵤ ⟦ σ ⟧ᵤ (UNIV k) h1
    where
    h1 : valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ τ ⟧ᵤ ⟦ σ ⟧ᵤ (UNIV k)
    h1 = ⟦_⟧Γ≡ j i k ltk lti
  ⟦_⟧Γ≡ {n} {Γ} {σ} {τ} (trans {σ} {ϕ} {τ} j j₁) i k ltk lti =
    valid≡𝕎-trans i ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ ⟦ ϕ ⟧ᵤ ⟦ τ ⟧ᵤ (UNIV k) cov h1 h2
    where
    h1 : valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ ⟦ ϕ ⟧ᵤ (UNIV k)
    h1 = ⟦_⟧Γ≡ j i k ltk lti

    h2 : valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ ϕ ⟧ᵤ ⟦ τ ⟧ᵤ (UNIV k)
    h2 = ⟦_⟧Γ≡ j₁ i k ltk lti

    cov : coveredH ⟦ Γ ⟧Γ ⟦ ϕ ⟧ᵤ
    cov = coveredΓ {n} Γ ϕ
  ⟦_⟧Γ≡ {n} {Γ} {.(Π _ ▹ _)} {.(Π _ ▹ _)} (Π-cong {F} {H} {G} {E} x j j₁) i k ltk lti =
    valid≡𝕎-PI i k lti ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ ⟦ H ⟧ᵤ ⟦ E ⟧ᵤ h1 h2
    where
    h1 : valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ H ⟧ᵤ (UNIV k)
    h1 = ⟦_⟧Γ≡ j i k ltk lti

    h2 : valid≡𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ ⟦ E ⟧ᵤ (UNIV k)
    h2 = ⟦_⟧Γ≡ j₁ i k ltk lti
  ⟦_⟧Γ≡ {n} {Γ} {.(Σ _ ▹ _)} {.(Σ _ ▹ _)} (Σ-cong {F} {H} {G} {E} x j j₁) i k ltk lti =
    valid≡𝕎-SUM! i k lti ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ ⟦ H ⟧ᵤ ⟦ E ⟧ᵤ h1 h2
    where
    h1 : valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ H ⟧ᵤ (UNIV k)
    h1 = ⟦_⟧Γ≡ j i k ltk lti

    h2 : valid≡𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ ⟦ E ⟧ᵤ (UNIV k)
    h2 = ⟦_⟧Γ≡ j₁ i k ltk lti


  -- TODO: Should this instead follow from ⟦_⟧Γ≡∈?
  ⟦_⟧Γ∈ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
          (j : Γ ⊢ t ∷ σ)
          (i : Nat) (lti : 2 <ℕ i)
        → valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ σ ⟧ᵤ
  ⟦_⟧Γ∈ {n} {Γ} {.(Π _ ▹ _)} {.U} ((Πⱼ_▹_) {F} {G} j j₁) i lti w =
    valid∈-PI i 1 (1+<→ lti) ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ h1 h2 w
    where
    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
    h1 = ⟦_⟧Γ∈ j i lti

    h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
    h2 = ⟦_⟧Γ∈ j₁ i lti
  ⟦_⟧Γ∈ {n} {Γ} {.(Σ _ ▹ _)} {.U} ((Σⱼ_▹_) {F} {G} j j₁) i lti w =
    valid∈-SUM! i 1 (1+<→ lti) ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ h1 h2 w
    where
    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
    h1 = ⟦_⟧Γ∈ j i lti

    h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
    h2 = ⟦_⟧Γ∈ j₁ i lti
  ⟦_⟧Γ∈ {n} {Γ} {.ℕ} {.U} (ℕⱼ x) i lti w = valid∈-NAT! i 1 (1+<→ lti) ⟦ Γ ⟧Γ w
  ⟦_⟧Γ∈ {n} {Γ} {.Empty} {.U} (Emptyⱼ x) i lti w = valid∈-FALSE i 1 (1+<→ lti) ⟦ Γ ⟧Γ w
  ⟦_⟧Γ∈ {n} {Γ} {.Unit} {.U} (Unitⱼ x) i lti w = valid∈-UNIT i 1 (1+<→ lti) ⟦ Γ ⟧Γ w
  ⟦_⟧Γ∈ {n} {Γ} {.(var _)} {σ} (var {σ} {v} x x₁) i lti w =
    valid∈VAR x₁ i w
  ⟦_⟧Γ∈ {n} {Γ} {.(lam _)} {.(Π _ ▹ _)} (lamⱼ {F} {G} {t} x j) i lti w =
    valid∈LAMBDA lti h1 h2 w
    where
    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 2)
    h1 = ⟦_⟧⊢ x i 2 ≤-refl lti

    h2 : valid∈𝕎 i ⟦ Γ ∙ F ⟧Γ ⟦ t ⟧ᵤ ⟦ G ⟧ᵤ
    h2 = ⟦_⟧Γ∈ j i lti
  ⟦_⟧Γ∈ {n} {Γ} {.(_ ∘ _)} {.(G [ a ])} ((_∘ⱼ_) {g} {a} {F} {G} j j₁) i lti w =
    ≣subst (valid∈ i w ⟦ Γ ⟧Γ (APPLY ⟦ g ⟧ᵤ ⟦ a ⟧ᵤ))
           (≣sym (⟦[]⟧ᵤ-as-subn G a))
           (valid∈APPLY covF h1 h2 w)
    where
    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ a ⟧ᵤ ⟦ F ⟧ᵤ
    h1 = ⟦_⟧Γ∈ j₁ i lti

    h2 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ g ⟧ᵤ (PI ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ)
    h2 = ⟦_⟧Γ∈ j i lti

    covF : coveredH ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ
    covF = coveredΓ {n} Γ F
  ⟦_⟧Γ∈ {n} {Γ} {.(prod _ _)} {.(Σ _ ▹ _)} (prodⱼ {F} {G} {t} {u} x x₁ j j₁) i lti w =
    valid∈PAIR lti h1 h2 h3 h4' w
    where
    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 2)
    h1 = ⟦_⟧⊢ x i 2 ≤-refl lti

    h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 2)
    h2 = ⟦_⟧⊢ x₁ i 2 ≤-refl lti

    h3 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ F ⟧ᵤ
    h3 = ⟦_⟧Γ∈ j i lti

    h4 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ u ⟧ᵤ ⟦ G [ t ] ⟧ᵤ
    h4 = ⟦_⟧Γ∈ j₁ i lti

    h4' : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ u ⟧ᵤ (subn 0 ⟦ t ⟧ᵤ ⟦ G ⟧ᵤ)
    h4' rewrite ≣sym (⟦[]⟧ᵤ-as-subn {n} G t) = h4
  ⟦_⟧Γ∈ {n} {Γ} {.(fst _)} {F} (fstⱼ {F} {G} {t} x x₁ j) i lti w =
    valid∈FST lti covH h1 h2 h3 w
    where
    covH : coveredH (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ
    covH = coveredΓ {1+ n} (Γ ∙ F) G

    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 2)
    h1 = ⟦_⟧⊢ x i 2 ≤-refl lti

    h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 2)
    h2 = ⟦_⟧⊢ x₁ i 2 ≤-refl lti

    h3 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ (SUM! ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ)
    h3 = ⟦_⟧Γ∈ j i lti
  ⟦_⟧Γ∈ {n} {Γ} {.(snd _)} {.(G [ fst u ])} (sndⱼ {F} {G} {u} x x₁ j) i lti w =
    ≣subst (valid∈ i w ⟦ Γ ⟧Γ (SND ⟦ u ⟧ᵤ))
           (≣sym (⟦[]⟧ᵤ-as-subn G (fst u)))
           (valid∈SND lti covH h1 h2 h3 w)
    where
    covH : coveredH ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ
    covH = coveredΓ {n} Γ F

    h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 2)
    h1 = ⟦_⟧⊢ x i 2 ≤-refl lti

    h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 2)
    h2 = ⟦_⟧⊢ x₁ i 2 ≤-refl lti

    h3 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ u ⟧ᵤ (SUM! ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ)
    h3 = ⟦_⟧Γ∈ j i lti
  ⟦_⟧Γ∈ {n} {Γ} {.Definition.Untyped.zero} {.ℕ} (zeroⱼ x) i lti w =
    valid∈N0-NAT i w ⟦ Γ ⟧Γ
  ⟦_⟧Γ∈ {n} {Γ} {.(Definition.Untyped.suc _)} {.ℕ} (sucⱼ {x} j) i lti w =
    valid∈SUC-NAT h1
    where
    h1 : valid∈ i w ⟦ Γ ⟧Γ ⟦ x ⟧ᵤ NAT!
    h1 = ⟦_⟧Γ∈ j i lti w
  ⟦_⟧Γ∈ {n} {Γ} {.(natrec _ _ _ _)} {.(G [ k ])} (natrecⱼ {G} {s} {z} {k} x j j₁ j₂) i lti w =
    ≣subst (valid∈ i w ⟦ Γ ⟧Γ (NATREC ⟦ k ⟧ᵤ ⟦ z ⟧ᵤ ⟦ s ⟧ᵤ))
           (≣sym (⟦[]⟧ᵤ-as-subn G k))
           (valid∈NATREC {i} {2} {⟦ Γ ⟧Γ} {⟦ G ⟧ᵤ} {⟦ k ⟧ᵤ} {⟦ z ⟧ᵤ} {⟦ s ⟧ᵤ} lti h1 h2' h3'' h4 w)
    -- valid∈NATREC and use ⟦[]⟧ᵤ-as-sub
    where
    h1 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp NAT!) ⟦ G ⟧ᵤ (UNIV 2)
    h1 = ⟦_⟧⊢ x i 2 ≤-refl lti

    h2 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ z ⟧ᵤ ⟦ G [ Definition.Untyped.zero ] ⟧ᵤ
    h2 = ⟦_⟧Γ∈ j i lti

    h2' : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ z ⟧ᵤ (subn 0 N0 ⟦ G ⟧ᵤ)
    h2' rewrite ≣sym (⟦[]⟧ᵤ-as-subn {n} G Definition.Untyped.zero) = h2

    h3 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ s ⟧ᵤ ⟦ Π ℕ ▹ (G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑) ⟧ᵤ
    h3 = ⟦_⟧Γ∈ j₁ i lti

    h3' : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ s ⟧ᵤ (PI NAT! (FUN ⟦ G ⟧ᵤ ⟦ G [ Definition.Untyped.suc (var Fin.zero) ]↑ ⟧ᵤ))
    h3' = ≣subst (λ z → valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ s ⟧ᵤ (PI NAT! z)) (⟦▹▹⟧ᵤ G (G [ Definition.Untyped.suc (var Fin.zero) ]↑)) h3

    h3'' : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ s ⟧ᵤ (PI NAT! (FUN ⟦ G ⟧ᵤ (subi 0 (SUC (VAR 0)) ⟦ G ⟧ᵤ)))
    h3'' = ≣subst (λ z → valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ s ⟧ᵤ (PI NAT! (FUN ⟦ G ⟧ᵤ z))) (⟦[]↑⟧ᵤ {_} {0} G (Definition.Untyped.suc (var Fin.zero))) h3'

    h4 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ k ⟧ᵤ NAT!
    h4 = ⟦_⟧Γ∈ j₂ i lti
  ⟦_⟧Γ∈ {n} {Γ} {.(Emptyrec σ _)} {σ} (Emptyrecⱼ {A} {e} x j) i lti w =
    valid∈-FALSE→ i w ⟦ Γ ⟧Γ ⟦ e ⟧ᵤ ⟦ σ ⟧ᵤ h1
    where
    h1 : valid∈ i w ⟦ Γ ⟧Γ ⟦ e ⟧ᵤ FALSE
    h1 = ⟦_⟧Γ∈ j i lti w
  ⟦_⟧Γ∈ {n} {Γ} {.star} {.Unit} (starⱼ x) i lti w = valid∈-AX-UNIT i ⟦ Γ ⟧Γ w
  ⟦_⟧Γ∈ {n} {Γ} {t} {σ} (conv {t} {τ} {σ} j x) i lti w =
    valid∈-change-type {i} {2} {w} {⟦ Γ ⟧Γ} {⟦ τ ⟧ᵤ} {⟦ σ ⟧ᵤ} lti cov h1 h2
    where
    h1 : valid≡ i w ⟦ Γ ⟧Γ ⟦ τ ⟧ᵤ ⟦ σ ⟧ᵤ (UNIV 2)
    h1 = ⟦_⟧Γ≡ x i 2 ≤-refl lti w

    h2 : valid∈ i w ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ τ ⟧ᵤ
    h2 = ⟦_⟧Γ∈ j i lti w

    cov : coveredH ⟦ Γ ⟧Γ ⟦ τ ⟧ᵤ
    cov = coveredΓ {n} Γ τ


  -- TODO: Can we prove this one from ⟦_⟧Γ≡?
  ⟦_⟧⊢ : {n : Nat} {Γ : Con Term n} {σ : Term n}
         (j : Γ ⊢ σ)
         (i k : Nat) (ltk : 1 <ℕ k) (lti : k <ℕ i)
       → valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ (UNIV k)
  ⟦_⟧⊢ {n} {Γ} {.U} (Uⱼ x) i k ltk lti w = valid∈-UNIV i k 1 ltk lti ⟦ Γ ⟧Γ w
  ⟦_⟧⊢ {n} {Γ} {.ℕ} (ℕⱼ x) i k ltk lti w = valid∈-NAT! i k lti ⟦ Γ ⟧Γ w
  ⟦_⟧⊢ {n} {Γ} {.Empty} (Emptyⱼ x) i k ltk lti w = valid∈-FALSE i k lti ⟦ Γ ⟧Γ w
  ⟦_⟧⊢ {n} {Γ} {.Unit} (Unitⱼ x) i k ltk lti w = valid∈-UNIT i k lti ⟦ Γ ⟧Γ w
  ⟦_⟧⊢ {n} {Γ} {.(Π _ ▹ _)} (Πⱼ_▹_ {F} {G} j j₁) i k ltk lti w =
    valid∈-PI i k lti ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ (⟦_⟧⊢ j i k ltk lti) (⟦_⟧⊢ j₁ i k ltk lti) w
  ⟦_⟧⊢ {n} {Γ} {.(Σ _ ▹ _)} (Σⱼ_▹_ {F} {G} j j₁) i k ltk lti w =
    valid∈-SUM! i k lti ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ (⟦_⟧⊢ j i k ltk lti) (⟦_⟧⊢ j₁ i k ltk lti) w
  ⟦_⟧⊢ {n} {Γ} {σ} (univ x) i k ltk lti w = valid∈𝕎-mon ltk lti (⟦ x ⟧Γ∈ i (≤-trans (s≤s ltk) lti)) w -- lti w


  ⟦_⟧Γ≡∈ : {n : Nat} {Γ : Con Term n} {t u : Term n} {σ : Term n}
           (j : Γ ⊢ t ≡ u ∷ σ)
           (i : Nat) (lti : 2 <ℕ i)
         → valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ u ⟧ᵤ ⟦ σ ⟧ᵤ
  ⟦_⟧Γ≡∈ {n} {Γ} {t} {.t} {σ} (refl x) i lti =
    valid∈𝕎→valid≡𝕎 i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ σ ⟧ᵤ (⟦ x ⟧Γ∈ i lti)
  ⟦_⟧Γ≡∈ {n} {Γ} {t} {u} {σ} (sym j) i lti =
    valid≡𝕎-sym i ⟦ Γ ⟧Γ ⟦ u ⟧ᵤ ⟦ t ⟧ᵤ ⟦ σ ⟧ᵤ (⟦ j ⟧Γ≡∈ i lti)
  ⟦_⟧Γ≡∈ {n} {Γ} {t} {u} {σ} (trans {t} {v} j j₁) i lti =
    valid≡𝕎-trans i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ v ⟧ᵤ ⟦ u ⟧ᵤ ⟦ σ ⟧ᵤ
      (coveredΓ {n} Γ v) (⟦ j ⟧Γ≡∈ i lti) (⟦ j₁ ⟧Γ≡∈ i lti)
  ⟦_⟧Γ≡∈ {n} {Γ} {t} {u} {B} (conv {A} {B} j x) i lti w =
    valid≡-change-type lti (coveredΓ {n} Γ A) (⟦ x ⟧Γ≡ i 2 ≤-refl lti w) (⟦ j ⟧Γ≡∈ i lti w)
  ⟦_⟧Γ≡∈ {n} {Γ} {.(Π _ ▹ _)} {.(Π _ ▹ _)} {.U} (Π-cong {E} {F} {G} {H} x j j₁) i lti =
    valid≡𝕎-PI i 1 (1+<→ lti) ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ ⟦ H ⟧ᵤ ⟦ E ⟧ᵤ (⟦ j ⟧Γ≡∈ i lti) (⟦ j₁ ⟧Γ≡∈ i lti)
  ⟦_⟧Γ≡∈ {n} {Γ} {.(Σ _ ▹ _)} {.(Σ _ ▹ _)} {.U} (Σ-cong {E} {F} {G} {H} x j j₁) i lti =
    valid≡𝕎-SUM! i 1 (1+<→ lti) ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ ⟦ H ⟧ᵤ ⟦ E ⟧ᵤ (⟦ j ⟧Γ≡∈ i lti) (⟦ j₁ ⟧Γ≡∈ i lti)
  ⟦_⟧Γ≡∈ {n} {Γ} {.(_ ∘ _)} {.(_ ∘ _)} {.(G [ a ])} (app-cong {a} {b} {f} {g} {F} {G} j j₁) i lti =
    ≣subst
      (valid≡𝕎 i ⟦ Γ ⟧Γ (APPLY ⟦ f ⟧ᵤ ⟦ a ⟧ᵤ) (APPLY ⟦ g ⟧ᵤ ⟦ b ⟧ᵤ))
      (≣sym (⟦[]⟧ᵤ-as-subn G a))
      (valid≡APPLY (coveredΓ {n} Γ F) (⟦ j₁ ⟧Γ≡∈ i lti) (⟦ j ⟧Γ≡∈ i lti))
  ⟦_⟧Γ≡∈ {n} {Γ} {.(lam _ ∘ _)} {.(t [ a ])} {.(G [ a ])} (β-red {a} {t} {F} {G} x x₁ x₂) i lti =
    subst₂
      (valid≡𝕎 i ⟦ Γ ⟧Γ (APPLY (LAMBDA ⟦ t ⟧ᵤ) ⟦ a ⟧ᵤ))
      (≣sym (⟦[]⟧ᵤ-as-subn t a))
      (≣sym (⟦[]⟧ᵤ-as-subn G a))
      (valid≡LAMBDA {i} {2} lti (coveredΓ {n} Γ F) (⟦ x ⟧⊢ i 2 ≤-refl lti) (⟦ x₂ ⟧Γ∈ i lti) (⟦ x₁ ⟧Γ∈ i lti))
  ⟦_⟧Γ≡∈ {n} {Γ} {t} {u} {.(Π _ ▹ _)} (η-eq x x₁ x₂ j) i lti = {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(fst _)} {.(fst _)} {σ} (fst-cong x x₁ j) i lti = {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(snd _)} {.(snd _)} {.(G [ fst t ])} (snd-cong {t} {t'} {F} {G} x x₁ j) i lti = {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(fst (prod u _))} {u} {σ} (Σ-β₁ x x₁ x₂ x₃) i lti = {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(snd (prod _ u))} {u} {.(G [ fst (prod t u) ])} (Σ-β₂ {F} {G} {t} {u} x x₁ x₂ x₃) i lti = {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {t} {u} {.(Σ _ ▹ _)} (Σ-η x x₁ x₂ x₃ j j₁) i lti = {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(Definition.Untyped.suc _)} {.(Definition.Untyped.suc _)} {.ℕ} (suc-cong j) i lti =
    valid≡SUC-NAT (⟦_⟧Γ≡∈ j i lti)
  ⟦_⟧Γ≡∈ {n} {Γ} {.(natrec _ _ _ _)} {.(natrec _ _ _ _)} {.(F [ m ])} (natrec-cong {z} {z'} {s} {s'} {m} {m'} {F} {F'} x j j₁ j₂) i lti =
    {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(natrec _ u _ Definition.Untyped.zero)} {u} {.(F [ Definition.Untyped.zero ])} (natrec-zero {z} {s} {F} x x₁ x₂) i lti =
    {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(natrec _ _ _ (Definition.Untyped.suc _))} {.((_ ∘ _) ∘ natrec _ _ _ _)} {.(F [ Definition.Untyped.suc m ])} (natrec-suc {m} {z} {s} {F} x x₁ x₂ x₃) i lti =
    {!!}
  ⟦_⟧Γ≡∈ {n} {Γ} {.(Emptyrec σ _)} {.(Emptyrec _ _)} {σ} (Emptyrec-cong x j) i lti =
    valid≡-FALSE→ (⟦_⟧Γ≡∈ j i lti)
  ⟦_⟧Γ≡∈ {n} {Γ} {t} {u} {.Unit} (η-unit x x₁) i lti =
    valid≡-UNIT i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ u ⟧ᵤ


{--
  ⟦_⟧≡∈ : {t u : Term 0} {σ : Term 0}
          (j : ε ⊢ t ≡ u ∷ σ)
          (i : Nat) (w : 𝕎·)
        → equalInType i w ⟦ j ⟧≡ₜ₀ ⟦ j ⟧≡ₗ₀ ⟦ j ⟧≡ᵣ₀ -- in the empty context
  ⟦_⟧≡∈ {t} {u} {σ} j i w = {!!}
--}

\end{code}
