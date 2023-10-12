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
open import Definition.Typed.Properties using (subset*Term ; noNe)
open import Definition.Typed.Weakening renaming (wk to wk⊢)
open import Definition.Typed.Consequences.Substitution using (substType ; substTerm)
open import Definition.Typed.Consequences.Syntactic using (syntacticEq)
open import Definition.Typed.Consequences.Canonicity using (sucᵏ)
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
  using (⇓NUM→SUC⇓NUM ; #APPLY2 ; #FST ; #SND ; SUM! ; #SUM! ; #⇛!-FST-PAIR)
open import subst(W)(C)(K)(G)(X)(N)(EC)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (eqTypes-mon)
open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (TSext-equalTypes-equalInType ; TEQsym-equalTypes ; TEQrefl-equalTypes ; TEQtrans-equalTypes)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (isTypeNAT! ; eqTypesUniv ; equalTypes→equalInType-UNIV ; equalInType→equalTypes-aux ; eqTypesPI← ; eqTypesSUM← ;
         ≡CTerm→eqTypes ; ≡CTerm→equalInType ; eqTypesFALSE ; eqTypesTRUE ; ¬equalInType-FALSE ; NUM-equalInType-NAT! ;
         equalInType-NAT!→ ; equalInType-local ; equalInType-mon ; equalInType-PI→ ; equalInType-PI ; isFam ;
         equalInType-FUN→ ; equalInType-refl ; equalInType-sym ; equalInType-SUM→)
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


valid∈-NAT! : (i : Nat) (lti : 1 <ℕ i) (H : hypotheses)
              → valid∈𝕎 i H NAT! (UNIV 1)
valid∈-NAT! i lti H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-NAT! s1 ce1 | #subs-NAT! s2 ce2 | #subs-UNIV s1 1 cc1 | #subs-UNIV s2 1 cc2
  = eqTypesUniv w i 1 lti , e
  where
    e : equalInType i w (#UNIV 1) #NAT! #NAT!
    e = equalTypes→equalInType-UNIV {i} {1} lti {w} {#NAT!} {#NAT!} isTypeNAT!


valid∈-FALSE : (i : Nat) (lti : 1 <ℕ i) (H : hypotheses)
             → valid∈𝕎 i H FALSE (UNIV 1)
valid∈-FALSE i lti H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-FALSE s1 ce1 | #subs-FALSE s2 ce2 | #subs-UNIV s1 1 cc1 | #subs-UNIV s2 1 cc2
  = eqTypesUniv w i 1 lti , e
  where
    e : equalInType i w (#UNIV 1) #FALSE #FALSE
    e = equalTypes→equalInType-UNIV {i} {1} lti {w} {#FALSE} {#FALSE} eqTypesFALSE


valid∈-UNIT : (i : Nat) (lti : 1 <ℕ i) (H : hypotheses)
             → valid∈𝕎 i H UNIT (UNIV 1)
valid∈-UNIT i lti H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-UNIT s1 ce1 | #subs-UNIT s2 ce2 | #subs-UNIV s1 1 cc1 | #subs-UNIV s2 1 cc2
  = eqTypesUniv w i 1 lti , e
  where
    e : equalInType i w (#UNIV 1) #TRUE #TRUE
    e = equalTypes→equalInType-UNIV {i} {1} lti {w} {#TRUE} {#TRUE} eqTypesTRUE


valid∈-AX-UNIT : (i : Nat) (lti : 1 <ℕ i) (H : hypotheses)
               → valid∈𝕎 i H AX UNIT
valid∈-AX-UNIT i lti H w s1 s2 cc1 cc2 ce1 ce2 eqs eqh
  rewrite #subs-UNIT s1 cc1 | #subs-UNIT s2 cc2 | #subs-AX s1 ce1 | #subs-AX s2 ce2
  = eqTypesTRUE , →equalInType-TRUE i


valid∈-FALSE→ : (i : Nat) (w : 𝕎·) (H : hypotheses) (a T : BTerm)
              → valid∈ i w H a FALSE
              → valid∈ i w H a T
valid∈-FALSE→ i w H a T h s1 s2 cc1 cc2 ce1 ce2 eqs eqh =
  ⊥-elim (¬equalInType-FALSE h2)
  where
  h1 : equalInType i w (#subs s1 FALSE (covered-FALSE s1)) (#subs s1 a ce1) (#subs s2 a ce2)
  h1 = π₂ (h s1 s2 (covered-FALSE s1) (covered-FALSE s2) ce1 ce2 eqs eqh)

  h2 : equalInType i w #FALSE (#subs s1 a ce1) (#subs s2 a ce2)
  h2 = ≡CTerm→equalInType (#subs-FALSE s1 (covered-FALSE s1)) h1


valid∈-PI : (i : Nat) (lti : 1 <ℕ i) (H : hypotheses) (F G : BTerm)
            → valid∈𝕎 i H F (UNIV 1)
            → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV 1)
            → valid∈𝕎 i H (PI F G) (UNIV 1)
valid∈-PI i lti H F G vF vG w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-UNIV s1 1 cc1 | #subs-UNIV s2 1 cc2
        | #subs-PI2 s1 F G ce1 | #subs-PI2 s2 F G ce2
  = h1 , h2
  where
  h1 : equalTypes i w (#UNIV 1) (#UNIV 1)
  h1 = eqTypesUniv w i 1 lti

  ha : ∀𝕎 w (λ w' _ → equalTypes 1 w' (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2)))
  ha w1 e1 = vf2
    where
    vf1 : equalInType i w1 (#UNIV 1) (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2))
    vf1 = ≡CTerm→equalInType
            (#subs-UNIV s1 1 cc1)
            (π₂ (vF w1 s1 s2 cc1 cc2 (coveredPI₁ {s1} {F} {G} ce1) (coveredPI₁ {s2} {F} {G} ce2) (≡subs-mon e1 es) (≡hyps-mon e1 eh)))

    vf2 : equalTypes 1 w1 (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2))
    vf2 = equalInType→equalTypes-aux i 1 lti w1
            (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1))
            (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2))
            vf1

  hb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType 1 w' (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) a₁ a₂
                    → equalTypes
                        1 w'
                        (sub0 a₁ (#[0]subs s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                        (sub0 a₂ (#[0]subs s2 G (coveredPI₂ {s2} {F} {G} ce2))))
  hb w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (≣sym (sub0-#[0]subs a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
      (≣sym (sub0-#[0]subs a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
      hb1
    where
    vg1 : equalInType i w1 (#UNIV 1) (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                                     (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 Data.List.∷ʳ a₁) 1 λ {x} ())
            (π₂ (vG w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂) (λ {x} ()) (λ {x} ())
                    (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1))
                    (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2))
                    (≡subs∷ʳ i w1 s1 s2 H F (coveredPI₁ {s1} {F} {G} ce1) a₁ a₂
                      (equalInType-uni-mon (<⇒≤ lti) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H F F (coveredPI₁ {s1} {F} {G} ce1) (coveredPI₁ {s2} {F} {G} ce2) a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) (ha w1 e1))
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes 1 w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
    hb1 = equalInType→equalTypes-aux i 1 lti w1
            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredPI₂ {s1} {F} {G} ce1)))
            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredPI₂ {s2} {F} {G} ce2)))
            vg1

  h2 : equalInType i w (#UNIV 1)
                       (#PI (#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)) (#[0]subs s1 G (coveredPI₂ {s1} {F} {G} ce1)))
                       (#PI (#subs s2 F (coveredPI₁ {s2} {F} {G} ce2)) (#[0]subs s2 G (coveredPI₂ {s2} {F} {G} ce2)))
  h2 = equalTypes→equalInType-UNIV
         lti
         (eqTypesPI←
           {w} {1}
           {#subs s1 F (coveredPI₁ {s1} {F} {G} ce1)} {#[0]subs s1 G (coveredPI₂ {s1} {F} {G} ce1)}
           {#subs s2 F (coveredPI₁ {s2} {F} {G} ce2)} {#[0]subs s2 G (coveredPI₂ {s2} {F} {G} ce2)}
           ha hb)


valid∈-SUM : (i : Nat) (lti : 1 <ℕ i) (H : hypotheses) (F G : BTerm)
            → valid∈𝕎 i H F (UNIV 1)
            → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV 1)
            → valid∈𝕎 i H (SUM F G) (UNIV 1)
valid∈-SUM i lti H F G vF vG w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-UNIV s1 1 cc1 | #subs-UNIV s2 1 cc2
        | #subs-SUM2 s1 F G ce1 | #subs-SUM2 s2 F G ce2
  = h1 , h2
  where
  h1 : equalTypes i w (#UNIV 1) (#UNIV 1)
  h1 = eqTypesUniv w i 1 lti

  ha : ∀𝕎 w (λ w' _ → equalTypes 1 w' (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2)))
  ha w1 e1 = vf2
    where
    vf1 : equalInType i w1 (#UNIV 1) (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2))
    vf1 = ≡CTerm→equalInType
            (#subs-UNIV s1 1 cc1)
            (π₂ (vF w1 s1 s2 cc1 cc2 (coveredSUM₁ {s1} {F} {G} ce1) (coveredSUM₁ {s2} {F} {G} ce2) (≡subs-mon e1 es) (≡hyps-mon e1 eh)))

    vf2 : equalTypes 1 w1 (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2))
    vf2 = equalInType→equalTypes-aux i 1 lti w1
            (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1))
            (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2))
            vf1

  hb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType 1 w' (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) a₁ a₂
                    → equalTypes
                        1 w'
                        (sub0 a₁ (#[0]subs s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                        (sub0 a₂ (#[0]subs s2 G (coveredSUM₂ {s2} {F} {G} ce2))))
  hb w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (≣sym (sub0-#[0]subs a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
      (≣sym (sub0-#[0]subs a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
      hb1
    where
    vg1 : equalInType i w1 (#UNIV 1) (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                                     (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 Data.List.∷ʳ a₁) 1 λ {x} ())
            (π₂ (vG w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂) (λ {x} ()) (λ {x} ())
                    (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1))
                    (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2))
                    (≡subs∷ʳ i w1 s1 s2 H F (coveredSUM₁ {s1} {F} {G} ce1) a₁ a₂
                      (equalInType-uni-mon (<⇒≤ lti) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H F F (coveredSUM₁ {s1} {F} {G} ce1) (coveredSUM₁ {s2} {F} {G} ce2) a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) (ha w1 e1))
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes 1 w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
    hb1 = equalInType→equalTypes-aux i 1 lti w1
            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
            vg1

  h2 : equalInType i w (#UNIV 1)
                       (#SUM (#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)) (#[0]subs s1 G (coveredSUM₂ {s1} {F} {G} ce1)))
                       (#SUM (#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2)) (#[0]subs s2 G (coveredSUM₂ {s2} {F} {G} ce2)))
  h2 = equalTypes→equalInType-UNIV
         lti
         (eqTypesSUM←
           {w} {1}
           {#subs s1 F (coveredSUM₁ {s1} {F} {G} ce1)} {#[0]subs s1 G (coveredSUM₂ {s1} {F} {G} ce1)}
           {#subs s2 F (coveredSUM₁ {s2} {F} {G} ce2)} {#[0]subs s2 G (coveredSUM₂ {s2} {F} {G} ce2)}
           ha hb)


valid∈-SUM! : (i : Nat) (lti : 1 <ℕ i) (H : hypotheses) (F G : BTerm)
            → valid∈𝕎 i H F (UNIV 1)
            → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV 1)
            → valid∈𝕎 i H (SUM! F G) (UNIV 1)
valid∈-SUM! i lti H F G vF vG w s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-UNIV s1 1 cc1 | #subs-UNIV s2 1 cc2
        | #subs-SUM!2 s1 F G ce1 | #subs-SUM!2 s2 F G ce2
  = h1 , h2
  where
  h1 : equalTypes i w (#UNIV 1) (#UNIV 1)
  h1 = eqTypesUniv w i 1 lti

  ha : ∀𝕎 w (λ w' _ → equalTypes 1 w' (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2)))
  ha w1 e1 = vf2
    where
    vf1 : equalInType i w1 (#UNIV 1) (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2))
    vf1 = ≡CTerm→equalInType
            (#subs-UNIV s1 1 cc1)
            (π₂ (vF w1 s1 s2 cc1 cc2 (coveredSUM!₁ {s1} {F} {G} ce1) (coveredSUM!₁ {s2} {F} {G} ce2) (≡subs-mon e1 es) (≡hyps-mon e1 eh)))

    vf2 : equalTypes 1 w1 (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2))
    vf2 = equalInType→equalTypes-aux i 1 lti w1
            (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1))
            (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2))
            vf1

  hb : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType 1 w' (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) a₁ a₂
                    → equalTypes
                        1 w'
                        (sub0 a₁ (#[0]subs s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                        (sub0 a₂ (#[0]subs s2 G (coveredSUM!₂ {s2} {F} {G} ce2))))
  hb w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (≣sym (sub0-#[0]subs a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
      (≣sym (sub0-#[0]subs a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
      hb1
    where
    vg1 : equalInType i w1 (#UNIV 1) (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                                     (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
    vg1 = ≡CTerm→equalInType
            (#subs-UNIV (s1 Data.List.∷ʳ a₁) 1 λ {x} ())
            (π₂ (vG w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂) (λ {x} ()) (λ {x} ())
                    (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1))
                    (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2))
                    (≡subs∷ʳ i w1 s1 s2 H F (coveredSUM!₁ {s1} {F} {G} ce1) a₁ a₂
                      (equalInType-uni-mon (<⇒≤ lti) a∈) (≡subs-mon e1 es))
                    (≡hyps∷ʳ i w1 s1 s2 H H F F (coveredSUM!₁ {s1} {F} {G} ce1) (coveredSUM!₁ {s2} {F} {G} ce2) a₁ a₂
                      (equalTypes-uni-mon (<⇒≤ lti) (ha w1 e1))
                      (≡hyps-mon e1 eh))))

    hb1 : equalTypes 1 w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
    hb1 = equalInType→equalTypes-aux i 1 lti w1
            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
            vg1

  h2 : equalInType i w (#UNIV 1)
                       (#SUM! (#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)) (#[0]subs s1 G (coveredSUM!₂ {s1} {F} {G} ce1)))
                       (#SUM! (#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2)) (#[0]subs s2 G (coveredSUM!₂ {s2} {F} {G} ce2)))
  h2 = equalTypes→equalInType-UNIV
         lti
         (eqTypesSUM!←
           {w} {1}
           {#subs s1 F (coveredSUM!₁ {s1} {F} {G} ce1)} {#[0]subs s1 G (coveredSUM!₂ {s1} {F} {G} ce1)}
           {#subs s2 F (coveredSUM!₁ {s2} {F} {G} ce2)} {#[0]subs s2 G (coveredSUM!₂ {s2} {F} {G} ce2)}
           ha hb)


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


valid∈-change-type : {i : Nat} {w : 𝕎·} {H : hypotheses} {A B t : BTerm}
                   → 1 <ℕ i
                   → coveredH H A
                   → valid≡ i w H A B (UNIV 1)
                   → valid∈ i w H t A
                   → valid∈ i w H t B
valid∈-change-type {i} {w} {H} {A} {B} {t} lti covHA h q s1 s2 cc1 cc2 ce1 ce2 es eh =
  equalTypes-uni-mon (<⇒≤ lti) h3 , q2
  where
  ca1 : covered s1 A
  ca1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {A} es covHA

  ca2 : covered s2 A
  ca2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {A} es covHA

  ceq1 : covered s1 (EQ A B (UNIV 1))
  ceq1 = →coveredEQ {s1} {A} {B} {UNIV 1} ca1 cc1 (covered-UNIV s1 1)

  ceq2 : covered s2 (EQ A B (UNIV 1))
  ceq2 = →coveredEQ {s2} {A} {B} {UNIV 1} ca2 cc2 (covered-UNIV s2 1)

  h1 : equalTypes i w (#subs s1 (EQ A B (UNIV 1)) ceq1) (#subs s2 (EQ A B (UNIV 1)) ceq2)
  h1 = π₁ (h s1 s2 ceq1 ceq2 (covered-AX s1) (covered-AX s2) es eh)

  h2 : equalTypes i w (#EQ (#subs s1 A ca1) (#subs s1 B cc1) (#UNIV 1)) (#EQ (#subs s2 A ca2) (#subs s2 B cc2) (#UNIV 1))
  h2 = ≡CTerm→eqTypes (CTerm≡ (≣trans (subs-EQ s1 A B (UNIV 1)) (cong₃ EQ refl refl (subs-UNIV s1 1))))
                      (CTerm≡ (≣trans (subs-EQ s2 A B (UNIV 1)) (cong₃ EQ refl refl (subs-UNIV s2 1))))
                      h1

  h3 : equalTypes 1 w (#subs s1 B cc1) (#subs s2 B cc2)
  h3 = equalInType→equalTypes-aux i 1 lti w (#subs s1 B cc1) (#subs s2 B cc2)
         (eqTypesEQ→ᵣ {w} {i} {#subs s1 A ca1} {#subs s1 B cc1} {#subs s2 A ca2} {#subs s2 B cc2} {#UNIV 1} {#UNIV 1} h2)

  z1 : equalInType i w (#subs s1 (EQ A B (UNIV 1)) ceq1) (#subs s1 AX (covered-AX s1)) (#subs s2 AX (covered-AX s2))
  z1 = π₂ (h s1 s2 ceq1 ceq2 (covered-AX s1) (covered-AX s2) es eh)

  z2 : equalInType i w (#EQ (#subs s1 A ca1) (#subs s1 B cc1) (#UNIV 1)) #AX #AX
  z2 = ≡→equalInType (CTerm≡ (≣trans (subs-EQ s1 A B (UNIV 1)) (cong₃ EQ refl refl (subs-UNIV s1 1))))
                     (#subs-AX s1 (covered-AX s1))
                     (#subs-AX s2 (covered-AX s2))
                     z1

  z3 : equalInType i w (#UNIV 1) (#subs s1 A ca1) (#subs s1 B cc1)
  z3 = equalInType-EQ→₁ z2

  z4 : equalTypes 1 w (#subs s1 A ca1) (#subs s1 B cc1)
  z4 = equalInType→equalTypes-aux i 1 lti w (#subs s1 A ca1) (#subs s1 B cc1) z3

  q1 : equalInType i w (#subs s1 A ca1) (#subs s1 t ce1) (#subs s2 t ce2)
  q1 = π₂ (q s1 s2 ca1 ca2 ce1 ce2 es eh)

  q2 : equalInType i w (#subs s1 B cc1) (#subs s1 t ce1) (#subs s2 t ce2)
  q2 = TSext-equalTypes-equalInType i w (#subs s1 A ca1) (#subs s1 B cc1)
         (#subs s1 t ce1) (#subs s2 t ce2) (equalTypes-uni-mon (<⇒≤ lti) z4) q1


valid∈N0-NAT : (i : Nat) (w : 𝕎·) (H : hypotheses)
             → valid∈ i w H N0 NAT!
valid∈N0-NAT i w H s1 s2 cc1 cc2 ce1 ce2 es eh
  rewrite #subs-NAT! s1 cc1 | #subs-NAT! s2 cc2 | #subs-N0 s1 ce1 | #subs-N0 s2 ce2
  = isTypeNAT! , NUM-equalInType-NAT! i w 0


SUC⇛! : {w : 𝕎·} {a : BTerm} {k : Nat}
      → a ⇛! NUM k at w
      → SUC a ⇛! NUM (Nat.suc k) at w
SUC⇛! {w} {a} {k} comp w1 e1 =
  lift (⇓NUM→SUC⇓NUM {a} {k} {w1} {w1} (lower (comp w1 e1)))


SUC∈NAT! : {i : Nat} {w : 𝕎·} {a b : CTerm}
        → equalInType i w #NAT! a b
        → equalInType i w #NAT! (#SUC a) (#SUC b)
SUC∈NAT! {i} {w} {a} {b} h =
  →equalInType-NAT! i w (#SUC a) (#SUC b) (Mod.∀𝕎-□Func M aw (equalInType-NAT!→ i w a b h))
  where
  aw : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' a b
                     → #⇛!sameℕ w' (#SUC a) (#SUC b))
  aw w1 e1 (k , c₁ , c₂) = Nat.suc k , SUC⇛! c₁ , SUC⇛! c₂


valid∈SUC-NAT : {i : Nat} {w : 𝕎·} {H : hypotheses} {t : BTerm}
              → valid∈ i w H t NAT!
              → valid∈ i w H (SUC t) NAT!
valid∈SUC-NAT {i} {w} {H} {t} h s1 s2 cc1 cc2 ce1 ce2 es eh =
  h1 , q1
  where
  h1 : equalTypes i w (#subs s1 NAT! cc1) (#subs s2 NAT! cc2)
  h1 = π₁ (h s1 s2 cc1 cc2 ce1 ce2 es eh)

  h2 : equalInType i w (#subs s1 NAT! cc1) (#subs s1 t ce1) (#subs s2 t ce2)
  h2 = π₂ (h s1 s2 cc1 cc2 ce1 ce2 es eh)

  h3 : equalInType i w #NAT! (#subs s1 t ce1) (#subs s2 t ce2)
  h3 = ≡→equalInType (#subs-NAT! s1 cc1) refl refl h2

  q2 : equalInType i w #NAT! (#SUC (#subs s1 t ce1)) (#SUC (#subs s2 t ce2))
  q2 = SUC∈NAT! h3

  q1 : equalInType i w (#subs s1 NAT! cc1) (#subs s1 (SUC t) ce1) (#subs s2 (SUC t) ce2)
  q1 = ≡→equalInType (≣sym (#subs-NAT! s1 cc1)) (≣sym (#subs-SUC s1 t ce1)) (≣sym (#subs-SUC s2 t ce2)) q2


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


-- finish converting G
valid∈NATREC : {i : Nat} {H : hypotheses} {G k z s : BTerm} (lti : 1 <ℕ i)
             → valid∈𝕎 i (H Data.List.∷ʳ mkHyp NAT!) G (UNIV 1)
             → valid∈𝕎 i H z (subn 0 N0 G)
             → valid∈𝕎 i H s (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) --⟦ G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑ ⟧ᵤ)
             → valid∈𝕎 i H k NAT!
             → valid∈𝕎 i H (NATREC k z s) (subn 0 k G)
valid∈NATREC {i} {H} {G} {k} {z} {s} lti hg hz hs hk w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cu1 : covered s1 (UNIV 1)
  cu1 = covered-UNIV s1 1

  cu2 : covered s2 (UNIV 1)
  cu2 = covered-UNIV s2 1

  cm1 : covered s1 N0
  cm1 = covered-NUM s1 0

  cm2 : covered s2 N0
  cm2 = covered-NUM s2 0

  cn1 : covered s1 NAT!
  cn1 = covered-NAT! s1

  cn2 : covered s2 NAT!
  cn2 = covered-NAT! s2

  ck1 : covered s1 k
  ck1 = coveredNATREC₁ {s1} {k} {z} {s} ce1

  ck2 : covered s2 k
  ck2 = coveredNATREC₁ {s2} {k} {z} {s} ce2

  cz1 : covered s1 z
  cz1 = coveredNATREC₂ {s1} {k} {z} {s} ce1

  cz2 : covered s2 z
  cz2 = coveredNATREC₂ {s2} {k} {z} {s} ce2

  cx1 : covered s1 s
  cx1 = coveredNATREC₃ {s1} {k} {z} {s} ce1

  cx2 : covered s2 s
  cx2 = coveredNATREC₃ {s2} {k} {z} {s} ce2

  cs1 : covered (s1 Data.List.∷ʳ #subs s1 k ck1) G
  cs1 = covered-subn→ (#subs s1 k ck1) k s1 G cc1

  cs2 : covered (s2 Data.List.∷ʳ #subs s2 k ck2) G
  cs2 = covered-subn→ (#subs s2 k ck2) k s2 G cc2

  cs1b : covered (s1 Data.List.∷ʳ #subs s1 N0 cm1) G
  cs1b = covered-subn→ (#subs s1 N0 cm1) k s1 G cc1

  cs1a : covered s1 (subn 0 N0 G)
  cs1a = →covered-subn (#subs s1 k ck1) N0 s1 G refl cs1

  cs2a : covered s2 (subn 0 N0 G)
  cs2a = →covered-subn (#subs s2 k ck2) N0 s2 G refl cs2

  cu1a : covered (s1 Data.List.∷ʳ (#subs s1 k ck1)) (UNIV 1)
  cu1a = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 k ck1)) 1

  cu2a : covered (s2 Data.List.∷ʳ (#subs s2 k ck2)) (UNIV 1)
  cu2a = covered-UNIV (s2 Data.List.∷ʳ (#subs s2 k ck2)) 1

  cu1b : covered (s1 Data.List.∷ʳ (#subs s1 N0 cm1)) (UNIV 1)
  cu1b = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 N0 cm1)) 1

  c0g1 : covered0 s1 G
  c0g1 = covered-subn→covered0 N0 s1 G cs1a

  c0g2 : covered0 s2 G
  c0g2 = covered-subn→covered0 N0 s2 G cs2a

  c0sg1 : covered0 s1 (subi 0 (SUC (VAR 0)) G)
  c0sg1 = →covered0-subi0 s1 G (SUC (VAR 0)) c0g1 (→covered0-SUC s1 (VAR 0) (→covered0-VAR0 s1))

  c0sg2 : covered0 s2 (subi 0 (SUC (VAR 0)) G)
  c0sg2 = →covered0-subi0 s2 G (SUC (VAR 0)) c0g2 (→covered0-SUC s2 (VAR 0) (→covered0-VAR0 s2))

  cp1 : covered s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp1 = →coveredPI {s1} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s1)
                   (→covered0FUN {s1} {G} {subi 0 (SUC (VAR 0)) G}
                     c0g1 c0sg1)

  cp2 : covered s2 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G)))
  cp2 = →coveredPI {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} (covered-NAT! s2)
                   (→covered0FUN {s2} {G} {subi 0 (SUC (VAR 0)) G}
                     c0g2 c0sg2)

  cp01 : covered0 s1 (FUN G (subi 0 (SUC (VAR 0)) G))
  cp01 = coveredPI₂ {s1} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} cp1

  cp02 : covered0 s2 (FUN G (subi 0 (SUC (VAR 0)) G))
  cp02 = coveredPI₂ {s2} {NAT!} {FUN G (subi 0 (SUC (VAR 0)) G)} cp2

  k∈ : equalInType i w (#subs s1 NAT! cn1) (#subs s1 k ck1) (#subs s2 k ck2)
  k∈ = π₂ (hk w s1 s2 cn1 cn2 ck1 ck2 es eh)

  k∈1 : equalInType i w #NAT! (#subs s1 k ck1) (#subs s2 k ck2)
  k∈1 = ≡→equalInType (#subs-NAT! s1 cn1) refl refl k∈

  es1 : ≡subs i w (s1 Data.List.∷ʳ #subs s1 k ck1) (s2 Data.List.∷ʳ #subs s2 k ck2) (H Data.List.∷ʳ mkHyp NAT!)
  es1 = ≡subs∷ʳ i w s1 s2 H NAT! cn1 (#subs s1 k ck1) (#subs s2 k ck2) k∈ es

  eh1 : ≡hyps i w (s1 Data.List.∷ʳ #subs s1 k ck1) (s2 Data.List.∷ʳ #subs s2 k ck2) (H Data.List.∷ʳ mkHyp NAT!) (H Data.List.∷ʳ mkHyp NAT!)
  eh1 = ≡hyps∷ʳ i w s1 s2 H H NAT! NAT! cn1 cn2 (#subs s1 k ck1) (#subs s2 k ck2)
                (≡CTerm→eqTypes (≣sym (#subs-NAT! s1 cn1)) (≣sym (#subs-NAT! s2 cn2)) isTypeNAT!) eh

  hg1 : equalInType i w (#subs (s1 Data.List.∷ʳ (#subs s1 k ck1)) (UNIV 1) cu1a)
                        (#subs (s1 Data.List.∷ʳ (#subs s1 k ck1)) G cs1)
                        (#subs (s2 Data.List.∷ʳ (#subs s2 k ck2)) G cs2)
  hg1 = π₂ (hg w (s1 Data.List.∷ʳ (#subs s1 k ck1)) (s2 Data.List.∷ʳ (#subs s2 k ck2)) cu1a cu2a cs1 cs2 es1 eh1)

  hg2 : equalInType i w (#UNIV 1) (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  hg2 = ≡→equalInType (#subs-UNIV (s1 Data.List.∷ʳ #subs s1 k ck1) 1 cu1a)
                       (CTerm≡ (subs∷ʳ≡ s1 k G ck1))
                       (CTerm≡ (subs∷ʳ≡ s2 k G ck2))
                       hg1

  hg3 : equalTypes 1 w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  hg3 = equalInType→equalTypes-aux i 1 lti w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2) hg2

  -- G[k] is a type
  c1 : equalTypes i w (#subs s1 (subn 0 k G) cc1) (#subs s2 (subn 0 k G) cc2)
  c1 = equalTypes-uni-mon (<⇒≤ lti) hg3

  aw0 : ∀𝕎 w (λ w1 e1 → (k    : BTerm)
                        (ck1  : covered s1 k)
                        (ck2  : covered s2 k)
                        (cc1  : covered s1 (subn 0 k G))
                        (cs1  : covered (s1 Data.List.∷ʳ #subs s1 k ck1) G)
                        (cu1a : covered (s1 Data.List.∷ʳ (#subs s1 k ck1)) (UNIV 1))
                        (n    : Nat)
                        (c₁   : #subs s1 k ck1 #⇛! #NUM n at w1)
                        (c₂   : #subs s2 k ck2 #⇛! #NUM n at w1)
                      → equalInType i w1 (#subs s1 (subn 0 k G) cc1)
                                    (#NATREC (#subs s1 k ck1) (#subs s1 z cz1) (#subs s1 s cx1))
                                    (#NATREC (#subs s2 k ck2) (#subs s2 z cz2) (#subs s2 s cx2)))
  aw0 w1 e1 k ck1 ck2 cc1 cs1 cu1a 0 c₁ c₂ =
    equalInType-#⇛ₚ-left-right-rev (NATREC-0⇛! c₁) (NATREC-0⇛! c₂) hz2
    where
    hz1 : equalInType i w1 (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 z cz1) (#subs s2 z cz2)
    hz1 = equalInType-mon (π₂ (hz w s1 s2 cs1a cs2a cz1 cz2 es eh)) w1 e1

    eqn1 : equalInType i w1 #NAT! #N0 (#subs s1 k ck1)
    eqn1 = →equalInType-NAT! i w1 #N0 (#subs s1 k ck1)
             (Mod.∀𝕎-□ M (λ w2 e2 → 0 , #⇛!-refl {w2} {#N0} , #⇛!-mon {#subs s1 k ck1} {#N0} e2 c₁))

    es2 : ≡subs i w1 (s1 Data.List.∷ʳ #subs s1 N0 cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!)
    es2 = ≡subs∷ʳ i w1 s1 s1 H NAT! cn1 (#subs s1 N0 cm1) (#subs s1 k ck1)
            (≡→equalInType (≣sym (#subs-NAT! s1 cn1)) (≣sym (#subs-N0 s1 cm1)) refl eqn1)
            (≡subs-refl i w1 s1 s2 H (≡subs-mon e1 es))

    eh2 : ≡hyps i w1 (s1 Data.List.∷ʳ #subs s1 N0 cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!) (H Data.List.∷ʳ mkHyp NAT!)
    eh2 = ≡hyps∷ʳ i w1 s1 s1 H H NAT! NAT! cn1 cn1 (#subs s1 N0 cm1) (#subs s1 k ck1)
            (≡CTerm→eqTypes (≣sym (#subs-NAT! s1 cn1)) (≣sym (#subs-NAT! s1 cn1)) isTypeNAT!)
            (≡hyps-refl i w1 s1 s2 H H (≡hyps-mon e1 eh))

    eqt1 : equalInType i w1 (#subs (s1 Data.List.∷ʳ #subs s1 N0 cm1) (UNIV 1) cu1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 N0 cm1) G cs1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 k ck1) G cs1)
    eqt1 = π₂ (hg w1 (s1 Data.List.∷ʳ #subs s1 N0 cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) cu1b cu1a cs1b cs1 es2 eh2)

    eqt2 : equalTypes 1 w1 (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 (subn 0 k G) cc1)
    eqt2 = equalInType→equalTypes-aux i 1 lti w1 (#subs s1 (subn 0 N0 G) cs1a) (#subs s1 (subn 0 k G) cc1)
             (≡→equalInType (#subs-UNIV (s1 Data.List.∷ʳ #subs s1 N0 cm1) 1 cu1b)
                            (CTerm≡ (subs∷ʳ≡ s1 N0 G cm1))
                            (CTerm≡ (subs∷ʳ≡ s1 k G ck1))
                            eqt1)

    hz2 : equalInType i w1 (#subs s1 (subn 0 k G) cc1) (#subs s1 z cz1) (#subs s2 z cz2)
    hz2 = TSext-equalTypes-equalInType i w1 _ _ _ _ (equalTypes-uni-mon (<⇒≤ lti) eqt2) hz1
  aw0 w1 e1 k ck1 ck2 cc1 cs1 cu1a (1+ n) c₁ c₂ =
    equalInType-#⇛ₚ-left-right-rev {i} {w1}
      (#NATREC-s⇛! {n} {#subs s1 k ck1} {#subs s1 z cz1} {#subs s1 s cx1} c₁)
      (#NATREC-s⇛! {n} {#subs s2 k ck2} {#subs s2 z cz2} {#subs s2 s cx2} c₂)
      hz2
    where
    hz1 : equalInType i w1 (#subs s1 (PI NAT! (FUN G (subi 0 (SUC (VAR 0)) G))) cp1) (#subs s1 s cx1) (#subs s2 s cx2)
    hz1 = equalInType-mon (π₂ (hs w s1 s2 cp1 cp2 cx1 cx2 es eh)) w1 e1

    hp1 : equalInType i w1 (#PI (#subs s1 NAT! cn1) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01))
                           (#subs s1 s cx1)
                           (#subs s2 s cx2)
    hp1 = ≡CTerm→equalInType (#subs-PI s1 NAT! (FUN G (subi 0 (SUC (VAR 0)) G)) cp1 cn1 cp01) hz1

    hp2 : equalInType i w1 (sub0 (#NUM n) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01))
                           (#APPLY (#subs s1 s cx1) (#NUM n)) (#APPLY (#subs s2 s cx2) (#NUM n))
    hp2 = π₂ (π₂ (equalInType-PI→ hp1)) w1 (⊑-refl· w1) (#NUM n) (#NUM n)
             (≡CTerm→equalInType (≣sym (#subs-NAT! s1 cn1)) (NUM-equalInType-NAT! i w1 n))

    cs1c : covered s1 (subn 0 (NUM n) G)
    cs1c = →covered-subn (#subs s1 k ck1) (NUM n) s1 G refl cs1

    cs1d : covered s1 (subn 0 (SUC (NUM n)) G)
    cs1d = →covered-subn (#subs s1 k ck1) (SUC (NUM n)) s1 G refl cs1

    cus1b : covered (s1 Data.List.∷ʳ (#subs s1 (SUC (NUM n)) cm1)) (UNIV 1)
    cus1b = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 (SUC (NUM n)) cm1)) 1

    css1b : covered (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) G
    css1b = covered-subn→ (#subs s1 (SUC (NUM n)) cm1) k s1 G cc1

    cus1c : covered (s1 Data.List.∷ʳ (#subs s1 (NUM n) cm1)) (UNIV 1)
    cus1c = covered-UNIV (s1 Data.List.∷ʳ (#subs s1 (NUM n) cm1)) 1

    css1c : covered (s1 Data.List.∷ʳ #subs s1 (NUM n) cm1) G
    css1c = covered-subn→ (#subs s1 (NUM n) cm1) k s1 G cc1

    esn0 : subn 0 (NUM n) (subsN 1 s1 (FUN G (subi 0 (SUC (VAR 0)) G)))
         ≣ FUN (subs s1 (subn 0 (NUM n) G)) (subs s1 (subn 0 (SUC (NUM n)) G))
    esn0 rewrite subsN-FUN 1 s1 G (subi 0 (SUC (VAR 0)) G) =
      ≡PI (≣trans (subn-subsN1 (#NUM n) s1 G)
                  (≣trans (cong (λ z → subs (s1 Data.List.∷ʳ z) G) (≣sym (#subs-NUM s1 n (covered-NUM s1 n))))
                          (subs∷ʳ≡ s1 (NUM n) G (covered-NUM s1 n))))
          (≣trans (cong (λ z → subn 1 (NUM n) z) (≣sym (subsN-suc-shiftUp 1 s1 (subi 0 (SUC (VAR 0)) G)))) --(cong (λ z → subn 1 (NUM n) z) {!!})
                  (≣trans (≣trans (≣trans (cong (λ z → subn 1 z (subsN 2 s1 (shiftUp 0 (subi 0 (SUC (VAR 0)) G)))) (≣sym (subsN-NUM 1 s1 n)))
                                          (≣trans (subn-subsN 1 (NUM n) s1 (shiftUp 0 (subi 0 (SUC (VAR 0)) G)))
                                                  (cong (subsN 1 s1)
                                                        (≣trans (≣sym (shiftUp-subn 0 0 (NUM n) (subi 0 (SUC (VAR 0)) G) ≤-refl))
                                                                (cong (shiftUp 0) (subn-subi 0 (NUM n) (SUC (VAR 0)) G))))))
                                  (subsN-suc-shiftUp 0 s1 (subn 0 (SUC (NUM n)) G)))
                          (cong (shiftUp 0) (subsN0 s1 (subn 0 (SUC (NUM n)) G)))))

    esn : sub0 (#NUM n) (#[0]subs s1 (FUN G (subi 0 (SUC (VAR 0)) G)) cp01)
        ≣ #FUN (#subs s1 (subn 0 (NUM n) G) cs1c) (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d)
    esn = CTerm≡ (≣trans (sub≡subn (NUM n) (subsN 1 s1 (FUN G (subi 0 (SUC (VAR 0)) G)))) esn0)

    hp3 : equalInType i w1 (#FUN (#subs s1 (subn 0 (NUM n) G) cs1c) (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d))
                           (#APPLY (#subs s1 s cx1) (#NUM n)) (#APPLY (#subs s2 s cx2) (#NUM n))
    hp3 = ≡CTerm→equalInType esn hp2

    nc1 : #subs s1 (NUM n) cm1 #⇛! #NUM n at w1
    nc1 = ≣subst (λ z → z #⇛! #NUM n at w1) (≣sym (#subs-NUM s1 n cm1)) (#⇛!-refl {w1} {#NUM n})

    nc2 : #subs s2 (NUM n) cm2 #⇛! #NUM n at w1
    nc2 = ≣subst (λ z → z #⇛! #NUM n at w1) (≣sym (#subs-NUM s2 n cm2)) (#⇛!-refl {w1} {#NUM n})

    ind0 : equalInType i w1 (#subs s1 (subn 0 (NUM n) G) cs1c)
                            (#NATREC (#subs s1 (NUM n) cm1) (#subs s1 z cz1) (#subs s1 s cx1))
                            (#NATREC (#subs s2 (NUM n) cm2) (#subs s2 z cz2) (#subs s2 s cx2))
    ind0 = aw0 w1 e1 (NUM n) cm1 cm2 cs1c css1c cus1c n nc1 nc2

    ind : equalInType i w1 (#subs s1 (subn 0 (NUM n) G) cs1c)
                           (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1))
                           (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2))
    ind = subst₂ (λ a b → equalInType i w1 (#subs s1 (subn 0 (NUM n) G) cs1c)
                                      (#NATREC a (#subs s1 z cz1) (#subs s1 s cx1))
                                      (#NATREC b (#subs s2 z cz2) (#subs s2 s cx2)))
            (#subs-NUM s1 n cm1) (#subs-NUM s2 n cm2) ind0

    hp4 : equalInType i w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d)
                           (#APPLY2 (#subs s1 s cx1) (#NUM n) (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1)))
                           (#APPLY2 (#subs s2 s cx2) (#NUM n) (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2)))
    hp4 = equalInType-FUN→ hp3 w1 (⊑-refl· w1)
            (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1))
            (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2))
            ind

    eqn1 : equalInType i w1 #NAT! (#SUC (#NUM n)) (#subs s1 k ck1)
    eqn1 = →equalInType-NAT! i w1 (#SUC (#NUM n)) (#subs s1 k ck1)
             (Mod.∀𝕎-□ M (λ w2 e2 → (1+ n) , (λ w1 e1 → lift (1 , refl)) ,
                                    #⇛!-mon {#subs s1 k ck1} {#NUM (1+ n)} e2 c₁))

    es2 : ≡subs i w1 (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!)
    es2 = ≡subs∷ʳ i w1 s1 s1 H NAT! cn1 (#subs s1 (SUC (NUM n)) cm1) (#subs s1 k ck1)
            (≡→equalInType (≣sym (#subs-NAT! s1 cn1)) (≣sym (≣trans (#subs-SUC s1 (NUM n) cm1) (cong #SUC (#subs-NUM s1 n cm1)))) refl eqn1)
            (≡subs-refl i w1 s1 s2 H (≡subs-mon e1 es))

    eh2 : ≡hyps i w1 (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) (H Data.List.∷ʳ mkHyp NAT!) (H Data.List.∷ʳ mkHyp NAT!)
    eh2 = ≡hyps∷ʳ i w1 s1 s1 H H NAT! NAT! cn1 cn1 (#subs s1 (SUC (NUM n)) cm1) (#subs s1 k ck1)
            (≡CTerm→eqTypes (≣sym (#subs-NAT! s1 cn1)) (≣sym (#subs-NAT! s1 cn1)) isTypeNAT!)
            (≡hyps-refl i w1 s1 s2 H H (≡hyps-mon e1 eh))

    eqt1 : equalInType i w1 (#subs (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (UNIV 1) cus1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) G css1b)
                            (#subs (s1 Data.List.∷ʳ #subs s1 k ck1) G cs1)
    eqt1 = π₂ (hg w1 (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) (s1 Data.List.∷ʳ #subs s1 k ck1) cus1b cu1a css1b cs1 es2 eh2)

    eqt2 : equalTypes 1 w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d) (#subs s1 (subn 0 k G) cc1)
    eqt2 = equalInType→equalTypes-aux i 1 lti w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d) (#subs s1 (subn 0 k G) cc1)
             (≡→equalInType (#subs-UNIV (s1 Data.List.∷ʳ #subs s1 (SUC (NUM n)) cm1) 1 cus1b)
                            (CTerm≡ (subs∷ʳ≡ s1 (SUC (NUM n)) G cm1))
                            (CTerm≡ (subs∷ʳ≡ s1 k G ck1))
                            eqt1)

    eqt : equalTypes i w1 (#subs s1 (subn 0 (SUC (NUM n)) G) cs1d) (#subs s1 (subn 0 k G) cc1)
    eqt = equalTypes-uni-mon (<⇒≤ lti) eqt2

    hz2 : equalInType i w1 (#subs s1 (subn 0 k G) cc1)
                           (#APPLY2 (#subs s1 s cx1) (#NUM n) (#NATREC (#NUM n) (#subs s1 z cz1) (#subs s1 s cx1)))
                           (#APPLY2 (#subs s2 s cx2) (#NUM n) (#NATREC (#NUM n) (#subs s2 z cz2) (#subs s2 s cx2)))
    hz2 = TSext-equalTypes-equalInType i w1 _ _ _ _ eqt hp4

  aw1 : ∀𝕎 w (λ w' e' → #⇛!sameℕ w' (#subs s1 k ck1) (#subs s2 k ck2)
                      → equalInType i w' (#subs s1 (subn 0 k G) cc1)
                                    (#NATREC (#subs s1 k ck1) (#subs s1 z cz1) (#subs s1 s cx1))
                                    (#NATREC (#subs s2 k ck2) (#subs s2 z cz2) (#subs s2 s cx2)))
  aw1 w1 e1 (n , c₁ , c₂) = aw0 w1 e1 k ck1 ck2 cc1 cs1 cu1a n c₁ c₂

  c2a : equalInType i w (#subs s1 (subn 0 k G) cc1)
                    (#NATREC (#subs s1 k ck1) (#subs s1 z cz1) (#subs s1 s cx1))
                    (#NATREC (#subs s2 k ck2) (#subs s2 z cz2) (#subs s2 s cx2))
  c2a = equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT!→ i w (#subs s1 k ck1) (#subs s2 k ck2) k∈1))

  -- natrec ∈ G[k]
  c2 : equalInType i w (#subs s1 (subn 0 k G) cc1) (#subs s1 (NATREC k z s) ce1) (#subs s2 (NATREC k z s) ce2)
  c2 = ≡→equalInType refl (≣sym (#subs-NATREC s1 k z s ce1 ck1 cz1 cx1)) (≣sym (#subs-NATREC s2 k z s ce2 ck2 cz2 cx2)) c2a


valid∈VAR : {n : Nat} {Γ : Con Term n} {σ : Term n} {x : Fin n}
          → x ∷ σ ∈ Γ
          → (i : Nat) (w : 𝕎·) → valid∈ i w ⟦ Γ ⟧Γ (VAR (toℕ x)) ⟦ σ ⟧ᵤ
valid∈VAR {.(1+ _)} {.(_ ∙ _)} {.(wk1 _)} {.Fin.zero} here i w s1 s2 cc1 cc2 ce1 ce2 es eh =
  {!!}
valid∈VAR {.(1+ _)} {.(_ ∙ _)} {.(wk1 _)} {.(Fin.suc _)} (there j) i w = {!!}


valid∈APPLY : {i : Nat} {H : hypotheses} {F G g a : BTerm}
            → coveredH H F
            → valid∈𝕎 i H a F
            → valid∈𝕎 i H g (PI F G)
            → valid∈𝕎 i H (APPLY g a) (subn 0 a G)
valid∈APPLY {i} {H} {F} {G} {g} {a} covF ha hg w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cF1 : covered s1 F
  cF1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {F} es covF

  cF2 : covered s2 F
  cF2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {F} es covF

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 a s1 G cc1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 a s2 G cc2

  cp1 : covered s1 (PI F G)
  cp1 = →coveredPI {s1} {F} {G} cF1 cG1

  cp2 : covered s2 (PI F G)
  cp2 = →coveredPI {s2} {F} {G} cF2 cG2

  ca1 : covered s1 a
  ca1 = coveredAPPLY₂ {s1} {g} {a} ce1

  ca2 : covered s2 a
  ca2 = coveredAPPLY₂ {s2} {g} {a} ce2

  cg1 : covered s1 g
  cg1 = coveredAPPLY₁ {s1} {g} {a} ce1

  cg2 : covered s2 g
  cg2 = coveredAPPLY₁ {s2} {g} {a} ce2

  hg1 : equalTypes i w (#subs s1 (PI F G) cp1) (#subs s2 (PI F G) cp2)
  hg1 = π₁ (hg w s1 s2 cp1 cp2 cg1 cg2 es eh)

  hg2 : equalTypes i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#PI (#subs s2 F cF2) (#[0]subs s2 G cG2))
  hg2 = ≡CTerm→eqTypes (#subs-PI s1 F G cp1 cF1 cG1) (#subs-PI s2 F G cp2 cF2 cG2) hg1

  ha1 : equalInType i w (#subs s1 F cF1) (#subs s1 a ca1) (#subs s2 a ca2)
  ha1 = π₂ (ha w s1 s2 cF1 cF2 ca1 ca2 es eh)

  hg3 : equalTypes i w (sub0 (#subs s1 a ca1) (#[0]subs s1 G cG1)) (sub0 (#subs s2 a ca2) (#[0]subs s2 G cG2))
  hg3 = equalTypesPI→ᵣ {w} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
                       hg2 (#subs s1 a ca1) (#subs s2 a ca2) ha1

  ehg3₁ : sub0 (#subs s1 a ca1) (#[0]subs s1 G cG1) ≣ #subs s1 (subn 0 a G) cc1
  ehg3₁ = ≣trans (sub0-#[0]subs (#subs s1 a ca1) s1 G cG1) (CTerm≡ (subs∷ʳ≡ s1 a G ca1))

  ehg3₂ : sub0 (#subs s2 a ca2) (#[0]subs s2 G cG2) ≣ #subs s2 (subn 0 a G) cc2
  ehg3₂ = ≣trans (sub0-#[0]subs (#subs s2 a ca2) s2 G cG2) (CTerm≡ (subs∷ʳ≡ s2 a G ca2))

  c1 : equalTypes i w (#subs s1 (subn 0 a G) cc1) (#subs s2 (subn 0 a G) cc2)
  c1 = ≡CTerm→eqTypes ehg3₁ ehg3₂ hg3

  hgg1 : equalInType i w (#subs s1 (PI F G) cp1) (#subs s1 g cg1) (#subs s2 g cg2)
  hgg1 = π₂ (hg w s1 s2 cp1 cp2 cg1 cg2 es eh)

  hgg2 : equalInType i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 g cg1) (#subs s2 g cg2)
  hgg2 = ≡CTerm→equalInType (#subs-PI s1 F G cp1 cF1 cG1) hgg1

  hgg3 : equalInType i w (sub0 (#subs s1 a ca1) (#[0]subs s1 G cG1))
                         (#APPLY (#subs s1 g cg1) (#subs s1 a ca1))
                         (#APPLY (#subs s2 g cg2) (#subs s2 a ca2))
  hgg3 = π₂ (π₂ (equalInType-PI→ {i} {w} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s1 g cg1} {#subs s2 g cg2} hgg2))
                                 w (⊑-refl· w) (#subs s1 a ca1) (#subs s2 a ca2) ha1

  c2 : equalInType i w (#subs s1 (subn 0 a G) cc1) (#subs s1 (APPLY g a) ce1) (#subs s2 (APPLY g a) ce2)
  c2 = ≡→equalInType ehg3₁ (≣sym (#subs-APPLY s1 g a ce1 cg1 ca1)) (≣sym (#subs-APPLY s2 g a ce2 cg2 ca2)) hgg3


#APPLY-LAMBDA⇛! : (w : 𝕎·) (t : CTerm0) (a : CTerm)
                → #APPLY (#LAMBDA t) a #⇛! sub0 a t at w
#APPLY-LAMBDA⇛! w t a w1 e1 = lift (1 , refl)


valid∈LAMBDA : {i : Nat} {H : hypotheses} {F G t : BTerm} (lti : 1 <ℕ i)
             → valid∈𝕎 i H F (UNIV 1)
             → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) t G
             → valid∈𝕎 i H (LAMBDA t) (PI F G)
valid∈LAMBDA {i} {H} {F} {G} {t} lti hf hg w s1 s2 cc1 cc2 ce1 ce2 es eh = c1 , c2
  where
  cF1 : covered s1 F
  cF1 = coveredPI₁ {s1} {F} {G} cc1

  cF2 : covered s2 F
  cF2 = coveredPI₁ {s2} {F} {G} cc2

  cG1 : covered0 s1 G
  cG1 = coveredPI₂ {s1} {F} {G} cc1

  cG2 : covered0 s2 G
  cG2 = coveredPI₂ {s2} {F} {G} cc2

  clt1 : covered0 s1 t
  clt1 = coveredLAMBDA {s1} {t} ce1

  clt2 : covered0 s2 t
  clt2 = coveredLAMBDA {s2} {t} ce2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  hf1 : equalInType i w (#subs s1 (UNIV 1) cu1a) (#subs s1 F cF1) (#subs s2 F cF2)
  hf1 = π₂ (hf w s1 s2 cu1a cu2a cF1 cF2 es eh)

  hf2 : equalInType i w (#UNIV 1) (#subs s1 F cF1) (#subs s2 F cF2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 1 cu1a) hf1

  hf3 : equalTypes 1 w (#subs s1 F cF1) (#subs s2 F cF2)
  hf3 = equalInType→equalTypes-aux i 1 lti w (#subs s1 F cF1) (#subs s2 F cF2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni 1) hf3 w1 e1)

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (≣sym (sub0-#[0]subs a₁ s1 G cG1))
      (≣sym (sub0-#[0]subs a₂ s2 G cG2))
      c1Ga
    where
    c1Ga : equalTypes i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = π₁ (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (→covered∷ʳ a₁ s1 t clt1) (→covered∷ʳ a₂ s2 t clt2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

  c1a : equalTypes i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#PI (#subs s2 F cF2) (#[0]subs s2 G cG2))
  c1a = eqTypesPI← {w} {i} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#subs s2 F cF2} {#[0]subs s2 G cG2}
                   c1F c1G

  c1 : equalTypes i w (#subs s1 (PI F G) cc1) (#subs s2 (PI F G) cc2)
  c1 = ≡CTerm→eqTypes (≣sym (#subs-PI s1 F G cc1 cF1 cG1)) (≣sym (#subs-PI s2 F G cc2 cF2 cG2)) c1a

  c2G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalInType i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s1 t ce1)) (sub0 a₂ (#[0]subs s2 t ce2)))
  c2G w1 e1 a₁ a₂ a∈ =
    ≡→equalInType
      (≣sym (sub0-#[0]subs a₁ s1 G cG1))
      (≣sym (sub0-#[0]subs a₁ s1 t ce1))
      (≣sym (sub0-#[0]subs a₂ s2 t ce2))
      c2Ga
    where
    c2Ga : equalInType i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s1 Data.List.∷ʳ a₁) t (→covered∷ʳ a₁ s1 t ce1))
                            (#subs (s2 Data.List.∷ʳ a₂) t (→covered∷ʳ a₂ s2 t ce2))
    c2Ga = π₂ (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (→covered∷ʳ a₁ s1 t clt1) (→covered∷ʳ a₂ s2 t clt2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

  c2b : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalInType i w' (sub0 a₁ (#[0]subs s1 G cG1))
                                        (#APPLY (#LAMBDA (#[0]subs s1 t ce1)) a₁)
                                        (#APPLY (#LAMBDA (#[0]subs s2 t ce2)) a₂))
  c2b w1 e1 a₁ a₂ a∈ =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1}
      {sub0 a₁ (#[0]subs s1 G cG1)}
      {#APPLY (#LAMBDA (#[0]subs s1 t ce1)) a₁} {sub0 a₁ (#[0]subs s1 t ce1)}
      {#APPLY (#LAMBDA (#[0]subs s2 t ce2)) a₂} {sub0 a₂ (#[0]subs s2 t ce2)}
      (#APPLY-LAMBDA⇛! w1 (#[0]subs s1 t ce1) a₁)
      (#APPLY-LAMBDA⇛! w1 (#[0]subs s2 t ce2) a₂)
      (c2G w1 e1 a₁ a₂ a∈)

  c2a : equalInType i w (#PI (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#LAMBDA (#[0]subs s1 t ce1)) (#LAMBDA (#[0]subs s2 t ce2))
  c2a = equalInType-PI {i} {w} {#subs s1 F cF1} {#[0]subs s1 G cG1} {#LAMBDA (#[0]subs s1 t ce1)} {#LAMBDA (#[0]subs s2 t ce2)}
                       (λ w1 e1 → TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
                       (λ w1 e1 a₁ a₂ a∈ →
                         TEQtrans-equalTypes i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2)) (sub0 a₂ (#[0]subs s1 G cG1))
                                             (c1G w1 e1 a₁ a₁ (equalInType-refl a∈))
                                             (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
                                                                (c1G w1 e1 a₂ a₁ (equalInType-sym a∈))))
                       c2b

  c2 : equalInType i w (#subs s1 (PI F G) cc1) (#subs s1 (LAMBDA t) ce1) (#subs s2 (LAMBDA t) ce2)
  c2 = ≡→equalInType (≣sym (#subs-PI s1 F G cc1 cF1 cG1))
                     (≣sym (#subs-LAMBDA s1 t ce1 ce1))
                     (≣sym (#subs-LAMBDA s2 t ce2 ce2))
                     c2a


valid∈FST : {i : Nat} {H : hypotheses} {F G t : BTerm} (lti : 1 <ℕ i)
          → coveredH (H Data.List.∷ʳ mkHyp F) G
          → valid∈𝕎 i H F (UNIV 1)
          → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV 1) -- this is not used
          → valid∈𝕎 i H t (SUM! F G)
          → valid∈𝕎 i H (FST t) F
valid∈FST {i} {H} {F} {G} {t} lti covH hf hg hs w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cG1 : covered0 s1 G
  cG1 = ≡subs→covered0ₗ {i} {w} {s1} {s2} {H} {mkHyp F} {G} es covH

  cG2 : covered0 s2 G
  cG2 = ≡subs→covered0ᵣ {i} {w} {s1} {s2} {H} {mkHyp F} {G} es covH

  clt1 : covered s1 t
  clt1 = coveredFST {s1} {t} ce1

  clt2 : covered s2 t
  clt2 = coveredFST {s2} {t} ce2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  cS1 : covered s1 (SUM! F G)
  cS1 = →coveredSUM! {s1} {F} {G} cc1 cG1

  cS2 : covered s2 (SUM! F G)
  cS2 = →coveredSUM! {s2} {F} {G} cc2 cG2

  hf1 : equalInType i w (#subs s1 (UNIV 1) cu1a) (#subs s1 F cc1) (#subs s2 F cc2)
  hf1 = π₂ (hf w s1 s2 cu1a cu2a cc1 cc2 es eh)

  hf2 : equalInType i w (#UNIV 1) (#subs s1 F cc1) (#subs s2 F cc2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 1 cu1a) hf1

  hf3 : equalTypes 1 w (#subs s1 F cc1) (#subs s2 F cc2)
  hf3 = equalInType→equalTypes-aux i 1 lti w (#subs s1 F cc1) (#subs s2 F cc2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cc1) (#subs s2 F cc2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni 1) hf3 w1 e1)

  c1 : equalTypes i w (#subs s1 F cc1) (#subs s2 F cc2)
  c1 = c1F w (⊑-refl· w)

  hs1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s2 t clt2)
  hs1 = π₂ (hs w s1 s2 cS1 cS2 clt1 clt2 es eh)

  hs2 : equalInType i w (#SUM! (#subs s1 F cc1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s2 t clt2)
  hs2 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cc1 cG1) hs1

  aw1 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cc1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 t clt2)
                      → equalInType i w' (#subs s1 F cc1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2)))
  aw1 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 F cc1} {#FST (#subs s1 t clt1)} {a₁} {#FST (#subs s2 t clt2)} {a₂}
      (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-FST-PAIR (#subs s2 t clt2) a₂ b₂ w1 c₂)
      a∈

  c2a : equalInType i w (#subs s1 F cc1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2))
  c2a = equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-SUM!→ hs2))

  c2 : equalInType i w (#subs s1 F cc1) (#subs s1 (FST t) ce1) (#subs s2 (FST t) ce2)
  c2 = ≡→equalInType refl
                     (≣sym (#subs-FST s1 t ce1 clt1))
                     (≣sym (#subs-FST s2 t ce2 clt2))
                     c2a


valid∈PAIR : {i : Nat} {H : hypotheses} {F G t u : BTerm} (lti : 1 <ℕ i)
           → valid∈𝕎 i H F (UNIV 1)
           → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV 1)
           → valid∈𝕎 i H t F
           → valid∈𝕎 i H u (subn 0 t G)
           → valid∈𝕎 i H (PAIR t u) (SUM! F G)
valid∈PAIR {i} {H} {F} {G} {t} {u} lti hf hg ht hu w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cF1 : covered s1 F
  cF1 = coveredSUM!₁ {s1} {F} {G} cc1

  cF2 : covered s2 F
  cF2 = coveredSUM!₁ {s2} {F} {G} cc2

  cG1 : covered0 s1 G
  cG1 = coveredSUM!₂ {s1} {F} {G} cc1

  cG2 : covered0 s2 G
  cG2 = coveredSUM!₂ {s2} {F} {G} cc2

  ctx1 : covered s1 t
  ctx1 = coveredPAIR₁ {s1} {t} {u} ce1

  ctx2 : covered s2 t
  ctx2 = coveredPAIR₁ {s2} {t} {u} ce2

  cux1 : covered s1 u
  cux1 = coveredPAIR₂ {s1} {t} {u} ce1

  cux2 : covered s2 u
  cux2 = coveredPAIR₂ {s2} {t} {u} ce2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  cu1b : covered0 s1 (UNIV 1)
  cu1b = covered0-UNIV s1 1

  cu2b : covered0 s2 (UNIV 1)
  cu2b = covered0-UNIV s2 1

  csg1 : covered s1 (subn 0 t G)
  csg1 = covered-subn s1 t G ctx1 cG1

  csg2 : covered s2 (subn 0 t G)
  csg2 = covered-subn s2 t G ctx2 cG2

  hf1 : equalInType i w (#subs s1 (UNIV 1) cu1a) (#subs s1 F cF1) (#subs s2 F cF2)
  hf1 = π₂ (hf w s1 s2 cu1a cu2a cF1 cF2 es eh)

  hf2 : equalInType i w (#UNIV 1) (#subs s1 F cF1) (#subs s2 F cF2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 1 cu1a) hf1

  hf3 : equalTypes 1 w (#subs s1 F cF1) (#subs s2 F cF2)
  hf3 = equalInType→equalTypes-aux i 1 lti w (#subs s1 F cF1) (#subs s2 F cF2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni 1) hf3 w1 e1)

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (≣sym (sub0-#[0]subs a₁ s1 G cG1))
      (≣sym (sub0-#[0]subs a₂ s2 G cG2))
      c1Ga
    where
    c1Gc : equalInType i w1 (#subs (s1 Data.List.∷ʳ a₁) (UNIV 1) (→covered∷ʳ a₁ s1 (UNIV 1) cu1b))
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = π₂ (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV 1) cu1b) (→covered∷ʳ a₂ s2 (UNIV 1) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV 1)
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 Data.List.∷ʳ a₁) 1 (→covered∷ʳ a₁ s1 (UNIV 1) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i 1 lti w1
                                          (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
                                          c1Gb)

  c1a : equalTypes i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#SUM! (#subs s2 F cF2) (#[0]subs s2 G cG2))
  c1a = eqTypesSUM!← c1F c1G

  c1 : equalTypes i w (#subs s1 (SUM! F G) cc1) (#subs s2 (SUM! F G) cc2)
  c1 = ≡CTerm→eqTypes (≣sym (#subs-SUM! s1 F G cc1 cF1 cG1)) (≣sym (#subs-SUM! s2 F G cc2 cF2 cG2)) c1a

  hu1 : equalInType i w (#subs s1 (subn 0 t G) csg1) (#subs s1 u cux1) (#subs s2 u cux2)
  hu1 = π₂ (hu w s1 s2 csg1 csg2 cux1 cux2 es eh)

  esn0 : sub0 (#subs s1 t ctx1) (#[0]subs s1 G cG1) ≣ #subs s1 (subn 0 t G) csg1
  esn0 = ≣trans (sub0-#[0]subs (#subs s1 t ctx1) s1 G cG1)
                (CTerm≡ (subs∷ʳ≡ s1 t G ctx1))

  c2b : ∀𝕎 w (λ w' _ → SUMeq! (equalInType i w' (#subs s1 F cF1)) (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1))) w'
                              (#PAIR (#subs s1 t ctx1) (#subs s1 u cux1))
                              (#PAIR (#subs s2 t ctx2) (#subs s2 u cux2)))
  c2b w1 e1 =
    #subs s1 t ctx1 , #subs s2 t ctx2 , #subs s1 u cux1 , #subs s2 u cux2 ,
    equalInType-mon (π₂ (ht w s1 s2 cF1 cF2 ctx1 ctx2 es eh)) w1 e1 ,
    #⇛!-refl {w1} {#PAIR (#subs s1 t ctx1) (#subs s1 u cux1)} ,
    #⇛!-refl {w1} {#PAIR (#subs s2 t ctx2) (#subs s2 u cux2)} ,
    equalInType-mon (≡CTerm→equalInType (≣sym esn0) hu1) w1 e1

  c2a : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1))
                        (#PAIR (#subs s1 t ctx1) (#subs s1 u cux1))
                        (#PAIR (#subs s2 t ctx2) (#subs s2 u cux2))
  c2a = equalInType-SUM!
          {i} {w} {#subs s1 F cF1} {#[0]subs s1 G cG1}
          {#PAIR (#subs s1 t ctx1) (#subs s1 u cux1)}
          {#PAIR (#subs s2 t ctx2) (#subs s2 u cux2)}
          (λ w1 e1 → TEQrefl-equalTypes i w1 (#subs s1 F cF1) (#subs s2 F cF2) (c1F w1 e1))
          (λ w1 e1 a₁ a₂ a∈ →
                         TEQtrans-equalTypes i w1 (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2)) (sub0 a₂ (#[0]subs s1 G cG1))
                                             (c1G w1 e1 a₁ a₁ (equalInType-refl a∈))
                                             (TEQsym-equalTypes i w1 (sub0 a₂ (#[0]subs s1 G cG1)) (sub0 a₁ (#[0]subs s2 G cG2))
                                                                (c1G w1 e1 a₂ a₁ (equalInType-sym a∈))))
          (Mod.∀𝕎-□ M c2b)

  c2 : equalInType i w (#subs s1 (SUM! F G) cc1) (#subs s1 (PAIR t u) ce1) (#subs s2 (PAIR t u) ce2)
  c2 = ≡→equalInType (≣sym (#subs-SUM! s1 F G cc1 cF1 cG1))
                     (≣sym (#subs-PAIR s1 t u ce1 ctx1 cux1))
                     (≣sym (#subs-PAIR s2 t u ce2 ctx2 cux2))
                     c2a


valid∈SND : {i : Nat} {H : hypotheses} {F G t : BTerm} (lti : 1 <ℕ i)
          → coveredH H F
          → valid∈𝕎 i H F (UNIV 1)
          → valid∈𝕎 i (H Data.List.∷ʳ mkHyp F) G (UNIV 1) -- used?
          → valid∈𝕎 i H t (SUM! F G)
          → valid∈𝕎 i H (SND t) (subn 0 (FST t) G)
valid∈SND {i} {H} {F} {G} {t} lti covH hf hg hs w s1 s2 cc1 cc2 ce1 ce2 es eh =
  c1 , c2
  where
  cF1 : covered s1 F
  cF1 = ≡subs→coveredₗ {i} {w} {s1} {s2} {H} {F} es covH

  cF2 : covered s2 F
  cF2 = ≡subs→coveredᵣ {i} {w} {s1} {s2} {H} {F} es covH

  cG1 : covered0 s1 G
  cG1 = covered-subn→covered0 (FST t) s1 G cc1

  cG2 : covered0 s2 G
  cG2 = covered-subn→covered0 (FST t) s2 G cc2

  clt1 : covered s1 t
  clt1 = coveredSND {s1} {t} ce1

  clt2 : covered s2 t
  clt2 = coveredSND {s2} {t} ce2

  cft1 : covered s1 (FST t)
  cft1 = →coveredFST {s1} {t} clt1

  cft2 : covered s2 (FST t)
  cft2 = →coveredFST {s2} {t} clt2

  cu1a : covered s1 (UNIV 1)
  cu1a = covered-UNIV s1 1

  cu2a : covered s2 (UNIV 1)
  cu2a = covered-UNIV s2 1

  cu1b : covered0 s1 (UNIV 1)
  cu1b = covered0-UNIV s1 1

  cu2b : covered0 s2 (UNIV 1)
  cu2b = covered0-UNIV s2 1

  cS1 : covered s1 (SUM! F G)
  cS1 = →coveredSUM! {s1} {F} {G} cF1 cG1

  cS2 : covered s2 (SUM! F G)
  cS2 = →coveredSUM! {s2} {F} {G} cF2 cG2

  hf1 : equalInType i w (#subs s1 (UNIV 1) cu1a) (#subs s1 F cF1) (#subs s2 F cF2)
  hf1 = π₂ (hf w s1 s2 cu1a cu2a cF1 cF2 es eh)

  hf2 : equalInType i w (#UNIV 1) (#subs s1 F cF1) (#subs s2 F cF2)
  hf2 = ≡CTerm→equalInType (#subs-UNIV s1 1 cu1a) hf1

  hf3 : equalTypes 1 w (#subs s1 F cF1) (#subs s2 F cF2)
  hf3 = equalInType→equalTypes-aux i 1 lti w (#subs s1 F cF1) (#subs s2 F cF2) hf2

  c1F : ∀𝕎 w (λ w' _ → equalTypes i w' (#subs s1 F cF1) (#subs s2 F cF2))
  c1F w1 e1 = equalTypes-uni-mon (<⇒≤ lti) (eqTypes-mon (uni 1) hf3 w1 e1)

  c1G : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#subs s1 F cF1) a₁ a₂
                     → equalTypes i w' (sub0 a₁ (#[0]subs s1 G cG1)) (sub0 a₂ (#[0]subs s2 G cG2)))
  c1G w1 e1 a₁ a₂ a∈ =
    ≡CTerm→eqTypes
      (≣sym (sub0-#[0]subs a₁ s1 G cG1))
      (≣sym (sub0-#[0]subs a₂ s2 G cG2))
      c1Ga
    where
    c1Gc : equalInType i w1 (#subs (s1 Data.List.∷ʳ a₁) (UNIV 1) (→covered∷ʳ a₁ s1 (UNIV 1) cu1b))
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gc = π₂ (hg w1 (s1 Data.List.∷ʳ a₁) (s2 Data.List.∷ʳ a₂)
                  (→covered∷ʳ a₁ s1 (UNIV 1) cu1b) (→covered∷ʳ a₂ s2 (UNIV 1) cu2b)
                  (→covered∷ʳ a₁ s1 G cG1) (→covered∷ʳ a₂ s2 G cG2)
                  (≡subs∷ʳ i w1 s1 s2 H F cF1 a₁ a₂ a∈ (≡subs-mon e1 es))
                  (≡hyps∷ʳ i w1 s1 s2 H H F F cF1 cF2 a₁ a₂ (c1F w1 e1) (≡hyps-mon e1 eh)))

    c1Gb : equalInType i w1 (#UNIV 1)
                            (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                            (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Gb = ≡CTerm→equalInType (#subs-UNIV (s1 Data.List.∷ʳ a₁) 1 (→covered∷ʳ a₁ s1 (UNIV 1) cu1b)) c1Gc

    c1Ga : equalTypes i w1 (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                           (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
    c1Ga = equalTypes-uni-mon (<⇒≤ lti) (equalInType→equalTypes-aux
                                          i 1 lti w1
                                          (#subs (s1 Data.List.∷ʳ a₁) G (→covered∷ʳ a₁ s1 G cG1))
                                          (#subs (s2 Data.List.∷ʳ a₂) G (→covered∷ʳ a₂ s2 G cG2))
                                          c1Gb)

  hs1 : equalInType i w (#subs s1 (SUM! F G) cS1) (#subs s1 t clt1) (#subs s2 t clt2)
  hs1 = π₂ (hs w s1 s2 cS1 cS2 clt1 clt2 es eh)

  hs2 : equalInType i w (#SUM! (#subs s1 F cF1) (#[0]subs s1 G cG1)) (#subs s1 t clt1) (#subs s2 t clt2)
  hs2 = ≡CTerm→equalInType (#subs-SUM! s1 F G cS1 cF1 cG1) hs1

  aw1 : ∀𝕎 w (λ w' e' → SUMeq! (equalInType i w' (#subs s1 F cF1))
                               (λ a b ea → equalInType i w' (sub0 a (#[0]subs s1 G cG1)))
                               w' (#subs s1 t clt1) (#subs s2 t clt2)
                      → equalInType i w' (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2)))
  aw1 w1 e1 (a₁ , a₂ , b₁ , b₂ , a∈ , c₁ , c₂ , b∈) =
    equalInType-#⇛ₚ-left-right-rev
      {i} {w1} {#subs s1 F cF1} {#FST (#subs s1 t clt1)} {a₁} {#FST (#subs s2 t clt2)} {a₂}
      (#⇛!-FST-PAIR (#subs s1 t clt1) a₁ b₁ w1 c₁)
      (#⇛!-FST-PAIR (#subs s2 t clt2) a₂ b₂ w1 c₂)
      a∈

  fst∈F1 : equalInType i w (#subs s1 F cF1) (#FST (#subs s1 t clt1)) (#FST (#subs s2 t clt2))
  fst∈F1 = equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-SUM!→ hs2))

  fst∈F : equalInType i w (#subs s1 F cF1) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2)
  fst∈F = ≡→equalInType
            refl
            (≣sym (#subs-FST s1 t cft1 clt1))
            (≣sym (#subs-FST s2 t cft2 clt2))
            fst∈F1

  c1Ga : equalTypes i w (sub0 (#subs s1 (FST t) cft1) (#[0]subs s1 G cG1)) (sub0 (#subs s2 (FST t) cft2) (#[0]subs s2 G cG2))
  c1Ga = c1G w (⊑-refl· w) (#subs s1 (FST t) cft1) (#subs s2 (FST t) cft2) fst∈F

  c1 : equalTypes i w (#subs s1 (subn 0 (FST t) G) cc1) (#subs s2 (subn 0 (FST t) G) cc2)
  c1 = {!!} -- use c1Ga by manipulating the subs

  c2 : equalInType i w (#subs s1 (subn 0 (FST t) G) cc1) (#subs s1 (SND t) ce1) (#subs s2 (SND t) ce2)
  c2 = {!!}


⟦_⟧Γ≡ : {n : Nat} {Γ : Con Term n} {σ τ : Term n}
        (j : Γ ⊢ σ ≡ τ)
        (i : Nat) (w : 𝕎·)
      → valid≡ i w ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ ⟦ τ ⟧ᵤ (UNIV 1)
⟦_⟧Γ≡ {n} {Γ} {σ} {τ} j i w = {!!}


⟦_⟧⊢ : {n : Nat} {Γ : Con Term n} {σ : Term n}
       (j : Γ ⊢ σ)
       (i : Nat) (lti : 1 <ℕ i)
     → valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ σ ⟧ᵤ (UNIV 1)
⟦_⟧⊢ {n} {Γ} {σ} j i lti w = {!!}


-- Should we use a closed version of the sequent constructor in valid∈ below?
⟦_⟧Γ∈ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
        (j : Γ ⊢ t ∷ σ)
        (i : Nat) (lti : 1 <ℕ i)
      → valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ σ ⟧ᵤ
⟦_⟧Γ∈ {n} {Γ} {.(Π _ ▹ _)} {.U} ((Πⱼ_▹_) {F} {G} j j₁) i lti w =
  valid∈-PI i lti ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ h1 h2 w
  where
  h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧Γ∈ j i lti

  h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
  h2 = ⟦_⟧Γ∈ j₁ i lti
⟦_⟧Γ∈ {n} {Γ} {.(Σ _ ▹ _)} {.U} ((Σⱼ_▹_) {F} {G} j j₁) i lti w =
  valid∈-SUM! i lti ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ h1 h2 w
  where
  h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧Γ∈ j i lti

  h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
  h2 = ⟦_⟧Γ∈ j₁ i lti
⟦_⟧Γ∈ {n} {Γ} {.ℕ} {.U} (ℕⱼ x) i lti w = valid∈-NAT! i lti ⟦ Γ ⟧Γ w
⟦_⟧Γ∈ {n} {Γ} {.Empty} {.U} (Emptyⱼ x) i lti w = valid∈-FALSE i lti ⟦ Γ ⟧Γ w
⟦_⟧Γ∈ {n} {Γ} {.Unit} {.U} (Unitⱼ x) i lti w = valid∈-UNIT i lti ⟦ Γ ⟧Γ w
⟦_⟧Γ∈ {n} {Γ} {.(var _)} {σ} (var {σ} {v} x x₁) i lti w = {!!} -- use valid∈VAR
⟦_⟧Γ∈ {n} {Γ} {.(lam _)} {.(Π _ ▹ _)} (lamⱼ {F} {G} {t} x j) i lti w =
  valid∈LAMBDA lti h1 h2 w
  where
  h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧⊢ x i lti

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
  h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧⊢ x i lti

  h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
  h2 = ⟦_⟧⊢ x₁ i lti

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

  h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧⊢ x i lti

  h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
  h2 = ⟦_⟧⊢ x₁ i lti

  h3 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ (SUM! ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ)
  h3 = ⟦_⟧Γ∈ j i lti
⟦_⟧Γ∈ {n} {Γ} {.(snd _)} {.(G [ fst u ])} (sndⱼ {F} {G} {u} x x₁ j) i lti w =
  ≣subst (valid∈ i w ⟦ Γ ⟧Γ (SND ⟦ u ⟧ᵤ))
         (≣sym (⟦[]⟧ᵤ-as-subn G (fst u)))
         (valid∈SND lti covH h1 h2 h3 w)
  where
  covH : coveredH ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ
  covH = coveredΓ {n} Γ F

  h1 : valid∈𝕎 i ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧⊢ x i lti

  h2 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
  h2 = ⟦_⟧⊢ x₁ i lti

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
         (valid∈NATREC {i} {⟦ Γ ⟧Γ} {⟦ G ⟧ᵤ} {⟦ k ⟧ᵤ} {⟦ z ⟧ᵤ} {⟦ s ⟧ᵤ} lti h1 h2' h3'' h4 w)
  -- valid∈NATREC and use ⟦[]⟧ᵤ-as-sub
  where
  h1 : valid∈𝕎 i (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp NAT!) ⟦ G ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧⊢ x i lti

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
⟦_⟧Γ∈ {n} {Γ} {.star} {.Unit} (starⱼ x) i lti w = valid∈-AX-UNIT i lti ⟦ Γ ⟧Γ w
⟦_⟧Γ∈ {n} {Γ} {t} {σ} (conv {t} {τ} {σ} j x) i lti w =
  valid∈-change-type {i} {w} {⟦ Γ ⟧Γ} {⟦ τ ⟧ᵤ} {⟦ σ ⟧ᵤ} lti cov h1 h2
  where
  h1 : valid≡ i w ⟦ Γ ⟧Γ ⟦ τ ⟧ᵤ ⟦ σ ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧Γ≡ x i w

  h2 : valid∈ i w ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ τ ⟧ᵤ
  h2 = ⟦_⟧Γ∈ j i lti w

  cov : coveredH ⟦ Γ ⟧Γ ⟦ τ ⟧ᵤ
  cov = coveredΓ {n} Γ τ


⟦_⟧Γ≡∈ : {n : Nat} {Γ : Con Term n} {t u : Term n} {σ : Term n}
         (j : Γ ⊢ t ≡ u ∷ σ)
         (i : Nat) (w : 𝕎·)
       → valid≡ i w ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ u ⟧ᵤ ⟦ σ ⟧ᵤ
⟦_⟧Γ≡∈ {n} {Γ} {t} {u} {σ} j i w = {!!}


⟦_⟧≡∈ : {t u : Term 0} {σ : Term 0}
        (j : ε ⊢ t ≡ u ∷ σ)
        (i : Nat) (w : 𝕎·)
      → equalInType i w ⟦ j ⟧≡ₜ₀ ⟦ j ⟧≡ₗ₀ ⟦ j ⟧≡ᵣ₀ -- in the empty context
⟦_⟧≡∈ {t} {u} {σ} j i w = {!!}

\end{code}
