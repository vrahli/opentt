\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Data.Nat using () renaming (_<_ to _<ℕ_)
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
  using (cong ; cong₂) renaming (trans to ≣trans ; sym to ≣sym ; subst to ≣subst)
open import Data.List using () renaming ([] to nil ; _∷_ to cons)
open import Data.List.Relation.Unary.Any
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
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import sequent(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (isTypeNAT! ; eqTypesUniv ; equalTypes→equalInType-UNIV ; equalInType→equalTypes-aux ; eqTypesPI← ;
         ≡CTerm→eqTypes ; ≡CTerm→equalInType)
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
⟦_⟧T {n} {Γ} {.(Σ _ ▹ _)} ((Σⱼ_▹_) {F} {G} i j) = SUM ⟦ i ⟧T ⟦ j ⟧T
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
⟦_⟧ᵤ {n} (gen {.(cons 0 (cons 1 nil))} Sigmakind (t GenTs.∷ (t₁ GenTs.∷ []))) = SUM ⟦ t ⟧ᵤ ⟦ t₁ ⟧ᵤ
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
⟦_⟧ᵤ {n} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) = BOT


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
  with ∈-++⁻ (fvars ⟦ t ⟧ᵤ) i
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
fvarsᵤ {n} (gen {.(cons 0 (cons 0 nil))} Emptyreckind (t GenTs.∷ (t₁ GenTs.∷ []))) v ()
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
                      {!!}
                      (≡hyps-mon e1 eh))))
 {--( (equalTypes-uni-mon (<⇒≤ lti) {!!}) (≡hyps-mon e1 ?)))) -- need something like ≡subs∷ʳ for ≡hyps
--}

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


-- Should we use a closed version of the sequent constructor in valid∈ below?
⟦_⟧Γ∈ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
        (j : Γ ⊢ t ∷ σ)
        (i : Nat) (lti : 1 <ℕ i) (w : 𝕎·)
      → valid∈ i w ⟦ Γ ⟧Γ ⟦ t ⟧ᵤ ⟦ σ ⟧ᵤ
⟦_⟧Γ∈ {n} {Γ} {.(Π _ ▹ _)} {.U} ((Πⱼ_▹_) {F} {G} j j₁) i lti w =
  valid∈-PI i lti ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ ⟦ G ⟧ᵤ h1 h2 w
  where
  h1 : (w : 𝕎·) → valid∈ i w ⟦ Γ ⟧Γ ⟦ F ⟧ᵤ (UNIV 1)
  h1 = ⟦_⟧Γ∈ j i lti

  h2 : (w : 𝕎·) → valid∈ i w (⟦ Γ ⟧Γ Data.List.∷ʳ mkHyp ⟦ F ⟧ᵤ) ⟦ G ⟧ᵤ (UNIV 1)
  h2 = ⟦_⟧Γ∈ j₁ i lti
⟦_⟧Γ∈ {n} {Γ} {.(Σ _ ▹ _)} {.U} ((Σⱼ_▹_) {F} {G} j j₁) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.ℕ} {.U} (ℕⱼ x) i lti w = valid∈-NAT! i lti ⟦ Γ ⟧Γ w
⟦_⟧Γ∈ {n} {Γ} {.Empty} {.U} (Emptyⱼ x) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.Unit} {.U} (Unitⱼ x) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(var _)} {σ} (var x x₁) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(lam _)} {.(Π _ ▹ _)} (lamⱼ x j) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(_ ∘ _)} {.(G [ a ])} ((_∘ⱼ_) {g} {a} {F} {G} j j₁) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(prod _ _)} {.(Σ _ ▹ _)} (prodⱼ x x₁ j j₁) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(fst _)} {σ} (fstⱼ x x₁ j) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(snd _)} {.(G [ fst u ])} (sndⱼ {F} {G} {u} x x₁ j) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.Definition.Untyped.zero} {.ℕ} (zeroⱼ x) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(Definition.Untyped.suc _)} {.ℕ} (sucⱼ j) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(natrec _ _ _ _)} {.(G [ k ])} (natrecⱼ {G} {s} {z} {k} x j j₁ j₂) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.(Emptyrec σ _)} {σ} (Emptyrecⱼ x j) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {.star} {.Unit} (starⱼ x) i lti w = {!!}
⟦_⟧Γ∈ {n} {Γ} {t} {σ} (conv j x) i lti w = {!!}


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
