\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
--open import Data.Nat using (ℕ ; _≟_ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _⊔_)
open import Agda.Builtin.Nat
open import Data.Fin using (Fin)
open import Agda.Builtin.Equality renaming (_≡_ to _≣_)
open import Agda.Builtin.Sigma renaming (fst to π₁ ; snd to π₂)
open import Relation.Binary.PropositionalEquality
  using (cong ; cong₂) renaming (trans to ≣trans ; sym to ≣sym ; subst to ≣subst)
open import Data.List using () renaming ([] to nil ; _∷_ to cons)
open import Data.Product
open import Axiom.Extensionality.Propositional

-- MLTT imports
open import Definition.Untyped hiding (_∷_)
open import Definition.Untyped.Properties using (wk-β ; wk1-sgSubst ; subst-wk)
open import Definition.Typed
open import Definition.Typed.Weakening renaming (wk to wk⊢)
open import Definition.Typed.Consequences.Substitution using (substType ; substTerm)
open import Definition.Typed.Consequences.Syntactic using (syntacticEq)
open import Tools.Nat using (1+)

-- BoxTT imports
open import calculus renaming (Term to BTerm)
open import terms -- renaming (Term to BTerm)
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
∷→⊢ {n} {Γ} {.(natrec _ _ _ _)} {.(G [ k ])} (natrecⱼ {G} {s} {z} {k} x i i₁ i₂) = {!!}
  where
    y1 : Γ ⊢ Π ℕ ▹ (G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑)
    y1 = ∷→⊢ i₁

    y2 : Γ ⊢ ((G ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑) [ k ])
    y2 = ⊢Π[] y1 i₂

    y3 : Γ ⊢ G [ k ] ▹▹ G [ Definition.Untyped.suc (var Fin.zero) ]↑ [ k ]
    y3 = ≣subst (λ z → Γ ⊢ z) (▹▹[] G (G [ Definition.Untyped.suc (var Fin.zero) ]↑) k) y2

    y4 : Γ ⊢ (G [ Definition.Untyped.suc (var Fin.zero) ]↑) [ k ]
    y4 = →▹▹[]ᵣ {!!} y3
∷→⊢ {n} {Γ} {.(Emptyrec σ _)} {σ} (Emptyrecⱼ x i) = x
∷→⊢ {n} {Γ} {.star} {.Unit} (starⱼ x) = Unitⱼ x
∷→⊢ {n} {Γ} {t} {σ} (conv {t} {A} {B} i x) =
  π₂ (syntacticEq x)
  where
    y : Γ ⊢ A
    y = ∷→⊢ i


-- Converts an MLTT term to its BoxTT type
⟦_⟧ₜ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
     → Γ ⊢ t ∷ σ
     → BTerm
⟦_⟧ₜ {n} {Γ} {.(Π _ ▹ _)} {.U} ((Πⱼ_▹_) {F} {G} A B) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.(Σ _ ▹ _)} {.U} ((Σⱼ_▹_) {F} {G} A B) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.ℕ} {.U} (ℕⱼ x) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.Empty} {.U} (Emptyⱼ x) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.Unit} {.U} (Unitⱼ x) = UNIV 1
⟦_⟧ₜ {n} {Γ} {.(var _)} {σ} (var x x₁) = VAR n -- convert σ
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


-- Converts an MLTT term into a BoxTT term
⟦_⟧ : {n : Nat} {Γ : Con Term n} {t : Term n} {σ : Term n}
    → Γ ⊢ t ∷ σ
    → BTerm
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


⟦_⟧≡ : (i : Nat) (w : 𝕎·) {n : Nat} {Γ : Con Term n} {t u : Term n} {σ : Term n}
     → Γ ⊢ t ≡ u ∷ σ
     → Set --equalInType i w ⟦ σ ⟧ₜ ⟦ t ⟧ ⟦ u ⟧ -- in the empty context
⟦_⟧≡ i w {n} {Γ} {t} {u} {σ} j = {!!}

\end{code}
