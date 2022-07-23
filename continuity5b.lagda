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
open import choiceBar


module continuity5b {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                    (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                    (X : ChoiceExt W C)
                    (N : NewChoice {L} W C K G)
                    (E : Extensionality 0ℓ (lsuc(lsuc(L))))
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

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3b(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4b(W)(M)(C)(K)(P)(G)(X)(N)(E)



-- subRen r1 r2 means that r1 is a sub-renaming of r2
data subRen (l k : List Name) : ren → ren → Set where
  subRen-refl : (r : ren) → subRen l k r r
  subRen-trans : (a b : Name) (r1 r2 : ren)
                 → ¬ a ∈ l -- The new names picked are 'fresh' names
                 → ¬ b ∈ k
                 → subRen l k r1 r2
                 → subRen l k r1 ((a , b) ∷ r2)


presUpdRel2 : (n : ℕ) (name : Name) (f g : Term) (k : ℕ) → Set(lsuc L)
presUpdRel2 n name f g k =
  {a b v : Term} {w0 w1 w2 w : 𝕎·} {r : ren}
  → updRel2 name f g r a b
  → names a ⊆ dom𝕎· w1
  → names b ⊆ dom𝕎· w
  → name ∈ dom𝕎· w
--  → names f ⊆ dom𝕎· w1
--  → names g ⊆ dom𝕎· w
  → upto𝕎 name w1 w r
  → compatible· name w1 Res⊤
  → compatible· name w Res⊤
  → ∀𝕎-get0-NUM w1 name
-- We use ∀𝕎-⇓∼ℕ instead of strongMonEq because if g could change the target world, it could be used for...
--  → ∀𝕎 w (λ w' _ → (k : ℕ) → k < n → ∀𝕎-⇓∼ℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
  → w0 ⊑· w1
  → w0 ⊑· w
  → ∀𝕎 w0 (λ w' _ → (k : ℕ) → k < n → ⇛!sameℕ w' (APPLY f (NUM k)) (APPLY g (NUM k)))
  → (comp : steps k (a , w1) ≡ (v , w2))
  → isHighestℕ {k} {w1} {w2} {a} {v} n name comp
  → ∈names𝕎 {k} {w1} {w2} {a} {v} name comp
  → isValue v
  → Σ ℕ (λ k' → Σ Term (λ v' → Σ 𝕎· (λ w' → Σ ren (λ r' →
      steps k' (b , w) ≡ (v' , w')
      × updRel2 name f g r' v v'
      × upto𝕎 name w2 w' r'
      × subRen (dom𝕎· w1) (dom𝕎· w) r r'))))


stepsPresUpdRel2 : (n : ℕ) (name : Name) (f g : Term) (b : Term) (w : 𝕎·) → Set(lsuc L)
stepsPresUpdRel2 n name f g b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    Σ (steps k (b , w) ≡ (v , w')) (λ comp →
    isValue v
    × isHighestℕ {k} {w} {w'} {b} {v} n name comp
    × ∈names𝕎 {k} {w} {w'} {b} {v} name comp
    × ((k' : ℕ) → k' ≤ k → presUpdRel2 n name f g k')))))


-- NOTE: We won't be able to prove that for impure terms x because it might read a choice
-- and return 2 different values in the two worlds w2 and w
ΣstepsUpdRel2 : (name : Name) (f g : Term) (x : Term) (w1 w2 : 𝕎·) (b : Term) (w : 𝕎·) (r : ren) → Set(1ℓ Level.⊔ L)
ΣstepsUpdRel2 name f g x w1 w2 b w r =
  Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ Term (λ y1 → Σ Term (λ y2 → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w' → Σ ren (λ r' →
    steps k1 (x , w2) ≡ (y1 , w3)
    × steps k2 (b , w) ≡ (y2 , w')
    × updRel2 name f g r' y1 y2
    × upto𝕎 name w3 w' r'
    × subRen (dom𝕎· w1) (dom𝕎· w) r r')))))))



isHighestℕ2-APPLY₂→ : {n : ℕ} {k : ℕ} {name : Name} {f g : Term} {name' : Name} {b v : Term} {w w' : 𝕎·}
                      → (comp : steps k (APPLY (CS name') b , w) ≡ (v , w'))
                      → isValue v
                      → isHighestℕ {k} {w} {w'} {APPLY (CS name') b} {v} n name comp
                      → ∈names𝕎 {k} {w} {w'} {APPLY (CS name') b} {v} name comp
                      → Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {b} {u} n name comp'
                          × ∈names𝕎 {k'} {w} {w''} {b} {u} name comp'
                          × isValue u
                          × k' < k))))
isHighestℕ2-APPLY₂→ {n} {0} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv h inw
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
isHighestℕ2-APPLY₂→ {n} {suc k} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv h inw with is-NUM b
... | inj₁ (j , r) rewrite r with getT j name' w
... |    just t = 0 , NUM j , w , refl , fst h , (fst inw , fst (snd inw)) , tt , _≤_.s≤s _≤_.z≤n
... |    nothing = 0 , NUM j , w , refl , h , inw , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ2-APPLY₂→ {n} {suc k} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv h inw | inj₂ r with step⊎ b w
... |    inj₁ (b0 , w0 , z) rewrite z = suc (fst ind) , concl
  where
    ind : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b0 , w0) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w0} {w''} {b0} {u} n name comp'
                          × ∈names𝕎 {k'} {w0} {w''} {b0} {u} name comp'
                          × isValue u
                          × k' < k))))
    ind = isHighestℕ2-APPLY₂→ {n} {k} {name} {f} {g} {name'} {b0} {v} {w0} {w'} comp isv (snd h) (snd (snd inw))

    concl : Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps (suc (fst ind)) (b , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {suc (fst ind)} {w} {w''} {b} {u} n name comp'
                          × ∈names𝕎 {suc (fst ind)} {w} {w''} {b} {u} name comp'
                          × isValue u
                          × suc (fst ind) < suc k)))
    concl rewrite z =
      fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
      (fst h , fst (snd (snd (snd (snd ind))))) ,
      (fst inw , fst (snd inw) , fst (snd (snd (snd (snd (snd ind)))))) ,
      fst (snd (snd (snd (snd (snd (snd ind)))))) ,
      _≤_.s≤s (snd (snd (snd (snd (snd (snd (snd ind)))))))
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



stepsPresUpdRel2-APPLY₂→ : {n : ℕ} {name : Name} {f g : Term} {name' : Name} {b : Term} {w : 𝕎·}
                           → stepsPresUpdRel2 n name f g (APPLY (CS name') b) w
                           → stepsPresUpdRel2 n name f g b w
stepsPresUpdRel2-APPLY₂→ {n} {name} {f} {g} {name'} {b} {w} (k , v , w' , comp , isv , ish , inw , ind) =
  fst hv , fst (snd hv) , fst (snd (snd hv)) , fst (snd (snd (snd hv))) ,
  fst (snd (snd (snd (snd (snd (snd hv)))))) , fst (snd (snd (snd (snd hv)))) ,
  fst (snd (snd (snd (snd (snd hv))))) ,
  λ k' j → ind k' (<⇒≤ (<-transʳ j (snd (snd (snd (snd (snd (snd (snd hv)))))))))
  where
    hv : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {b} {u} n name comp'
                          × ∈names𝕎 {k'} {w} {w''} {b} {u} name comp'
                          × isValue u
                          × k' < k))))
    hv = isHighestℕ2-APPLY₂→ {n} {k} {name} {f} {g} {name'} {b} {v} {w} {w'} comp isv ish inw


→Σ-steps-APPLY-CS : (n : ℕ) (a b : Term) (w w' : 𝕎·) (name : Name)
                 → steps n (a , w) ≡ (b , w')
                 → Σ ℕ (λ m → steps m (APPLY (CS name) a , w) ≡ (APPLY (CS name) b , w'))
→Σ-steps-APPLY-CS n a b w w' name h =
  fst (Σ-steps-APPLY-CS≤ n a b w w' name h) ,
  snd (snd (Σ-steps-APPLY-CS≤ n a b w w' name h))



dren : ren → ren
dren [] = []
dren ((a , b) ∷ r) = (pred a , pred b) ∷ dren r



∈ren-sucIf≤-ren→ : (n name1 name2 : Name) (r : ren)
                    → (sucIf≤ n name1 , sucIf≤ n name2) ∈ sucIf≤-ren n r
                    → (name1 , name2) ∈ r
∈ren-sucIf≤-ren→ n name1 name2 ((a , b) ∷ xs) (here px)
  rewrite sym (sucIf≤-inj {n} {name1} {a} (pair-inj₁ px))
        | sym (sucIf≤-inj {n} {name2} {b} (pair-inj₂ px)) = here refl
∈ren-sucIf≤-ren→ n name1 name2 (x ∷ xs) (there i) = there (∈ren-sucIf≤-ren→ n name1 name2 xs i)



→∈renₗ-sucIf≤-ren : {name : Name} {r : ren} (n : Name)
                    → name ∈ renₗ r
                    → sucIf≤ n name ∈ renₗ (sucIf≤-ren n r)
→∈renₗ-sucIf≤-ren {name} {[]} n ()
→∈renₗ-sucIf≤-ren {name} {(a , b) ∷ r} n (here px) rewrite sym px = here refl
→∈renₗ-sucIf≤-ren {name} {(a , b) ∷ r} n (there i) = there (→∈renₗ-sucIf≤-ren {name} {r} n i)


→∈renᵣ-sucIf≤-ren : {name : Name} {r : ren} (n : Name)
                    → name ∈ renᵣ r
                    → sucIf≤ n name ∈ renᵣ (sucIf≤-ren n r)
→∈renᵣ-sucIf≤-ren {name} {[]} n ()
→∈renᵣ-sucIf≤-ren {name} {(a , b) ∷ r} n (here px) rewrite sym px = here refl
→∈renᵣ-sucIf≤-ren {name} {(a , b) ∷ r} n (there i) = there (→∈renᵣ-sucIf≤-ren {name} {r} n i)


names∈ren-sucIf≤-ren→ : (n name1 name2 : Name) (r : ren)
                         → names∈ren (sucIf≤ n name1) (sucIf≤ n name2) (sucIf≤-ren n r)
                         → names∈ren name1 name2 r
names∈ren-sucIf≤-ren→ n name1 name2 [] e = sucIf≤-inj {n} {name1} {name2} e
names∈ren-sucIf≤-ren→ n name1 name2 ((a , b) ∷ r) (inj₁ (e₁ , e₂)) =
  inj₁ (sucIf≤-inj {n} {name1} {a} e₁ , (sucIf≤-inj {n} {name2} {b} e₂))
names∈ren-sucIf≤-ren→ n name1 name2 ((a , b) ∷ r) (inj₂ (e₁ , e₂ , x)) =
  inj₂ ((λ z → e₁ (→≡sucIf≤ z)) , (λ z → e₂ (→≡sucIf≤ z)) , (names∈ren-sucIf≤-ren→ n name1 name2 r x))



force≡shiftNameUp→ : (v : Var) (name : Name) (g : Term) (b : Term)
                      → LET (VAR 0) (APPLY (shiftNameUp v g) (VAR 0)) ≡ shiftNameUp v b
                      → b ≡ LET (VAR 0) (APPLY g (VAR 0))
force≡shiftNameUp→ v name g (LET (VAR 0) (APPLY b (VAR 0))) e
  rewrite shiftNameUp-inj {v} {g} {b} (APPLYinj1 (LETinj2 e)) = refl



updRel2-shiftNameUp-LAMBDA→ : (v : Name) {name : Name} {f g : Term} (cf : # f) (cg : # g) {r : ren} {a b t u : Term}
                                → t ≡ shiftNameUp v a
                                → u ≡ shiftNameUp v b
                                → updRel2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v g) (sucIf≤-ren v r) (LAMBDA t) u
                                → ((c : Term)
                                    → updRel2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v g) (sucIf≤-ren v r) (shiftNameUp v a) (shiftNameUp v c)
                                    → updRel2 name f g r a c)
                                → updRel2 name f g r (LAMBDA a) b
updRel2-shiftNameUp-LAMBDA→ v {name} {f} {g} cf cg {r} {a} {LAMBDA b} {t} {.(LAMBDA c)} e₁ e₂ (updRel2-LAMBDA .t c u₁) ind rewrite e₁ | LAMinj e₂ = updRel2-LAMBDA _ _ (ind b u₁)
updRel2-shiftNameUp-LAMBDA→ v {name} {f} {g} cf cg {r} {a} {LAMBDA b} {.(updBody (sucIf≤ v name) (shiftNameUp v f))} {.(force (shiftNameUp v g))} e₁ e₂ updRel2-upd ind
  rewrite updBody≡shiftNameUp→ v name f a e₁
        | force≡shiftNameUp→ v name g b (LAMinj e₂) = updRel2-upd



updRel2-shiftNameUp→ : (n : ℕ) {name : Name} {f g : Term} {r : ren} (cf : # f) (cg : # g) {a b : Term}
                        → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) (shiftNameUp n a) (shiftNameUp n b)
                        → updRel2 name f g r a b
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {VAR x} {VAR .x} (updRel2-VAR .x) = updRel2-VAR x
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {NAT} {NAT} updRel2-NAT = updRel2-NAT
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {QNAT} {QNAT} updRel2-QNAT = updRel2-QNAT
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {TNAT} {TNAT} updRel2-TNAT = updRel2-TNAT
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {LT a a₁} {LT b b₁} (updRel2-LT .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-LT _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {QLT a a₁} {QLT b b₁} (updRel2-QLT .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-QLT _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {NUM x} {NUM .x} (updRel2-NUM .x) = updRel2-NUM x
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {IFLT a a₁ a₂ a₃} {IFLT b b₁ b₂ b₃} (updRel2-IFLT .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) .(shiftNameUp n a₂) .(shiftNameUp n b₂) .(shiftNameUp n a₃) .(shiftNameUp n b₃) u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁) (updRel2-shiftNameUp→ n cf cg u₂) (updRel2-shiftNameUp→ n cf cg u₃)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {SUC a} {SUC b} (updRel2-SUC .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-SUC _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {PI a a₁} {PI b b₁} (updRel2-PI .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-PI _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {LAMBDA a} {b} u =
  updRel2-shiftNameUp-LAMBDA→ n {name} {f} {g} cf cg {r} {a} {b} {shiftNameUp n a} {shiftNameUp n b} refl refl u ind
  where
    ind : (c : Term)
          → updRel2 (sucIf≤ n name) (shiftNameUp n f) (shiftNameUp n g) (sucIf≤-ren n r) (shiftNameUp n a) (shiftNameUp n c)
          → updRel2 name f g r a c
    ind c = updRel2-shiftNameUp→ n cf cg {a} {c}
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {APPLY a a₁} {APPLY b b₁} (updRel2-APPLY .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-APPLY _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {FIX a} {FIX b} (updRel2-FIX .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-FIX _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {LET a a₁} {LET b b₁} (updRel2-LET .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-LET _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {SUM a a₁} {SUM b b₁} (updRel2-SUM .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-SUM _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {PAIR a a₁} {PAIR b b₁} (updRel2-PAIR .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-PAIR _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {SPREAD a a₁} {SPREAD b b₁} (updRel2-SPREAD .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {SET a a₁} {SET b b₁} (updRel2-SET .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-SET _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {TUNION a a₁} {TUNION b b₁} (updRel2-TUNION .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-TUNION _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {ISECT a a₁} {ISECT b b₁} (updRel2-ISECT .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-ISECT _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {UNION a a₁} {UNION b b₁} (updRel2-UNION .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-UNION _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {QTUNION a a₁} {QTUNION b b₁} (updRel2-QTUNION .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {INL a} {INL b} (updRel2-INL .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-INL _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {INR a} {INR b} (updRel2-INR .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-INR _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {DECIDE a a₁ a₂} {DECIDE b b₁ b₂} (updRel2-DECIDE .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) .(shiftNameUp n a₂) .(shiftNameUp n b₂) u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁) (updRel2-shiftNameUp→ n cf cg u₂)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {EQ a a₁ a₂} {EQ b b₁ b₂} (updRel2-EQ .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) .(shiftNameUp n a₂) .(shiftNameUp n b₂) u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁) (updRel2-shiftNameUp→ n cf cg u₂)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {EQB a a₁ a₂ a₃} {EQB b b₁ b₂ b₃} (updRel2-EQB .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) .(shiftNameUp n a₂) .(shiftNameUp n b₂) .(shiftNameUp n a₃) .(shiftNameUp n b₃) u u₁ u₂ u₃) = updRel2-EQB _ _ _ _ _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁) (updRel2-shiftNameUp→ n cf cg u₂) (updRel2-shiftNameUp→ n cf cg u₃)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {AX} {AX} updRel2-AX = updRel2-AX
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {FREE} {FREE} updRel2-FREE = updRel2-FREE
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {CS name1} {CS name2} (updRel2-CS .(sucIf≤ n name1) .(sucIf≤ n name2) d1 d2 i) = updRel2-CS name1 name2 (λ z → d1 (→≡sucIf≤ z)) (λ z → d2 (→≡sucIf≤ z)) (names∈ren-sucIf≤-ren→ n name1 name2 r i)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {NAME name1} {NAME name2} (updRel2-NAME .(sucIf≤ n name1) .(sucIf≤ n name2) d1 d2 i) = updRel2-NAME name1 name2 (λ z → d1 (→≡sucIf≤ z)) (λ z → d2 (→≡sucIf≤ z)) (names∈ren-sucIf≤-ren→ n name1 name2 r i)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {FRESH a} {FRESH b} (updRel2-FRESH .(shiftNameUp (suc n) a) .(shiftNameUp (suc n) b) u) =
  updRel2-FRESH _ _ (updRel2-shiftNameUp→ (suc n) {suc name} {shiftNameUp 0 f}
                       {shiftNameUp 0 g} {sren r} (→#shiftNameUp 0 {f} cf)
                       (→#shiftNameUp 0 {g} cg) {a} {b} upd1)
  where
    seq1 : suc (sucIf≤ n name) ≡ sucIf≤ (suc n) (sucIf≤ 0 name)
    seq1 rewrite sym (sucIf≤-sucIf≤ {name} {0} {n} _≤_.z≤n) | sym (suc≡sucIf≤0 (sucIf≤ n name)) = refl

    seq2 : sren (sucIf≤-ren n r) ≡ sucIf≤-ren (suc n) (sren r)
    seq2 = sym (sucIf≤-ren-suc-sren n r)

    upd1 : updRel2 (sucIf≤ (suc n) (suc name))
                   (shiftNameUp (suc n) (shiftNameUp 0 f))
                   (shiftNameUp (suc n) (shiftNameUp 0 g))
                   (sucIf≤-ren (suc n) (sren r))
                   (shiftNameUp (suc n) a)
                   (shiftNameUp (suc n) b)
    upd1 rewrite suc≡sucIf≤0 name | sym seq1 | sym seq2 | sym (shiftNameUp-shiftNameUp {0} {n} {f} _≤_.z≤n) | sym (shiftNameUp-shiftNameUp {0} {n} {g} _≤_.z≤n) = u
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {LOAD a} {LOAD .a} (updRel2-LOAD .a) = updRel2-LOAD _
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {CHOOSE a a₁} {CHOOSE b b₁} (updRel2-CHOOSE .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {TSQUASH a} {TSQUASH b} (updRel2-TSQUASH .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-TSQUASH _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {TTRUNC a} {TTRUNC b} (updRel2-TTRUNC .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-TTRUNC _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {TCONST a} {TCONST b} (updRel2-TCONST .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-TCONST _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {SUBSING a} {SUBSING b} (updRel2-SUBSING .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-SUBSING _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {DUM a} {DUM b} (updRel2-DUM .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-DUM _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {FFDEFS a a₁} {FFDEFS b b₁} (updRel2-FFDEFS .(shiftNameUp n a) .(shiftNameUp n b) .(shiftNameUp n a₁) .(shiftNameUp n b₁) u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-shiftNameUp→ n cf cg u) (updRel2-shiftNameUp→ n cf cg u₁)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {PURE} {PURE} updRel2-PURE = updRel2-PURE
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {UNIV x} {UNIV .x} (updRel2-UNIV .x) = updRel2-UNIV x
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {LIFT a} {LIFT b} (updRel2-LIFT .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-LIFT _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {LOWER a} {LOWER b} (updRel2-LOWER .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-LOWER _ _ (updRel2-shiftNameUp→ n cf cg u)
updRel2-shiftNameUp→ n {name} {f} {g} {r} cf cg {SHRINK a} {SHRINK b} (updRel2-SHRINK .(shiftNameUp n a) .(shiftNameUp n b) u) = updRel2-SHRINK _ _ (updRel2-shiftNameUp→ n cf cg u)



→updRel2-shiftNameDown : (v : Name) {name : Name} {f g : Term} (cf : # f) (cg : # g) (r : ren) {a b : Term}
                           → ((x : Name) → x ∈ names a → ¬ x ≡ v)
                           → ((x : Name) → x ∈ names b → ¬ x ≡ v)
                           → (0 ∈ names a → 0 < v)
                           → (0 ∈ names b → 0 < v)
                           → updRel2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v g) (sucIf≤-ren v r) a b
                           → updRel2 name f g r (shiftNameDown v a) (shiftNameDown v b)
→updRel2-shiftNameDown v {name} {f} {g} cf cg r {a} {b} impa1 impb1 impa2 impb2 u =
  updRel2-shiftNameUp→ v {name} {f} {g} {r} cf cg {shiftNameDown v a} {shiftNameDown v b} upd1
  where
    upd1 : updRel2 (sucIf≤ v name) (shiftNameUp v f) (shiftNameUp v g) (sucIf≤-ren v r) (shiftNameUp v (shiftNameDown v a)) (shiftNameUp v (shiftNameDown v b))
    upd1 rewrite shiftNameUpDown v a impa1 impa2 | shiftNameUpDown v b impb1 impb2 = u




→updRel2-shiftNameDown0 : {name : Name} {f g : Term} (cf : # f) (cg : # g) (r : ren) {a b : Term}
                           → ¬ 0 ∈ names a
                           → ¬ 0 ∈ names b
                           → updRel2 (suc name) (shiftNameUp 0 f) (shiftNameUp 0 g) (sren r) a b
                           → updRel2 name f g r (shiftNameDown 0 a) (shiftNameDown 0 b)
→updRel2-shiftNameDown0 {name} {f} {g} cf cg r {a} {b} impa impb u =
  →updRel2-shiftNameDown
    0 {name} {f} {g} cf cg r {a} {b} na nb
    (λ x → ⊥-elim (impa x)) (λ x → ⊥-elim (impb x))
    u'
  where
    na : (x : Name) → x ∈ names a → ¬ x ≡ 0
    na x i e rewrite e = impa i

    nb : (x : Name) → x ∈ names b → ¬ x ≡ 0
    nb x i e rewrite e = impb i

    u' : updRel2 (sucIf≤ 0 name) (shiftNameUp 0 f) (shiftNameUp 0 g) (sucIf≤-ren 0 r) a b
    u' rewrite sym (suc≡sucIf≤0 name) | sym (sren≡sucIf≤0-ren r) = u



→names∈ren∷ : {n1 n2 name1 name2 : Name} {r : ren}
               → ¬ n1 ≡ name1
               → ¬ n2 ≡ name2
               → names∈ren name1 name2 r
               → names∈ren name1 name2 ((n1 , n2) ∷ r)
→names∈ren∷ {n1} {n2} {name1} {name2} {r} d1 d2 i =
  inj₂ ((λ z → d1 (sym z)) , (λ z → d2 (sym z)) , i)



→∈renₗ : (a b : Name) (r : ren) → (a , b) ∈ r → a ∈ renₗ r
→∈renₗ a b ((u , v) ∷ r) (here px) rewrite pair-inj₁ px | pair-inj₂ px = here refl
→∈renₗ a b ((u , v) ∷ r) (there i) = there (→∈renₗ a b r i)


→∈renᵣ : (a b : Name) (r : ren) → (a , b) ∈ r → b ∈ renᵣ r
→∈renᵣ a b ((u , v) ∷ r) (here px) rewrite pair-inj₁ px | pair-inj₂ px = here refl
→∈renᵣ a b ((u , v) ∷ r) (there i) = there (→∈renᵣ a b r i)


suc∈renₗ-sren→ : {n : Name} {r : ren}
                 → suc n ∈ renₗ (sren r)
                 → n ∈ renₗ r
suc∈renₗ-sren→ {n} {[]} ()
suc∈renₗ-sren→ {n} {(a , b) ∷ r} (here p) = here (suc-injective p)
suc∈renₗ-sren→ {n} {(a , b) ∷ r} (there p) = there (suc∈renₗ-sren→ p)


suc∈renᵣ-sren→ : {n : Name} {r : ren}
                 → suc n ∈ renᵣ (sren r)
                 → n ∈ renᵣ r
suc∈renᵣ-sren→ {n} {[]} ()
suc∈renᵣ-sren→ {n} {(a , b) ∷ r} (here p) = here (suc-injective p)
suc∈renᵣ-sren→ {n} {(a , b) ∷ r} (there p) = there (suc∈renᵣ-sren→ p)


¬∈renₗ-names∈ren→ : (n1 n2 : Name) (r : ren)
                    → names∈ren n1 n2 r
                    → ¬ n1 ∈ renₗ r
                    → n1 ≡ n2
¬∈renₗ-names∈ren→ n1 n2 [] i d = i
¬∈renₗ-names∈ren→ n1 n2 ((a , b) ∷ r) (inj₁ (i₁ , i₂)) d rewrite i₁ | i₂ = ⊥-elim (d (here refl))
¬∈renₗ-names∈ren→ n1 n2 ((a , b) ∷ r) (inj₂ (i₁ , i₂ , x)) d = ¬∈renₗ-names∈ren→ n1 n2 r x (λ z → d (there z))



¬∈renᵣ-names∈ren→ : (n1 n2 : Name) (r : ren)
                    → names∈ren n1 n2 r
                    → ¬ n2 ∈ renᵣ r
                    → n1 ≡ n2
¬∈renᵣ-names∈ren→ n1 n2 [] i d = i
¬∈renᵣ-names∈ren→ n1 n2 ((a , b) ∷ r) (inj₁ (i₁ , i₂)) d rewrite i₁ | i₂ = ⊥-elim (d (here refl))
¬∈renᵣ-names∈ren→ n1 n2 ((a , b) ∷ r) (inj₂ (i₁ , i₂ , x)) d = ¬∈renᵣ-names∈ren→ n1 n2 r x (λ z → d (there z))


updRel2-renn : {name : Name} {f g : Term} {r : ren} {a b : Term} (n n1 n2 : Name)
               → ¬ n1 ∈ names a
               → ¬ n2 ∈ names b
               → ¬ n1 ≡ name
               → ¬ n2 ≡ name
               → ¬ n ∈ renₗ r
               → ¬ n ∈ renᵣ r
               → ¬ n ∈ names f
               → ¬ n ∈ names g
               → ¬ n ≡ name
               → updRel2 name f g r a b
               → updRel2 name f g ((n1 , n2) ∷ r) (renn n n1 a) (renn n n2 b)
updRel2-renn {name} {f} {g} {r} {.(VAR x)} {.(VAR x)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-VAR x) = updRel2-VAR x
updRel2-renn {name} {f} {g} {r} {.NAT} {.NAT} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm updRel2-NAT = updRel2-NAT
updRel2-renn {name} {f} {g} {r} {.QNAT} {.QNAT} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm updRel2-QNAT = updRel2-QNAT
updRel2-renn {name} {f} {g} {r} {.TNAT} {.TNAT} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm updRel2-TNAT = updRel2-TNAT
updRel2-renn {name} {f} {g} {r} {.(LT a₁ b₁)} {.(LT a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-LT a₁ a₂ b₁ b₂ u u₁) = updRel2-LT _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-QLT a₁ a₂ b₁ b₂ u u₁) = updRel2-QLT _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(NUM x)} {.(NUM x)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-NUM x) = updRel2-NUM x
updRel2-renn {name} {f} {g} {r} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-IFLT _ _ _ _ _ _ _ _ (updRel2-renn n n1 n2 (¬∈++4→¬∈1 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈1 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++4→¬∈2 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈2 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁) (updRel2-renn n n1 n2 (¬∈++4→¬∈3 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈3 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₂) (updRel2-renn n n1 n2 (¬∈++4→¬∈4 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈4 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₃)
updRel2-renn {name} {f} {g} {r} {.(SUC a₁)} {.(SUC a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-SUC a₁ a₂ u) = updRel2-SUC _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(PI a₁ b₁)} {.(PI a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-PI a₁ a₂ b₁ b₂ u u₁) = updRel2-PI _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(LAMBDA a₁)} {.(LAMBDA a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-LAMBDA a₁ a₂ u) = updRel2-LAMBDA _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel2-APPLY _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(FIX a₁)} {.(FIX a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-FIX a₁ a₂ u) = updRel2-FIX _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(LET a₁ b₁)} {.(LET a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-LET a₁ a₂ b₁ b₂ u u₁) = updRel2-LET _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-SUM a₁ a₂ b₁ b₂ u u₁) = updRel2-SUM _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel2-PAIR _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel2-SPREAD _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(SET a₁ b₁)} {.(SET a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-SET a₁ a₂ b₁ b₂ u u₁) = updRel2-SET _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-ISECT a₁ a₂ b₁ b₂ u u₁) = updRel2-ISECT _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-TUNION _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-UNION a₁ a₂ b₁ b₂ u u₁) = updRel2-UNION _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel2-QTUNION _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(INL a₁)} {.(INL a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-INL a₁ a₂ u) = updRel2-INL _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(INR a₁)} {.(INR a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-INR a₁ a₂ u) = updRel2-INR _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-DECIDE _ _ _ _ _ _ (updRel2-renn n n1 n2 (¬∈++3→¬∈1 {_} {_} {names a₁} {names b₁} {names c₁} {n1} na) (¬∈++3→¬∈1 {_} {_} {names a₂} {names b₂} {names c₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++3→¬∈2 {_} {_} {names a₁} {names b₁} {names c₁} {n1} na) (¬∈++3→¬∈2 {_} {_} {names a₂} {names b₂} {names c₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁) (updRel2-renn n n1 n2 (¬∈++3→¬∈3 {_} {_} {names a₁} {names b₁} {names c₁} {n1} na) (¬∈++3→¬∈3 {_} {_} {names a₂} {names b₂} {names c₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₂)
updRel2-renn {name} {f} {g} {r} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel2-EQ _ _ _ _ _ _ (updRel2-renn n n1 n2 (¬∈++3→¬∈1 {_} {_} {names a₁} {names b₁} {names c₁} {n1} na) (¬∈++3→¬∈1 {_} {_} {names a₂} {names b₂} {names c₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++3→¬∈2 {_} {_} {names a₁} {names b₁} {names c₁} {n1} na) (¬∈++3→¬∈2 {_} {_} {names a₂} {names b₂} {names c₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁) (updRel2-renn n n1 n2 (¬∈++3→¬∈3 {_} {_} {names a₁} {names b₁} {names c₁} {n1} na) (¬∈++3→¬∈3 {_} {_} {names a₂} {names b₂} {names c₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₂)
updRel2-renn {name} {f} {g} {r} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel2-EQB _ _ _ _ _ _ _ _ (updRel2-renn n n1 n2 (¬∈++4→¬∈1 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈1 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++4→¬∈2 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈2 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁) (updRel2-renn n n1 n2 (¬∈++4→¬∈3 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈3 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₂) (updRel2-renn n n1 n2 (¬∈++4→¬∈4 {_} {_} {names a₁} {names b₁} {names c₁} {names d₁} {n1} na) (¬∈++4→¬∈4 {_} {_} {names a₂} {names b₂} {names c₂} {names d₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₃)
updRel2-renn {name} {f} {g} {r} {.AX} {.AX} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm updRel2-AX = updRel2-AX
updRel2-renn {name} {f} {g} {r} {.FREE} {.FREE} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm updRel2-FREE = updRel2-FREE
updRel2-renn {name} {f} {g} {r} {.(CS name1)} {.(CS name2)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-CS name1 name2 x x₁ x₂) with name1 ≟ n | name2 ≟ n
... | yes p | yes q rewrite p | q = updRel2-CS n1 n2 d1 d2 (inj₁ (refl , refl))
... | yes p | no q rewrite p = updRel2-CS n1 name2 d1 x₁ (⊥-elim (c x₂))
  where
    c : ¬ names∈ren n name2 r
    c i = q (sym (¬∈renₗ-names∈ren→ n name2 r i nr1)) {--(inj₁ (i , x₁ , x₂)) rewrite i = q refl
    c (inj₂ i) = nr1 (→∈renₗ n name2 r i)--}
... | no p | yes q rewrite q = updRel2-CS name1 n2 x d2 (⊥-elim (c x₂))
  where
    c : ¬ names∈ren name1 n r
    c i = p (¬∈renᵣ-names∈ren→ name1 n r i nr2) {--(inj₁ (i , x₁ , x₂)) rewrite i = p refl
    c (inj₂ i) = nr2 (→∈renᵣ name1 n r i)--}
... | no p | no q = updRel2-CS name1 name2 x x₁ (→names∈ren∷ (λ x → na (here x)) (λ x → nb (here x)) x₂)
updRel2-renn {name} {f} {g} {r} {.(NAME name1)} {.(NAME name2)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-NAME name1 name2 x x₁ x₂) with name1 ≟ n | name2 ≟ n
... | yes p | yes q rewrite p | q = updRel2-NAME n1 n2 d1 d2 (inj₁ (refl , refl)) {--(inj₂ (here refl))--}
... | yes p | no q rewrite p = updRel2-NAME n1 name2 d1 x₁ (⊥-elim (c x₂))
  where
    c : ¬ names∈ren n name2 r
    c i = q (sym (¬∈renₗ-names∈ren→ n name2 r i nr1)) {--(inj₁ (i , x₁ , x₂)) rewrite i = q refl
    c (inj₂ i) = nr1 (→∈renₗ n name2 r i)--}
... | no p | yes q rewrite q = updRel2-NAME name1 n2 x d2 (⊥-elim (c x₂))
  where
    c : ¬ names∈ren name1 n r
    c i = p (¬∈renᵣ-names∈ren→ name1 n r i nr2) {--(inj₁ (i , x₁ , x₂)) rewrite i = p refl
    c (inj₂ i) = nr2 (→∈renᵣ name1 n r i)--}
... | no p | no q = updRel2-NAME name1 name2 x x₁ (→names∈ren∷ (λ x → na (here x)) (λ x → nb (here x)) x₂)
updRel2-renn {name} {f} {g} {r} {.(FRESH a)} {.(FRESH b)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-FRESH a b u) =
  updRel2-FRESH
    _ _ (updRel2-renn {suc name} {shiftNameUp 0 f} {shiftNameUp 0 g} {sren r} {a} {b}
    (suc n) (suc n1) (suc n2)
    (λ x → na (suc→∈lowerNames {n1} {names a} x))
    (λ x → nb (suc→∈lowerNames {n2} {names b} x))
    (λ x → d1 (suc-injective x))
    (λ x → d2 (suc-injective x))
    (λ x → nr1 (suc∈renₗ-sren→ x))
    (λ x → nr2 (suc∈renᵣ-sren→ x))
    (→¬s∈names-shiftNameUp n f nf)
    (→¬s∈names-shiftNameUp n g ng)
    (λ x → nnm (suc-injective x))
    u)
updRel2-renn {name} {f} {g} {r} {.(LOAD a)} {.(LOAD a)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-LOAD a) = updRel2-LOAD _ --updRel2-LOAD _ ? -- (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel2-CHOOSE _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(TSQUASH a₁)} {.(TSQUASH a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-TSQUASH a₁ a₂ u) = updRel2-TSQUASH _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(TTRUNC a₁)} {.(TTRUNC a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-TTRUNC a₁ a₂ u) = updRel2-TTRUNC _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(TCONST a₁)} {.(TCONST a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-TCONST a₁ a₂ u) = updRel2-TCONST _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(SUBSING a₁)} {.(SUBSING a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-SUBSING a₁ a₂ u) = updRel2-SUBSING _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.PURE} {.PURE} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm updRel2-PURE = updRel2-PURE
updRel2-renn {name} {f} {g} {r} {.(DUM a₁)} {.(DUM a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-DUM a₁ a₂ u) = updRel2-DUM _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel2-FFDEFS _ _ _ _ (updRel2-renn n n1 n2 (¬∈++2→¬∈1 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈1 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u) (updRel2-renn n n1 n2 (¬∈++2→¬∈2 {_} {_} {names a₁} {names b₁} {n1} na) (¬∈++2→¬∈2 {_} {_} {names a₂} {names b₂} {n2} nb) d1 d2 nr1 nr2 nf ng nnm u₁)
updRel2-renn {name} {f} {g} {r} {.(UNIV x)} {.(UNIV x)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-UNIV x) = updRel2-UNIV _
updRel2-renn {name} {f} {g} {r} {.(LIFT a₁)} {.(LIFT a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-LIFT a₁ a₂ u) = updRel2-LIFT _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(LOWER a₁)} {.(LOWER a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-LOWER a₁ a₂ u) = updRel2-LOWER _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(SHRINK a₁)} {.(SHRINK a₂)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm (updRel2-SHRINK a₁ a₂ u) = updRel2-SHRINK _ _ (updRel2-renn n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm u)
updRel2-renn {name} {f} {g} {r} {.(upd name f)} {.(force g)} n n1 n2 na nb d1 d2 nr1 nr2 nf ng nnm updRel2-upd with name ≟ n
... | yes p rewrite p | renn¬∈ n n1 (shiftUp 0 f) (→¬∈names-shiftUp {n} {0} {f} nf) | renn¬∈ n n2 g ng = ⊥-elim (nnm refl)
... | no p rewrite renn¬∈ n n1 (shiftUp 0 f) (→¬∈names-shiftUp {n} {0} {f} nf) | renn¬∈ n n2 g ng = updRel2-upd



{--
step-upto𝕎 : (cc : ContConds) (name : Name) (a b : Term) (w1 w2 w1' : 𝕎·) (r : ren)
               → ¬ name ∈ names a
               → ¬ name ∈ names𝕎· w1
               → name ∈ dom𝕎· w1
               → step a w1 ≡ just (b , w2)
               → upto𝕎 name w1 w1' r
               → Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (b , w2')
                   × upto𝕎 name w2 w2' r' -- we'll probably need to know that r' extends r
                   × ¬ name ∈ names b
                   × ¬ name ∈ names𝕎· w2
                   × name ∈ dom𝕎· w2))
step-upto𝕎 cc name NAT b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name QNAT b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name TNAT b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LT a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (QLT a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (NUM x) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (IFLT a a₁ a₂ a₃) b w1 w2 w1' r nna nnw idom comp upw with is-NUM a
... | inj₁ (n , p) rewrite p with is-NUM a₁
... |    inj₁ (m , q) rewrite q with n <? m
... |       yes xr rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw , ¬∈++2→¬∈1 {_} {_} {names a₂} {names a₃} {name} nna , nnw , idom
... |       no xr rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw , ¬∈++2→¬∈2 {_} {_} {names a₂} {names a₃} {name} nna , nnw , idom
step-upto𝕎 cc name (IFLT a a₁ a₂ a₃) b w1 w2 w1' r nna nnw idom comp upw | inj₁ (n , p) | inj₂ q with step⊎ a₁ w1
... |       inj₁ (a₁' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                       | fst (snd (snd (step-upto𝕎 cc name a₁ a₁' w1 w1x w1' r (¬∈++3→¬∈1 {_} {_} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    (λ x → nna (¬∈1→∈++3 {_} {_} {names a₁} {names a₂} {names a₃} {names a₁'} (fst (snd (snd (snd (snd ind))))) x)) ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a₁ w1' ≡ just (a₁' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a₁'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a₁ a₁' w1 w1x w1' r (¬∈++3→¬∈1 {_} {_} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (IFLT a a₁ a₂ a₃) b w1 w2 w1' r nna nnw idom comp upw | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (snd (step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++4→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    (λ x → nna (¬∈1→∈++4 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {names a'} (fst (snd (snd (snd (snd ind))))) x)) ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++4→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {names a₃} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (SUC a) b w1 w2 w1' r nna nnw idom comp upw with is-NUM a
... | inj₁ (n , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw , ¬∈[] {Name} {name} , nnw , idom
... | inj₂ p with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (snd (step-upto𝕎 cc name a a' w1 w1x w1' r nna nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    fst (snd (snd (snd (snd ind)))) ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a a' w1 w1x w1' r nna nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (PI a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LAMBDA a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (APPLY f a) b w1 w2 w1' r nna nnw idom comp upw with is-LAM f
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw , ¬∈names-sub {name} {a} {t} (λ x → nna (∈-++⁺ʳ (names t) x)) (λ x → nna (∈-++⁺ˡ x)) , nnw , idom
... | inj₂ x with is-CS f
... |    inj₁ (name' , p) rewrite p with is-NUM a
... |       inj₁ (n , q) rewrite q with getT⊎ n name' w1
... |          inj₁ (y , xr) rewrite xr | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' ,
  {!!} ,
  {!!} , --getT≡→map-getT≡ (λ z → nna (here (sym z))) upw r ,
  upw ,
  (λ iy → nnw (ContConds.ccGnames cc name name' n y w1 xr iy)) ,
  nnw , idom
... |          inj₂ xr rewrite xr = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (APPLY f a) b w1 w2 w1' r nna nnw idom comp upw | inj₂ x | inj₁ (name' , p) | inj₂ y with step⊎ a w1
... |          inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                         | fst (snd (snd (step-upto𝕎 cc name a a' w1 w1x w1' r (λ z → nna (there z)) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl ,
    fst (snd (snd (snd ind))) ,
    (λ { (here z) → nna (here z) ; (there z) → fst (snd (snd (snd (snd ind)))) z }) ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a a' w1 w1x w1' r (λ z → nna (there z)) nnw idom z upw
... |          inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (APPLY f a) b w1 w2 w1' r nna nnw idom comp upw | inj₂ x | inj₂ y with step⊎ f w1
... | inj₁ (f' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                | fst (snd (snd (step-upto𝕎 cc name f f' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names f} {names a} {name} nna) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    (→¬∈++2 {_} {_} {name} {names f} {names a} {names f'} {names a} (λ x → fst (snd (snd (snd (snd ind))))) (λ x → x) nna) ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step f w1' ≡ just (f' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names f'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name f f' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names f} {names a} {name} nna) nnw idom z upw
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (FIX a) b w1 w2 w1' r nna nnw idom comp upw with is-LAM a
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw , ¬∈names-sub {name} {FIX (LAMBDA t)} {t} nna nna , nnw , idom
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (snd (step-upto𝕎 cc name a a' w1 w1x w1' r nna nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    fst (snd (snd (snd (snd ind)))) ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a a' w1 w1x w1' r nna nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (LET a a₁) b w1 w2 w1' r nna nnw idom comp upw with isValue⊎ a
... | inj₁ x rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw ,
  ¬∈names-sub {name} {a} {a₁} (λ x → nna (∈-++⁺ˡ x)) (λ x → nna (∈-++⁺ʳ (names a) x)) ,
  nnw , idom
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (snd (step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    →¬∈++2 {_} {_} {name} {names a} {names a₁} {names a'} {names a₁} (λ x → fst (snd (snd (snd (snd ind))))) (λ x → x) nna ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (SUM a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (PAIR a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (SPREAD a a₁) b w1 w2 w1' r nna nnw idom comp upw with is-PAIR a
... | inj₁ (u , v , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw ,
  ¬∈names-sub {name} {v} {sub u a₁} (λ x → nna (∈-++⁺ˡ (∈-++⁺ʳ (names u) x))) (¬∈names-sub {name} {u} {a₁} (λ x → nna (∈-++⁺ˡ (∈-++⁺ˡ x))) (λ x → nna (∈-++⁺ʳ (names u ++ names v) x))) ,
  nnw , idom
... | inj₂ x with step⊎ a w1
... |    inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                   | fst (snd (snd (step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    →¬∈++2 {_} {_} {name} {names a} {names a₁} {names a'} {names a₁} (λ x → fst (snd (snd (snd (snd ind))))) (λ x → x) nna ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names a} {names a₁} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (SET a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (TUNION a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (ISECT a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (UNION a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (QTUNION a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (INL a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (INR a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (DECIDE a a₁ a₂) b w1 w2 w1' r nna nnw idom comp upw with is-INL a
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw , ¬∈names-sub {name} {t} {a₁} (λ x → nna (∈-++⁺ˡ x)) (λ x → nna (∈-++⁺ʳ (names t) (∈-++⁺ˡ x))) , nnw , idom
... | inj₂ x with is-INR a
... |    inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  w1' , r , refl , upw , ¬∈names-sub {name} {t} {a₂} (λ x → nna (∈-++⁺ˡ x)) (λ x → nna (∈-++⁺ʳ (names t) (∈-++⁺ʳ (names a₁) x))) , nnw , idom
... |    inj₂ y with step⊎ a w1
... |       inj₁ (a' , w1x , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp))
                                      | fst (snd (snd (step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {name} nna) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    →¬∈++3 {_} {_} {name} {names a} {names a₁} {names a₂} {names a'} {names a₁} {names a₂} (λ x → fst (snd (snd (snd (snd ind))))) (λ x → x) (λ x → x) nna ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step a w1' ≡ just (a' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names a'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name a a' w1 w1x w1' r (¬∈++3→¬∈1 {_} {_} {names a} {names a₁} {names a₂} {name} nna) nnw idom z upw
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (EQ a a₁ a₂) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (EQB a a₁ a₂ a₃) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name AX b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name FREE b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (CS x) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (NAME x) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (FRESH a) b w1 w2 w1' r nna nnw idom comp upw rewrite sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  concl
  where
    concl : Σ 𝕎· (λ w2' → Σ ren (λ r' → just (fresh-inst w1' a , startNewChoiceT Res⊤ w1' a) ≡ just (fresh-inst w1 a , w2')
                   × upto𝕎 name (startNewChoiceT Res⊤ w1 a) w2' r'
                   × ¬ name ∈ names (fresh-inst w1 a)
                   × ¬ name ∈ names𝕎· (startNewChoiceT Res⊤ w1 a)
                   × name ∈ dom𝕎· (startNewChoiceT Res⊤ w1 a)))
    concl = startNewChoiceT Res⊤ w1' a ,
            {!!} ,
            {!!} , --≡just (≡pair (upto𝕎→≡fresh-inst a (upto𝕎-sym _ _ _ upw)) refl) ,
            {!!} , --→upto𝕎-startNewChoiceT cc a upw ,
            (λ x → nna (suc→∈lowerNames (∈names-shiftNameDown-renn→ name (newChoiceT+ w1 a) a (_≤_.s≤s _≤_.z≤n) (∈dom𝕎→¬≡newChoiceT+ name w1 a idom) x))) ,
            (λ x → nnw (∈names𝕎-startNewChoiceT→ cc name w1 a x)) ,
            ContConds.ccDstart cc name w1 a idom
step-upto𝕎 cc name (CHOOSE n t) b w1 w2 w1' r nna nnw idom comp upw with is-NAME n
... | inj₁ (name' , p) rewrite p | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp)) =
  chooseT name' w1' t ,
  {!!} , --
  refl ,
  {!!} , --upto𝕎-chooseT cc name name' w1 w1' t upw ,
  (λ ()) ,
  (λ x → nnw (names𝕎-chooseT→ cc name name' w1 t x)) ,
  dom𝕎-chooseT cc name name' w1 t idom
... | inj₂ x with step⊎ n w1
... |    inj₁ (n' , w1x , z) rewrite z | sym (pair-inj₁ (just-inj comp)) | sym (pair-inj₂ (just-inj comp))
                                   | fst (snd (snd (step-upto𝕎 cc name n n' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names n} {names t} {name} nna) nnw idom z upw)))
  = fst ind , fst (snd ind) , refl , fst (snd (snd (snd ind))) ,
    →¬∈++2 {_} {_} {name} {names n} {names t} {names n'} {names t} (λ x → fst (snd (snd (snd (snd ind))))) (λ x → x) nna ,
    snd (snd (snd (snd (snd ind))))
  where
    ind : Σ 𝕎· (λ w2' → Σ ren (λ r' → step n w1' ≡ just (n' , w2')
                   × upto𝕎 name w1x w2' r'
                   × ¬ name ∈ names n'
                   × ¬ name ∈ names𝕎· w1x
                   × name ∈ dom𝕎· w1x))
    ind = step-upto𝕎 cc name n n' w1 w1x w1' r (¬∈++2→¬∈1 {_} {_} {names n} {names t} {name} nna) nnw idom z upw
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-upto𝕎 cc name (TSQUASH a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (TTRUNC a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (TCONST a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (SUBSING a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (DUM a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (FFDEFS a a₁) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name PURE b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (UNIV x) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LIFT a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (LOWER a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom
step-upto𝕎 cc name (SHRINK a) b w1 w2 w1' r nna nnw idom comp upw rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = w1' , r , refl , upw , nna , nnw , idom



steps-upto𝕎 : (cc : ContConds) (name : Name) (k : ℕ) (a b : Term) (w1 w2 w1' : 𝕎·) (r : ren)
               → ¬ name ∈ names a
               → ¬ name ∈ names𝕎· w1
               → name ∈ dom𝕎· w1
               → steps k (a , w1) ≡ (b , w2)
               → upto𝕎 name w1 w1' r
               → Σ ℕ (λ k' → Σ 𝕎· (λ w2' → Σ ren (λ r' → steps k' (a , w1') ≡ (b , w2')
                   × upto𝕎 name w2 w2' r'
                   × ¬ name ∈ names b
                   × ¬ name ∈ names𝕎· w2
                   × name ∈ dom𝕎· w2)))
steps-upto𝕎 cc name 0 a b w1 w2 w1' r nna nnw idom comp upw
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , w1' , r , refl , upw , nna , nnw , idom
steps-upto𝕎 cc name (suc k) a b w1 w2 w1' r nna nnw idom comp upw with step⊎ a w1
... | inj₁ (a' , w1x , z) rewrite z =
  suc (fst h2) , fst (snd h2) , fst (snd (snd h2)) ,
  step-steps-trans {w1'} {fst h1} {fst (snd h2)} {a} {a'} {b} (fst (snd (snd h1))) (fst (snd (snd (snd h2)))) ,
  snd (snd (snd (snd h2)))
  where
    h1 : Σ 𝕎· (λ w1x' → Σ ren (λ r' → step a w1' ≡ just (a' , w1x')
           × upto𝕎 name w1x w1x' r'
           × ¬ name ∈ names a'
           × ¬ name ∈ names𝕎· w1x
           × name ∈ dom𝕎· w1x))
    h1 = step-upto𝕎 cc name a a' w1 w1x w1' r nna nnw idom z upw

    h2 : Σ ℕ (λ k' → Σ 𝕎· (λ w2' → Σ ren (λ r' → steps k' (a' , fst h1) ≡ (b , w2')
           × upto𝕎 name w2 w2' r'
           × ¬ name ∈ names b
           × ¬ name ∈ names𝕎· w2
           × name ∈ dom𝕎· w2)))
    h2 = steps-upto𝕎
           cc name k a' b w1x w2 (fst h1) {!!} (fst (snd (snd (snd (snd h1)))))
           (fst (snd (snd (snd (snd (snd h1))))))
           (snd (snd (snd (snd (snd (snd h1))))))
           comp
           (fst (snd (snd (snd h1))))
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , w1' , r , refl , upw , nna , nnw , idom
--}

\end{code}
