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
--open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
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


module continuity4 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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

open import continuity(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(V)(F)(E)(CB)



data updRel (name : Name) (f g : Term) : Term → Term → Set where
  updRel-VAR     : (x : Var) → updRel name f g (VAR x) (VAR x)
  updRel-NAT     : updRel name f g NAT NAT
  updRel-QNAT    : updRel name f g QNAT QNAT
  updRel-LT      : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (LT a₁ b₁) (LT a₂ b₂)
  updRel-QLT     : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (QLT a₁ b₁) (QLT a₂ b₂)
  updRel-NUM     : (x : ℕ) → updRel name f g (NUM x) (NUM x)
  updRel-IFLT    : (a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g c₁ c₂ → updRel name f g d₁ d₂ → updRel name f g (IFLT a₁ b₁ c₁ d₁) (IFLT a₂ b₂ c₂ d₂)
  updRel-SUC     : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (SUC a₁) (SUC a₂)
  updRel-PI      : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (PI a₁ b₁) (PI a₂ b₂)
  updRel-LAMBDA  : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (LAMBDA a₁) (LAMBDA a₂)
  updRel-APPLY   : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (APPLY a₁ b₁) (APPLY a₂ b₂)
  updRel-FIX     : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (FIX a₁) (FIX a₂)
  updRel-LET     : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (LET a₁ b₁) (LET a₂ b₂)
  updRel-SUM     : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (SUM a₁ b₁) (SUM a₂ b₂)
  updRel-PAIR    : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (PAIR a₁ b₁) (PAIR a₂ b₂)
  updRel-SPREAD  : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (SPREAD a₁ b₁) (SPREAD a₂ b₂)
  updRel-SET     : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (SET a₁ b₁) (SET a₂ b₂)
  updRel-TUNION  : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (TUNION a₁ b₁) (TUNION a₂ b₂)
  updRel-UNION   : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (UNION a₁ b₁) (UNION a₂ b₂)
  updRel-QTUNION : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (QTUNION a₁ b₁) (QTUNION a₂ b₂)
  updRel-INL     : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (INL a₁) (INL a₂)
  updRel-INR     : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (INR a₁) (INR a₂)
  updRel-DECIDE  : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g c₁ c₂ → updRel name f g (DECIDE a₁ b₁ c₁) (DECIDE a₂ b₂ c₂)
  updRel-EQ      : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g c₁ c₂ → updRel name f g (EQ a₁ b₁ c₁) (EQ a₂ b₂ c₂)
  updRel-AX      : updRel name f g AX AX
  updRel-FREE    : updRel name f g FREE FREE
  --updRel-CS      : updRel name1 name2 f (CS name1) (CS name2)
  --updRel-CS      : updRel name1 name2 f (CS name1) (CS name2)
  --updRel-NAME    : updRel name1 name2 f (NAME name1) (NAME name2)
  --updRel-FRESH   : (a b : Term) → updRel name1 name2 f a b → updRel name1 name2 f (FRESH a) (FRESH b)
  updRel-CHOOSE  : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (CHOOSE a₁ b₁) (CHOOSE a₂ b₂)
--  updRel-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updRel name1 name2 f a₁ a₂ → updRel name1 name2 f b₁ b₂ → updRel name1 name2 f c₁ c₂ → updRel name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  updRel-TSQUASH : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (TSQUASH a₁) (TSQUASH a₂)
  updRel-TTRUNC  : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (TTRUNC a₁) (TTRUNC a₂)
  updRel-TCONST  : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (TCONST a₁) (TCONST a₂)
  updRel-SUBSING : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (SUBSING a₁) (SUBSING a₂)
  updRel-DUM     : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (DUM a₁) (DUM a₂)
  updRel-FFDEFS  : (a₁ a₂ b₁ b₂ : Term) → updRel name f g a₁ a₂ → updRel name f g b₁ b₂ → updRel name f g (FFDEFS a₁ b₁) (FFDEFS a₂ b₂)
  updRel-UNIV    : (x : ℕ) → updRel name f g (UNIV x) (UNIV x)
  updRel-LIFT    : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (LIFT a₁) (LIFT a₂)
  updRel-LOWER   : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (LOWER a₁) (LOWER a₂)
  updRel-SHRINK  : (a₁ a₂ : Term) → updRel name f g a₁ a₂ → updRel name f g (SHRINK a₁) (SHRINK a₂)
  updRel-upd     : updRel name f g (upd name f) (force g)



presUpdRel : (n : ℕ) (name : Name) (f g : Term) (k : ℕ) → Set(lsuc L)
presUpdRel n name f g k =
  {a b v : Term} {w1 w2 w : 𝕎·}
  → updRel name f g a b
  → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n → strongMonEq w' (APPLY f (NUM k)) (APPLY g (NUM k)))
  → (comp : steps k (a , w1) ≡ (v , w2))
  → isHighestℕ {k} {w1} {w2} {a} {v} n name comp
  → isValue v
  → Σ ℕ (λ k' → Σ Term (λ v' → steps k' (b , w) ≡ (v' , w) × updRel name f g v v'))


stepsPresUpdRel : (n : ℕ) (name : Name) (f g : Term) (b : Term) (w : 𝕎·) → Set(lsuc L)
stepsPresUpdRel n name f g b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    Σ (steps k (b , w) ≡ (v , w')) (λ comp →
    isValue v
    × isHighestℕ {k} {w} {w'} {b} {v} n name comp
    × ((k' : ℕ) → k' ≤ k → presUpdRel n name f g k')))))


updRel-NUMₗ→ : {name : Name} {f g : Term} {n : ℕ} {a : Term}
               → updRel name f g (NUM n) a
               → a ≡ NUM n
updRel-NUMₗ→ {name} {f} {g} {n} {.(NUM n)} (updRel-NUM .n) = refl


ΣstepsUpdRel : (name : Name) (f g : Term) (x : Term) (w2 : 𝕎·) (b : Term)  (w : 𝕎·) → Set(L)
ΣstepsUpdRel name f g x w2 b w =
  Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ Term (λ y1 → Σ Term (λ y2 → Σ 𝕎· (λ w3 →
    steps k1 (x , w2) ≡ (y1 , w3)
    × steps k2 (b , w) ≡ (y2 , w)
    × updRel name f g y1 y2)))))



isHighestℕ-IFLT₁→ : {n : ℕ} {k : ℕ} {name : Name} {f g : Term} {a b c d v : Term} {w w' : 𝕎·}
                      → (comp : steps k (IFLT a b c d , w) ≡ (v , w'))
                      → isValue v
                      → isHighestℕ {k} {w} {w'} {IFLT a b c d} {v} n name comp
                      → Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × isValue u
                          × k' < k))))
isHighestℕ-IFLT₁→ {n} {0} {name} {f} {g} {a} {b} {c} {d} {v} {w} {w'} comp isv h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
isHighestℕ-IFLT₁→ {n} {suc k} {name} {f} {g} {a} {b} {c} {d} {v} {w} {w'} comp isv h with is-NUM a
... | inj₁ (i1 , p) rewrite p with is-NUM b
... |    inj₁ (i2 , q) rewrite q with i1 <? i2
... |       yes r = 0 , NUM i1 , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n
... |       no r = 0 , NUM i1 , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ-IFLT₁→ {n} {suc k} {name} {f} {g} {a} {b} {c} {d} {v} {w} {w'} comp isv h | inj₁ (i1 , p) | inj₂ q with step⊎ b w
... |       inj₁ (b' , w0 , z) rewrite z = 0 , NUM i1 , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n --ret (IFLT a b' c d) w'
... |       inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
isHighestℕ-IFLT₁→ {n} {suc k} {name} {f} {g} {a} {b} {c} {d} {v} {w} {w'} comp isv h | inj₂ p with step⊎ a w
... |    inj₁ (a0 , w0 , z) rewrite z =
  suc (fst ind) , concl
  where
    ind : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a0 , w0) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w0} {w''} {a0} {u} n name comp'
                          × isValue u
                          × k' < k))))
    ind = isHighestℕ-IFLT₁→ {n} {k} {name} {f} {g} {a0} {b} {c} {d} {v} {w0} {w'} comp isv (snd h)

    concl : Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps (suc (fst ind)) (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {suc (fst ind)} {w} {w''} {a} {u} n name comp'
                          × isValue u
                          × suc (fst ind) < suc k)))
    concl rewrite z =
      fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
      (fst h , fst (snd (snd (snd (snd ind))))) ,
      fst (snd (snd (snd (snd (snd ind))))) ,
      _≤_.s≤s (snd (snd (snd (snd (snd (snd ind))))))
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



stepsPresUpdRel-IFLT₁→ : {n : ℕ} {name : Name} {f g : Term} {a b c d : Term} {w : 𝕎·}
                          → stepsPresUpdRel n name f g (IFLT a b c d) w
                          → stepsPresUpdRel n name f g a w
stepsPresUpdRel-IFLT₁→ {n} {name} {f} {g} {a} {b} {c} {d} {w} (k , v , w' , comp , isv , ish , ind) =
  fst hv , fst (snd hv) , fst (snd (snd hv)) , fst (snd (snd (snd hv))) ,
  fst (snd (snd (snd (snd (snd hv))))) , fst (snd (snd (snd (snd hv)))) ,
  λ k' j → ind k' (<⇒≤ (<-transʳ j (snd (snd (snd (snd (snd (snd hv))))))))
  where
    hv : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × isValue u
                          × k' < k))))
    hv = isHighestℕ-IFLT₁→ {n} {k} {name} {f} {g} {a} {b} {c} {d} {v} {w} {w'} comp isv ish



isHighestℕ-IFLT₂→ : {n : ℕ} {k : ℕ} {name : Name} {f g : Term} {m : ℕ} {b c d v : Term} {w w' : 𝕎·}
                      → (comp : steps k (IFLT (NUM m) b c d , w) ≡ (v , w'))
                      → isValue v
                      → isHighestℕ {k} {w} {w'} {IFLT (NUM m) b c d} {v} n name comp
                      → Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {b} {u} n name comp'
                          × isValue u
                          × k' < k))))
isHighestℕ-IFLT₂→ {n} {0} {name} {f} {g} {m} {b} {c} {d} {v} {w} {w'} comp isv h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
isHighestℕ-IFLT₂→ {n} {suc k} {name} {f} {g} {m} {b} {c} {d} {v} {w} {w'} comp isv h with is-NUM b
... | inj₁ (m' , q) rewrite q with m <? m'
... |    yes r = 0 , NUM m' , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n
... |    no r = 0 , NUM m' , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ-IFLT₂→ {n} {suc k} {name} {f} {g} {m} {b} {c} {d} {v} {w} {w'} comp isv h | inj₂ q with step⊎ b w
... |    inj₁ (b0 , w0 , z) rewrite z =
  suc (fst ind) , concl
  where
    ind : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b0 , w0) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w0} {w''} {b0} {u} n name comp'
                          × isValue u
                          × k' < k))))
    ind = isHighestℕ-IFLT₂→ {n} {k} {name} {f} {g} {m} {b0} {c} {d} {v} {w0} {w'} comp isv (snd h)

    concl : Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps (suc (fst ind)) (b , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {suc (fst ind)} {w} {w''} {b} {u} n name comp'
                          × isValue u
                          × suc (fst ind) < suc k)))
    concl rewrite z =
      fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
      (fst h , fst (snd (snd (snd (snd ind))))) ,
      fst (snd (snd (snd (snd (snd ind))))) ,
      _≤_.s≤s (snd (snd (snd (snd (snd (snd ind))))))
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



stepsPresUpdRel-IFLT₂→ : {n : ℕ} {name : Name} {f g : Term} {m : ℕ} {b c d : Term} {w : 𝕎·}
                          → stepsPresUpdRel n name f g (IFLT (NUM m) b c d) w
                          → stepsPresUpdRel n name f g b w
stepsPresUpdRel-IFLT₂→ {n} {name} {f} {g} {m} {b} {c} {d} {w} (k , v , w' , comp , isv , ish , ind) =
  fst hv , fst (snd hv) , fst (snd (snd hv)) , fst (snd (snd (snd hv))) ,
  fst (snd (snd (snd (snd (snd hv))))) , fst (snd (snd (snd (snd hv)))) ,
  λ k' j → ind k' (<⇒≤ (<-transʳ j (snd (snd (snd (snd (snd (snd hv))))))))
  where
    hv : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (b , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {b} {u} n name comp'
                          × isValue u
                          × k' < k))))
    hv = isHighestℕ-IFLT₂→ {n} {k} {name} {f} {g} {m} {b} {c} {d} {v} {w} {w'} comp isv ish



→ΣstepsUpdRel-IFLT₂ : {name : Name} {f g : Term} {m : ℕ} {b₁ b₂ c₁ c₂ d₁ d₂ : Term} {w1 w : 𝕎·}
                       → updRel name f g c₁ c₂
                       → updRel name f g d₁ d₂
                       → ΣstepsUpdRel name f g b₁ w1 b₂ w
                       → ΣstepsUpdRel name f g (IFLT (NUM m) b₁ c₁ d₁) w1 (IFLT (NUM m) b₂ c₂ d₂) w
→ΣstepsUpdRel-IFLT₂ {name} {f} {g} {m} {b₁} {b₂} {c₁} {c₂} {d₁} {d₂} {w1} {w} updc updd (k1 , k2 , y1 , y2 , w3 , comp1 , comp2 , r) =
  fst comp1' , fst comp2' , IFLT (NUM m) y1 c₁ d₁ , IFLT (NUM m) y2 c₂ d₂ , w3 , snd comp1' , snd comp2' ,
  updRel-IFLT _ _ _ _ _ _ _ _ (updRel-NUM m) r updc updd
  where
    comp1' : IFLT (NUM m) b₁ c₁ d₁ ⇓ IFLT (NUM m) y1 c₁ d₁ from w1 to w3
    comp1' = IFLT-NUM-2nd⇓steps k1 m c₁ d₁ comp1

    comp2' : IFLT (NUM m) b₂ c₂ d₂ ⇓ IFLT (NUM m) y2 c₂ d₂ from w to w
    comp2' = IFLT-NUM-2nd⇓steps k2 m c₂ d₂ comp2



→ΣstepsUpdRel-IFLT₁ : {name : Name} {f g : Term} {a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : Term} {w1 w : 𝕎·}
                       → updRel name f g b₁ b₂
                       → updRel name f g c₁ c₂
                       → updRel name f g d₁ d₂
                       → ΣstepsUpdRel name f g a₁ w1 a₂ w
                       → ΣstepsUpdRel name f g (IFLT a₁ b₁ c₁ d₁) w1 (IFLT a₂ b₂ c₂ d₂) w
→ΣstepsUpdRel-IFLT₁ {name} {f} {g} {a₁} {a₂} {b₁} {b₂} {c₁} {c₂} {d₁} {d₂} {w1} {w} updb updc updd (k1 , k2 , y1 , y2 , w3 , comp1 , comp2 , r) =
  fst comp1' , fst comp2' , IFLT y1 b₁ c₁ d₁ , IFLT y2 b₂ c₂ d₂ , w3 , snd comp1' , snd comp2' ,
  updRel-IFLT _ _ _ _ _ _ _ _ r updb updc updd
  where
    comp1' : IFLT a₁ b₁ c₁ d₁ ⇓ IFLT y1 b₁ c₁ d₁ from w1 to w3
    comp1' = IFLT-NUM-1st⇓steps k1 b₁ c₁ d₁ comp1

    comp2' : IFLT a₂ b₂ c₂ d₂ ⇓ IFLT y2 b₂ c₂ d₂ from w to w
    comp2' = IFLT-NUM-1st⇓steps k2 b₂ c₂ d₂ comp2



updRel-CSₗ→ : {name : Name} {f g : Term} {n : Name} {a : Term}
              → updRel name f g (CS n) a
              → ⊥
updRel-CSₗ→ {name} {f} {g} {n} {a} ()



updRel-NAMEₗ→ : {name : Name} {f g : Term} {n : Name} {a : Term}
                → updRel name f g (NAME n) a
                → ⊥
updRel-NAMEₗ→ {name} {f} {g} {n} {a} ()



updRel-LAMBDAₗ→ : {name : Name} {f g : Term} {t : Term} {a : Term}
                  → updRel name f g (LAMBDA t) a
                  → Σ Term (λ u → a ≡ LAMBDA u × updRel name f g t u)
                     ⊎ (t ≡ updBody name f × a ≡ force g)
updRel-LAMBDAₗ→ {name} {f} {g} {t} {.(LAMBDA a₂)} (updRel-LAMBDA .t a₂ u) = inj₁ (a₂ , refl , u)
updRel-LAMBDAₗ→ {name} {f} {g} {.(updBody name f)} {.(force g)} updRel-upd = inj₂ (refl , refl)




isHighestℕ-APPLY₁→ : {n : ℕ} {k : ℕ} {name : Name} {f g : Term} {a b v : Term} {w w' : 𝕎·}
                      → (comp : steps k (APPLY a b , w) ≡ (v , w'))
                      → isValue v
                      → isHighestℕ {k} {w} {w'} {APPLY a b} {v} n name comp
                      → Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × isValue u
                          × k' < k))))
isHighestℕ-APPLY₁→ {n} {0} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
isHighestℕ-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h with is-LAM a
... | inj₁ (t , p) rewrite p = 0 , LAMBDA t , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n
... | inj₂ x with is-CS a
... |    inj₁ (name' , q) rewrite q with is-NUM b
... |       inj₁ (j , r) rewrite r with getT j name' w
... |          just t = 0 , CS name' , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n
... |          nothing = 0 , CS name' , w , refl , h , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h | inj₂ x | inj₁ (name' , q) | inj₂ r with step⊎ b w
... |          inj₁ (b0 , w0 , z) rewrite z = 0 , CS name' , w , refl , fst h , tt , _≤_.s≤s _≤_.z≤n
... |          inj₂ z rewrite z = 0 , CS name' , w , refl , h , tt , _≤_.s≤s _≤_.z≤n
isHighestℕ-APPLY₁→ {n} {suc k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv h | inj₂ x | inj₂ y with step⊎ a w
... |    inj₁ (a0 , w0 , z) rewrite z =
  suc (fst ind) , concl
  where
    ind : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a0 , w0) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w0} {w''} {a0} {u} n name comp'
                          × isValue u
                          × k' < k))))
    ind = isHighestℕ-APPLY₁→ {n} {k} {name} {f} {g} {a0} {b} {v} {w0} {w'} comp isv (snd h)

    concl : Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps (suc (fst ind)) (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {suc (fst ind)} {w} {w''} {a} {u} n name comp'
                          × isValue u
                          × suc (fst ind) < suc k)))
    concl rewrite z =
      fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
      (fst h , fst (snd (snd (snd (snd ind))))) ,
      fst (snd (snd (snd (snd (snd ind))))) ,
      _≤_.s≤s (snd (snd (snd (snd (snd (snd ind))))))
... |    inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv



stepsPresUpdRel-APPLY₁→ : {n : ℕ} {name : Name} {f g : Term} {a b : Term} {w : 𝕎·}
                           → stepsPresUpdRel n name f g (APPLY a b) w
                           → stepsPresUpdRel n name f g a w
stepsPresUpdRel-APPLY₁→ {n} {name} {f} {g} {a} {b} {w} (k , v , w' , comp , isv , ish , ind) =
  fst hv , fst (snd hv) , fst (snd (snd hv)) , fst (snd (snd (snd hv))) ,
  fst (snd (snd (snd (snd (snd hv))))) , fst (snd (snd (snd (snd hv)))) ,
  λ k' j → ind k' (<⇒≤ (<-transʳ j (snd (snd (snd (snd (snd (snd hv))))))))
  where
    hv : Σ ℕ (λ k' → Σ Term (λ u → Σ 𝕎· (λ w'' → Σ (steps k' (a , w) ≡ (u , w'')) (λ comp' →
                          isHighestℕ {k'} {w} {w''} {a} {u} n name comp'
                          × isValue u
                          × k' < k))))
    hv = isHighestℕ-APPLY₁→ {n} {k} {name} {f} {g} {a} {b} {v} {w} {w'} comp isv ish



→ΣstepsUpdRel-APPLY₁ : {name : Name} {f g : Term} {a₁ a₂ b₁ b₂ : Term} {w1 w : 𝕎·}
                        → updRel name f g b₁ b₂
                        → ΣstepsUpdRel name f g a₁ w1 a₂ w
                        → ΣstepsUpdRel name f g (APPLY a₁ b₁) w1 (APPLY a₂ b₂) w
→ΣstepsUpdRel-APPLY₁ {name} {f} {g} {a₁} {a₂} {b₁} {b₂} {w1} {w} updb (k1 , k2 , y1 , y2 , w3 , comp1 , comp2 , r) =
  fst comp1' , fst comp2' , APPLY y1 b₁ , APPLY y2 b₂ , w3 , snd comp1' , snd comp2' ,
  updRel-APPLY _ _ _ _ r updb
  where
    comp1' : APPLY a₁ b₁ ⇓ APPLY y1 b₁ from w1 to w3
    comp1' = →steps-APPLY b₁ k1 comp1

    comp2' : APPLY a₂ b₂ ⇓ APPLY y2 b₂ from w to w
    comp2' = →steps-APPLY b₂ k2 comp2



updRel-shiftUp : (n : ℕ) {name : Name} {f g : Term} (cf : # f) (cg : # g) {a b : Term}
                 → updRel name f g a b
                 → updRel name f g (shiftUp n a) (shiftUp n b)
updRel-shiftUp n {name} {f} {g} cf cg {.(VAR x)} {.(VAR x)} (updRel-VAR x) = updRel-VAR _
updRel-shiftUp n {name} {f} {g} cf cg {.NAT} {.NAT} updRel-NAT = updRel-NAT
updRel-shiftUp n {name} {f} {g} cf cg {.QNAT} {.QNAT} updRel-QNAT = updRel-QNAT
updRel-shiftUp n {name} {f} {g} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel-LT a₁ a₂ b₁ b₂ u u₁) = updRel-LT _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel-QLT a₁ a₂ b₁ b₂ u u₁) = updRel-QLT _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(NUM x)} {.(NUM x)} (updRel-NUM x) = updRel-NUM _
updRel-shiftUp n {name} {f} {g} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel-IFLT _ _ _ _ _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁) (updRel-shiftUp n cf cg u₂) (updRel-shiftUp n cf cg u₃)
updRel-shiftUp n {name} {f} {g} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel-SUC a₁ a₂ u) = updRel-SUC _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel-PI a₁ a₂ b₁ b₂ u u₁) = updRel-PI _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp (suc n) cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel-LAMBDA a₁ a₂ u) = updRel-LAMBDA _ _ (updRel-shiftUp (suc n) cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel-APPLY _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel-FIX a₁ a₂ u) = updRel-FIX _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel-LET a₁ a₂ b₁ b₂ u u₁) = updRel-LET _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp (suc n) cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel-SUM a₁ a₂ b₁ b₂ u u₁) = updRel-SUM _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp (suc n) cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel-PAIR _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel-SPREAD _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp (suc (suc n)) cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel-SET a₁ a₂ b₁ b₂ u u₁) = updRel-SET _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp (suc n) cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel-TUNION _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp (suc n) cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel-UNION a₁ a₂ b₁ b₂ u u₁) = updRel-UNION _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel-QTUNION _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(INL a₁)} {.(INL a₂)} (updRel-INL a₁ a₂ u) = updRel-INL _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(INR a₁)} {.(INR a₂)} (updRel-INR a₁ a₂ u) = updRel-INR _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel-DECIDE _ _ _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp (suc n) cf cg u₁) (updRel-shiftUp (suc n) cf cg u₂)
updRel-shiftUp n {name} {f} {g} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel-EQ _ _ _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁) (updRel-shiftUp n cf cg u₂)
updRel-shiftUp n {name} {f} {g} cf cg {.AX} {.AX} updRel-AX = updRel-AX
updRel-shiftUp n {name} {f} {g} cf cg {.FREE} {.FREE} updRel-FREE = updRel-FREE
updRel-shiftUp n {name} {f} {g} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel-CHOOSE _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel-TSQUASH a₁ a₂ u) = updRel-TSQUASH _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel-TTRUNC a₁ a₂ u) = updRel-TTRUNC _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel-TCONST a₁ a₂ u) = updRel-TCONST _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel-SUBSING a₁ a₂ u) = updRel-SUBSING _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel-DUM a₁ a₂ u) = updRel-DUM _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel-FFDEFS _ _ _ _ (updRel-shiftUp n cf cg u) (updRel-shiftUp n cf cg u₁)
updRel-shiftUp n {name} {f} {g} cf cg {.(UNIV x)} {.(UNIV x)} (updRel-UNIV x) = updRel-UNIV x
updRel-shiftUp n {name} {f} {g} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel-LIFT a₁ a₂ u) = updRel-LIFT _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel-LOWER a₁ a₂ u) = updRel-LOWER _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel-SHRINK a₁ a₂ u) = updRel-SHRINK _ _ (updRel-shiftUp n cf cg u)
updRel-shiftUp n {name} {f} {g} cf cg {.(upd name f)} {.(force g)} updRel-upd
  rewrite #shiftUp (suc (suc n)) (ct g cg)
        | #shiftUp (suc (suc (suc n))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updRel-upd



updRel-shiftDown : (n : ℕ) {name : Name} {f g : Term} (cf : # f) (cg : # g) {a b : Term}
                 → updRel name f g a b
                 → updRel name f g (shiftDown n a) (shiftDown n b)
updRel-shiftDown n {name} {f} {g} cf cg {.(VAR x)} {.(VAR x)} (updRel-VAR x) = updRel-VAR _
updRel-shiftDown n {name} {f} {g} cf cg {.NAT} {.NAT} updRel-NAT = updRel-NAT
updRel-shiftDown n {name} {f} {g} cf cg {.QNAT} {.QNAT} updRel-QNAT = updRel-QNAT
updRel-shiftDown n {name} {f} {g} cf cg {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updRel-LT a₁ a₂ b₁ b₂ u u₁) = updRel-LT _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updRel-QLT a₁ a₂ b₁ b₂ u u₁) = updRel-QLT _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(NUM x)} {.(NUM x)} (updRel-NUM x) = updRel-NUM _
updRel-shiftDown n {name} {f} {g} cf cg {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) = updRel-IFLT _ _ _ _ _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁) (updRel-shiftDown n cf cg u₂) (updRel-shiftDown n cf cg u₃)
updRel-shiftDown n {name} {f} {g} cf cg {.(SUC a₁)} {.(SUC a₂)} (updRel-SUC a₁ a₂ u) = updRel-SUC _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updRel-PI a₁ a₂ b₁ b₂ u u₁) = updRel-PI _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown (suc n) cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updRel-LAMBDA a₁ a₂ u) = updRel-LAMBDA _ _ (updRel-shiftDown (suc n) cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} (updRel-APPLY a₁ a₂ b₁ b₂ u u₁) = updRel-APPLY _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(FIX a₁)} {.(FIX a₂)} (updRel-FIX a₁ a₂ u) = updRel-FIX _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(LET a₁ b₁)} {.(LET a₂ b₂)} (updRel-LET a₁ a₂ b₁ b₂ u u₁) = updRel-LET _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown (suc n) cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updRel-SUM a₁ a₂ b₁ b₂ u u₁) = updRel-SUM _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown (suc n) cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updRel-PAIR a₁ a₂ b₁ b₂ u u₁) = updRel-PAIR _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} (updRel-SPREAD a₁ a₂ b₁ b₂ u u₁) = updRel-SPREAD _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown (suc (suc n)) cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updRel-SET a₁ a₂ b₁ b₂ u u₁) = updRel-SET _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown (suc n) cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updRel-TUNION a₁ a₂ b₁ b₂ u u₁) = updRel-TUNION _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown (suc n) cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updRel-UNION a₁ a₂ b₁ b₂ u u₁) = updRel-UNION _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updRel-QTUNION a₁ a₂ b₁ b₂ u u₁) = updRel-QTUNION _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(INL a₁)} {.(INL a₂)} (updRel-INL a₁ a₂ u) = updRel-INL _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(INR a₁)} {.(INR a₂)} (updRel-INR a₁ a₂ u) = updRel-INR _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} (updRel-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel-DECIDE _ _ _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown (suc n) cf cg u₁) (updRel-shiftDown (suc n) cf cg u₂)
updRel-shiftDown n {name} {f} {g} cf cg {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updRel-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) = updRel-EQ _ _ _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁) (updRel-shiftDown n cf cg u₂)
updRel-shiftDown n {name} {f} {g} cf cg {.AX} {.AX} updRel-AX = updRel-AX
updRel-shiftDown n {name} {f} {g} cf cg {.FREE} {.FREE} updRel-FREE = updRel-FREE
updRel-shiftDown n {name} {f} {g} cf cg {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} (updRel-CHOOSE a₁ a₂ b₁ b₂ u u₁) = updRel-CHOOSE _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updRel-TSQUASH a₁ a₂ u) = updRel-TSQUASH _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updRel-TTRUNC a₁ a₂ u) = updRel-TTRUNC _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(TCONST a₁)} {.(TCONST a₂)} (updRel-TCONST a₁ a₂ u) = updRel-TCONST _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} (updRel-SUBSING a₁ a₂ u) = updRel-SUBSING _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(DUM a₁)} {.(DUM a₂)} (updRel-DUM a₁ a₂ u) = updRel-DUM _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updRel-FFDEFS a₁ a₂ b₁ b₂ u u₁) = updRel-FFDEFS _ _ _ _ (updRel-shiftDown n cf cg u) (updRel-shiftDown n cf cg u₁)
updRel-shiftDown n {name} {f} {g} cf cg {.(UNIV x)} {.(UNIV x)} (updRel-UNIV x) = updRel-UNIV _
updRel-shiftDown n {name} {f} {g} cf cg {.(LIFT a₁)} {.(LIFT a₂)} (updRel-LIFT a₁ a₂ u) = updRel-LIFT _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(LOWER a₁)} {.(LOWER a₂)} (updRel-LOWER a₁ a₂ u) = updRel-LOWER _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} (updRel-SHRINK a₁ a₂ u) = updRel-SHRINK _ _ (updRel-shiftDown n cf cg u)
updRel-shiftDown n {name} {f} {g} cf cg {.(upd name f)} {.(force g)} updRel-upd
  rewrite #shiftDown (suc (suc n)) (ct g cg)
        | #shiftDown (suc (suc (suc n))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updRel-upd
-- LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1))))
-- LAMBDA (LET (VAR 0) (APPLY g (VAR 0)))



updRel-subv : (v : Var) {name : Name} {f g : Term} (cf : # f) (cg : # g) {a₁ a₂ b₁ b₂ : Term}
              → updRel name f g a₁ a₂
              → updRel name f g b₁ b₂
              → updRel name f g (subv v b₁ a₁) (subv v b₂ a₂)
updRel-subv v {name} {f} {g} cf cg {.(VAR x)} {.(VAR x)} {b₁} {b₂} (updRel-VAR x) ub with x ≟ v
... | yes p = ub
... | no p = updRel-VAR x
updRel-subv v {name} {f} {g} cf cg {.NAT} {.NAT} {b₁} {b₂} updRel-NAT ub = updRel-NAT
updRel-subv v {name} {f} {g} cf cg {.QNAT} {.QNAT} {b₁} {b₂} updRel-QNAT ub = updRel-QNAT
updRel-subv v {name} {f} {g} cf cg {.(LT a₁ b₃)} {.(LT a₂ b₄)} {b₁} {b₂} (updRel-LT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-LT _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(QLT a₁ b₃)} {.(QLT a₂ b₄)} {b₁} {b₂} (updRel-QLT a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-QLT _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(NUM x)} {.(NUM x)} {b₁} {b₂} (updRel-NUM x) ub = updRel-NUM x
updRel-subv v {name} {f} {g} cf cg {.(IFLT a₁ b₃ c₁ d₁)} {.(IFLT a₂ b₄ c₂ d₂)} {b₁} {b₂} (updRel-IFLT a₁ a₂ b₃ b₄ c₁ c₂ d₁ d₂ ua ua₁ ua₂ ua₃) ub = updRel-IFLT _ _ _ _ _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub) (updRel-subv v cf cg ua₂ ub) (updRel-subv v cf cg ua₃ ub)
updRel-subv v {name} {f} {g} cf cg {.(SUC a₁)} {.(SUC a₂)} {b₁} {b₂} (updRel-SUC a₁ a₂ ua) ub = updRel-SUC _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(PI a₁ b₃)} {.(PI a₂ b₄)} {b₁} {b₂} (updRel-PI a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-PI _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv (suc v) cf cg ua₁ (updRel-shiftUp 0 cf cg ub))
updRel-subv v {name} {f} {g} cf cg {.(LAMBDA a₁)} {.(LAMBDA a₂)} {b₁} {b₂} (updRel-LAMBDA a₁ a₂ ua) ub = updRel-LAMBDA _ _ (updRel-subv (suc v) cf cg ua (updRel-shiftUp 0 cf cg ub))
updRel-subv v {name} {f} {g} cf cg {.(APPLY a₁ b₃)} {.(APPLY a₂ b₄)} {b₁} {b₂} (updRel-APPLY a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-APPLY _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(FIX a₁)} {.(FIX a₂)} {b₁} {b₂} (updRel-FIX a₁ a₂ ua) ub = updRel-FIX _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(LET a₁ b₃)} {.(LET a₂ b₄)} {b₁} {b₂} (updRel-LET a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-LET _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv (suc v) cf cg ua₁ (updRel-shiftUp 0 cf cg ub))
updRel-subv v {name} {f} {g} cf cg {.(SUM a₁ b₃)} {.(SUM a₂ b₄)} {b₁} {b₂} (updRel-SUM a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-SUM _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv (suc v) cf cg ua₁ (updRel-shiftUp 0 cf cg ub))
updRel-subv v {name} {f} {g} cf cg {.(PAIR a₁ b₃)} {.(PAIR a₂ b₄)} {b₁} {b₂} (updRel-PAIR a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-PAIR _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(SPREAD a₁ b₃)} {.(SPREAD a₂ b₄)} {b₁} {b₂} (updRel-SPREAD a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-SPREAD _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv (suc (suc v)) cf cg ua₁ (updRel-shiftUp 0 cf cg (updRel-shiftUp 0 cf cg ub)))
updRel-subv v {name} {f} {g} cf cg {.(SET a₁ b₃)} {.(SET a₂ b₄)} {b₁} {b₂} (updRel-SET a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-SET _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv (suc v) cf cg ua₁ (updRel-shiftUp 0 cf cg ub))
updRel-subv v {name} {f} {g} cf cg {.(TUNION a₁ b₃)} {.(TUNION a₂ b₄)} {b₁} {b₂} (updRel-TUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-TUNION _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv (suc v) cf cg ua₁ (updRel-shiftUp 0 cf cg ub))
updRel-subv v {name} {f} {g} cf cg {.(UNION a₁ b₃)} {.(UNION a₂ b₄)} {b₁} {b₂} (updRel-UNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-UNION _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(QTUNION a₁ b₃)} {.(QTUNION a₂ b₄)} {b₁} {b₂} (updRel-QTUNION a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-QTUNION _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(INL a₁)} {.(INL a₂)} {b₁} {b₂} (updRel-INL a₁ a₂ ua) ub = updRel-INL _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(INR a₁)} {.(INR a₂)} {b₁} {b₂} (updRel-INR a₁ a₂ ua) ub = updRel-INR _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(DECIDE a₁ b₃ c₁)} {.(DECIDE a₂ b₄ c₂)} {b₁} {b₂} (updRel-DECIDE a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updRel-DECIDE _ _ _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv (suc v) cf cg ua₁ (updRel-shiftUp 0 cf cg ub)) (updRel-subv (suc v) cf cg ua₂ (updRel-shiftUp 0 cf cg ub))
updRel-subv v {name} {f} {g} cf cg {.(EQ a₁ b₃ c₁)} {.(EQ a₂ b₄ c₂)} {b₁} {b₂} (updRel-EQ a₁ a₂ b₃ b₄ c₁ c₂ ua ua₁ ua₂) ub = updRel-EQ _ _ _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub) (updRel-subv v cf cg ua₂ ub)
updRel-subv v {name} {f} {g} cf cg {.AX} {.AX} {b₁} {b₂} updRel-AX ub = updRel-AX
updRel-subv v {name} {f} {g} cf cg {.FREE} {.FREE} {b₁} {b₂} updRel-FREE ub = updRel-FREE
updRel-subv v {name} {f} {g} cf cg {.(CHOOSE a₁ b₃)} {.(CHOOSE a₂ b₄)} {b₁} {b₂} (updRel-CHOOSE a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-CHOOSE _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(TSQUASH a₁)} {.(TSQUASH a₂)} {b₁} {b₂} (updRel-TSQUASH a₁ a₂ ua) ub = updRel-TSQUASH _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(TTRUNC a₁)} {.(TTRUNC a₂)} {b₁} {b₂} (updRel-TTRUNC a₁ a₂ ua) ub = updRel-TTRUNC _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(TCONST a₁)} {.(TCONST a₂)} {b₁} {b₂} (updRel-TCONST a₁ a₂ ua) ub = updRel-TCONST _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(SUBSING a₁)} {.(SUBSING a₂)} {b₁} {b₂} (updRel-SUBSING a₁ a₂ ua) ub = updRel-SUBSING _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(DUM a₁)} {.(DUM a₂)} {b₁} {b₂} (updRel-DUM a₁ a₂ ua) ub = updRel-DUM _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(FFDEFS a₁ b₃)} {.(FFDEFS a₂ b₄)} {b₁} {b₂} (updRel-FFDEFS a₁ a₂ b₃ b₄ ua ua₁) ub = updRel-FFDEFS _ _ _ _ (updRel-subv v cf cg ua ub) (updRel-subv v cf cg ua₁ ub)
updRel-subv v {name} {f} {g} cf cg {.(UNIV x)} {.(UNIV x)} {b₁} {b₂} (updRel-UNIV x) ub = updRel-UNIV x
updRel-subv v {name} {f} {g} cf cg {.(LIFT a₁)} {.(LIFT a₂)} {b₁} {b₂} (updRel-LIFT a₁ a₂ ua) ub = updRel-LIFT _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(LOWER a₁)} {.(LOWER a₂)} {b₁} {b₂} (updRel-LOWER a₁ a₂ ua) ub = updRel-LOWER _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(SHRINK a₁)} {.(SHRINK a₂)} {b₁} {b₂} (updRel-SHRINK a₁ a₂ ua) ub = updRel-SHRINK _ _ (updRel-subv v cf cg ua ub)
updRel-subv v {name} {f} {g} cf cg {.(upd name f)} {.(force g)} {b₁} {b₂} updRel-upd ub
  rewrite subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b₁))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
        | subv# (suc (suc v)) (shiftUp 0 (shiftUp 0 b₂)) g cg
  = updRel-upd
-- LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1))))
-- LAMBDA (LET (VAR 0) (APPLY g (VAR 0)))



updRel-sub : {name : Name} {f g : Term} (cf : # f) (cg : # g) {a₁ a₂ b₁ b₂ : Term}
             → updRel name f g a₁ a₂
             → updRel name f g b₁ b₂
             → updRel name f g (sub b₁ a₁) (sub b₂ a₂)
updRel-sub {name} {f} {g} cf cg {a₁} {a₂} {b₁} {b₂} ua ub =
  updRel-shiftDown 0 cf cg (updRel-subv 0 cf cg ua (updRel-shiftUp 0 cf cg ub))



isHighestℕ-updBody-NUM3→< : (gc : getT-chooseT) {n : ℕ} {name : Name} {f : Term} {k : ℕ} {m : ℕ} {v : Term} {w1 w2 : 𝕎·}
                             → compatible· name w1 Res⊤
                             → (comp : steps k (LET (setT name (NUM m)) (APPLY f (NUM m)) , w1) ≡ (v , w2))
                             → isValue v
                             → isHighestℕ {k} {w1} {w2} {LET (setT name (NUM m)) (APPLY f (NUM m))} {v} n name comp
                             → m < n
isHighestℕ-updBody-NUM3→< gc {n} {name} {f} {0} {m} {v} {w1} {w2} compat comp isv ish
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv
isHighestℕ-updBody-NUM3→< gc {n} {name} {f} {suc k} {m} {v} {w1} {w2} compat comp isv (g0 , ish) =
  getT≤ℕ-chooseT→ gc {name} {w1} {n} {m} compat g1
  where
    ish' : isHighestℕ {k} {chooseT name w1 (NUM m)} {w2} {LET AX (APPLY f (NUM m))} {v} n name comp
    ish' = ish

    g1 : getT≤ℕ (chooseT name w1 (NUM m)) n name
    g1 = isHighestℕ→getT≤ℕ {k} {chooseT name w1 (NUM m)} {w2} {LET AX (APPLY f (NUM m))} {v} n name comp ish'



isHighestℕ-updBody-NUM2→< : (gc : getT-chooseT) {n : ℕ} {name : Name} {f : Term} {k : ℕ} {j m : ℕ} {v : Term} {w1 w2 : 𝕎·}
                             → compatible· name w1 Res⊤
                             → j < n
                             → (comp : steps k (LET (IFLT (NUM j) (NUM m) (setT name (NUM m)) AX) (APPLY f (NUM m)) , w1) ≡ (v , w2))
                             → isValue v
                             → isHighestℕ {k} {w1} {w2} {LET (IFLT (NUM j) (NUM m) (setT name (NUM m)) AX) (APPLY f (NUM m))} {v} n name comp
                             → m < n
isHighestℕ-updBody-NUM2→< gc {n} {name} {f} {0} {j} {m} {v} {w1} {w2} compat ltjn comp isv ish
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv
isHighestℕ-updBody-NUM2→< gc {n} {name} {f} {suc k} {j} {m} {v} {w1} {w2} compat ltjn comp isv ish with j <? m
... | yes x = isHighestℕ-updBody-NUM3→< gc {n} {name} {f} {k} {m} {v} {w1} {w2} compat comp isv (snd ish)
... | no x = <-transʳ (≮⇒≥ x) ltjn


isHighestℕ-updBody-NUM2b→< : (gc : getT-chooseT) {n : ℕ} {name : Name} {f : Term} {k : ℕ} {j m : ℕ} {u v : Term} {w1 w2 : 𝕎·}
                             → compatible· name w1 Res⊤
                             → j < n
                             → u ≡ NUM j
                             → (comp : steps k (LET (IFLT u (NUM m) (setT name (NUM m)) AX) (APPLY f (NUM m)) , w1) ≡ (v , w2))
                             → isValue v
                             → isHighestℕ {k} {w1} {w2} {LET (IFLT u (NUM m) (setT name (NUM m)) AX) (APPLY f (NUM m))} {v} n name comp
                             → m < n
isHighestℕ-updBody-NUM2b→< gc {n} {name} {f} {k} {j} {m} {u} {v} {w1} {w2} compat ltjn equ comp isv ish rewrite equ =
  isHighestℕ-updBody-NUM2→< gc {n} {name} {f} {k} {j} {m} {v} {w1} {w2} compat ltjn comp isv ish



isHighestℕ-updBody-NUM1→< : (gc : getT-chooseT) {n : ℕ} {name : Name} {f : Term} {k : ℕ} {m : ℕ} {v : Term} {w1 w2 : 𝕎·}
                             → compatible· name w1 Res⊤
                             → (comp : steps k (LET (IFLT (get0 name) (NUM m) (setT name (NUM m)) AX) (APPLY f (NUM m)) , w1) ≡ (v , w2))
                             → isValue v
                             → isHighestℕ {k} {w1} {w2} {LET (IFLT (get0 name) (NUM m) (setT name (NUM m)) AX) (APPLY f (NUM m))} {v} n name comp
                             → m < n
isHighestℕ-updBody-NUM1→< gc {n} {name} {f} {0} {m} {v} {w1} {w2} compat comp isv ish
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv
isHighestℕ-updBody-NUM1→< gc {n} {name} {f} {suc k} {m} {v} {w1} {w2} compat comp isv ish with getT⊎ 0 name w1
... | inj₁ (u , p) rewrite p =
  isHighestℕ-updBody-NUM2b→< gc {n} {name} {f} {k} {j} {m} {u} {v} {w1} {w2} compat ltj equ comp isv (snd ish)
  where
    j : ℕ
    j = fst (fst ish)

    gj : getT 0 name w1 ≡ just (NUM j)
    gj = fst (snd (fst ish))

    equ : u ≡ NUM j
    equ = just-inj (trans (sym p) gj)

    ltj : j < n
    ltj = snd (snd (fst ish))
... | inj₂ p rewrite p | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv



isHighestℕ-updBody-NUM→< : (gc : getT-chooseT) {n : ℕ} {name : Name} {f : Term} {k : ℕ} {m : ℕ} {v : Term} {w1 w2 : 𝕎·}
                             → # f
                             → compatible· name w1 Res⊤
                             → (comp : steps k (LET (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w2))
                             → isValue v
                             → isHighestℕ {k} {w1} {w2} {LET (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {v} n name comp
                             → m < n
isHighestℕ-updBody-NUM→< gc {n} {name} {f} {0} {m} {v} {w1} {w2} cf compat comp isv ish
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv
isHighestℕ-updBody-NUM→< gc {n} {name} {f} {suc k} {m} {v} {w1} {w2} cf compat comp isv ish
  rewrite #shiftUp 0 (ct f cf) | subv# 1 (NUM m) f cf | #shiftDown 1 (ct f cf) =
  isHighestℕ-updBody-NUM1→< gc {n} {name} {f} {k} {m} {v} {w1} {w2} compat comp isv (snd ish)



isHighestℕ-updBody→< : (gc : getT-chooseT) {n : ℕ} {name : Name} {f : Term} {k1 k2 : ℕ} {a v : Term} {m : ℕ} {w1 w2 w3 : 𝕎·}
                         → # f
                         → compatible· name w1 Res⊤
                         → (comp1 : steps k1 (a , w1) ≡ (NUM m , w2))
                         → (comp2 : steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w3))
                         → isValue v
                         → isHighestℕ {k2} {w1} {w3} {LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {v} n name comp2
                         → m < n
isHighestℕ-updBody→< gc {n} {name} {f} {0} {k2} {a} {v} {m} {w1} {w2} {w3} cf compat comp1 comp2 isv ish
  rewrite pair-inj₁ comp1 | pair-inj₂ comp1 =
  isHighestℕ-updBody-NUM→< gc {n} {name} {f} {k2} {m} {v} {w2} {w3} cf compat comp2 isv ish
isHighestℕ-updBody→< gc {n} {name} {f} {suc k1} {0} {a} {v} {m} {w1} {w2} {w3} cf compat comp1 comp2 isv ish
  rewrite pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2) = ⊥-elim isv
isHighestℕ-updBody→< gc {n} {name} {f} {suc k1} {suc k2} {a} {v} {m} {w1} {w2} {w3} cf compat comp1 comp2 isv ish with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z with isValue⊎ a
... |    inj₁ x
  rewrite stepVal a w1 x
        | sym (pair-inj₁ (just-inj z))
        | sym (pair-inj₂ (just-inj z))
        | stepsVal a w1 k1 x
        | pair-inj₁ comp1
        | pair-inj₂ comp1
        | #shiftUp 0 (ct f cf)
        | subv# 1 (NUM m) f cf
        | #shiftDown 1 (ct f cf) = isHighestℕ-updBody-NUM1→< gc {n} {name} {f} {k2} {m} {v} {w2} {w3} compat comp2 isv (snd ish)
... |    inj₂ x rewrite z =
  isHighestℕ-updBody→< gc {n} {name} {f} {k1} {k2} {a'} {v} {m} {w1'} {w2} {w3} cf (⊑-compatible· (step⊑ {w1} {w1'} {a} {a'} z) compat) comp1 comp2 isv (snd ish)
isHighestℕ-updBody→< gc {n} {name} {f} {suc k1} {suc k2} {a} {v} {m} {w1} {w2} {w3} cf compat comp1 comp2 isv ish | inj₂ z
  rewrite z | pair-inj₁ comp1 | pair-inj₂ comp1 = ⊥-elim (¬just≡nothing z)



steps-trans+ : {n m : ℕ} {a b c : Term} {w1 w2 w3 : 𝕎·}
              → steps n (a , w1) ≡ (b , w2)
              → steps m (b , w2) ≡ (c , w3)
              → steps (n + m) (a , w1) ≡ (c , w3)
steps-trans+ {n} {m} {a} {b} {c} {w1} {w2} {w3} comp1 comp2
  rewrite steps-+ n m a w1 | comp1 = comp2



→APPLY-force⇓APPLY-NUM : {m : ℕ} {g a : Term} {w1 w2 : 𝕎·}
                          → # g
                          → a ⇓ NUM m from w1 to w2
                          → APPLY (force g) a ⇓ APPLY g (NUM m) from w1 to w2
→APPLY-force⇓APPLY-NUM {m} {g} {a} {w1} {w2} cg comp =
  ⇓-trans₂ {w1} {w1} {w2} {APPLY (force g) a} {LET a (APPLY g (VAR 0))} {APPLY g (NUM m)}
           (1 , →≡pair e1 refl)
           (⇓-trans₂ {w1} {w2} {w2} {LET a (APPLY g (VAR 0))} {LET (NUM m) (APPLY g (VAR 0))} {APPLY g (NUM m)}
                     (LET⇓ (APPLY g (VAR 0)) comp)
                     (1 , →≡pair e2 refl))
  where
    e1 : sub a (LET (VAR 0) (APPLY g (VAR 0))) ≡ LET a (APPLY g (VAR 0))
    e1 rewrite subNotIn a g cg
             | subv# 1 (shiftUp 0 (shiftUp 0 a)) g cg
             | #shiftDown 1 (ct g cg)
             | shiftDownUp a 0 = refl

    e2 : sub (NUM m) (APPLY g (VAR 0)) ≡ APPLY g (NUM m)
    e2 rewrite subNotIn (NUM m) g cg = refl



Σsteps-updRel-NUM→ : {name : Name} {f g : Term} {m : ℕ} {b : Term} {w1 : 𝕎·}
                      → Σ ℕ (λ k' → Σ Term (λ v' → steps k' (b , w1) ≡ (v' , w1) × updRel name f g (NUM m) v'))
                      → Σ ℕ (λ k' → steps k' (b , w1) ≡ (NUM m , w1))
Σsteps-updRel-NUM→ {name} {f} {g} {m} {b} {w1} (k' , .(NUM m) , comp , updRel-NUM .m) = k' , comp


→ΣstepsUpdRel-upd : (gc : getT-chooseT) {n : ℕ} {name : Name} {f g : Term} {a b : Term} {w1 w : 𝕎·}
                     → # f
                     → ¬Names g
                     → compatible· name w1 Res⊤
                     → ∀𝕎-get0-NUM w1 name
                     → updRel name f g a b
                     → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n → strongMonEq w' (APPLY f (NUM k)) (APPLY g (NUM k)))
                     → stepsPresUpdRel n name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
                     → ΣstepsUpdRel name f g (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 (APPLY (force g) b) w
→ΣstepsUpdRel-upd gc {n} {name} {f} {g} {a} {b} {w1} {w} cf nng compat wgt0 u eqn (k , v , w2 , comp , isv , ish ,  ind) =
  k2 + k3 , {!!}
  where
    c : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1' → Σ ℕ (λ m → Σ ℕ (λ m' →
           k1 < k
           × k2 < k
           × getT 0 name w1' ≡ just (NUM m')
           × ssteps k1 (a , w1) ≡ just (NUM m , w1')
           × steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))))))
    c = upd-decomp cf wgt0 comp isv
-- We need to know that m is less than n

    k1 : ℕ
    k1 = fst c

    k2 : ℕ
    k2 = fst (snd c)

    w1' : 𝕎·
    w1' = fst (snd (snd c))

    m : ℕ
    m = fst (snd (snd (snd c)))

    m' : ℕ
    m' = fst (snd (snd (snd (snd c))))

    ltk1 : k1 < k
    ltk1 = fst (snd (snd (snd (snd (snd c)))))

    ltk2 : k2 < k
    ltk2 = fst (snd (snd (snd (snd (snd (snd c))))))

    gt0 : getT 0 name w1' ≡ just (NUM m')
    gt0 = fst (snd (snd (snd (snd (snd (snd (snd c)))))))

    comp1 : ssteps k1 (a , w1) ≡ just (NUM m , w1')
    comp1 = fst (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    comp1b : steps k1 (a , w1) ≡ (NUM m , w1')
    comp1b = ssteps→steps {k1} {a} {NUM m} {w1} {w1'} comp1

    comp2 : steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m)
    comp2 = snd (snd (snd (snd (snd (snd (snd (snd (snd c))))))))

    e1 : w1 ⊑· w1'
    e1 = steps→⊑ k1 a (NUM m) comp1b

    e2 : w1 ⊑· chooseT0if name w1' m' m
    e2 = {!!}

    ltm : m < n -- use with eqn
    ltm = isHighestℕ-updBody→< gc {n} {name} {f} {k1} {k} {a} {v} {m} {w1} {w1'} {w2} cf compat comp1b comp isv ish

    q : strongMonEq w1 (APPLY f (NUM m)) (APPLY g (NUM m))
    q = eqn w1 (⊑-refl· w1) m ltm

    i : ℕ
    i = fst q

    c1 : Σ 𝕎· (λ w1a → APPLY f (NUM m) ⇓ NUM i from chooseT0if name w1' m' m to w1a)
    c1 = ⇓→from-to (lower (fst (snd q) (chooseT0if name w1' m' m) e2))

    w1a : 𝕎·
    w1a = fst c1

    k3 : ℕ
    k3 = fst (snd c1)

    c1b : steps k3 (APPLY f (NUM m) , chooseT0if name w1' m' m) ≡ (NUM i , w1a)
    c1b = snd (snd c1)

    comp2b : steps (k2 + k3) (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (NUM i , w1a)
    comp2b = steps-trans+ {k2} {k3} {LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} {NUM i} {w1} {chooseT0if name w1' m' m} {w1a} comp2 c1b

    indb : Σ ℕ (λ k' → steps k' (b , w1) ≡ (NUM m , w1))
    indb = Σsteps-updRel-NUM→ (ind k1 {!!} {a} {b} {NUM m} {w1} {w1'} {w1} u {!!} comp1b {!!} tt)

    k4 : ℕ
    k4 = fst indb

    cb : steps k4 (b , w1) ≡ (NUM m , w1)
    cb = snd indb

    compg : APPLY (force g) b ⇓ APPLY g (NUM m) from w1 to w1
    compg = →APPLY-force⇓APPLY-NUM {m} {g} {b} {w1} {w1} {!!} (k4 , cb)

    k5 : ℕ
    k5 = fst compg

    compgb : steps k5 (APPLY (force g) b , w1) ≡ (APPLY g (NUM m) , w1)
    compgb = snd compg

    c2 : Σ 𝕎· (λ w1b → APPLY g (NUM m) ⇓ NUM i from w1 to w1b)
    c2 = ⇓→from-to (lower (snd (snd q) w1 (⊑-refl· _)))

    w1b : 𝕎·
    w1b = fst c2

    k6 : ℕ
    k6 = fst (snd c2)

    c2b : steps k6 (APPLY g (NUM m) , w1) ≡ (NUM i , w1b)
    c2b = snd (snd c2)

    compgc : steps (k5 + k6) (APPLY (force g) b , w1) ≡ (NUM i , w1b)
    compgc = steps-trans+ {k5} {k6} {APPLY (force g) b} {APPLY g (NUM m)} {NUM i} {w1} {w1} {w1b} compgb c2b

    compgd : steps (k5 + k6) (APPLY (force g) b , w) ≡ (NUM i , w)
    compgd = {!!} -- use ¬Names→steps in terms4



step-updRel : (gc : getT-chooseT) {n : ℕ} {name : Name} {f g : Term}
              {a b x : Term} {w1 w2 w : 𝕎·}
              → ¬Names f
              → # f
              → # g
              → (k : ℕ)
              → step a w1 ≡ just (x , w2)
              → stepsPresUpdRel n name f g x w2
              → updRel name f g a b
              → getT≤ℕ w1 n name
              → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n → strongMonEq w' (APPLY f (NUM k)) (APPLY g (NUM k)))
              → ΣstepsUpdRel name f g x w2 b w
step-updRel gc {n} {name} {f} {g} {.NAT} {.NAT} {x} {w1} {w2} {w} nnf cf cg k comp ind updRel-NAT gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAT , NAT , w1 , refl , refl , updRel-NAT
step-updRel gc {n} {name} {f} {g} {.QNAT} {.QNAT} {x} {w1} {w2} {w} nnf cf cg k comp ind updRel-QNAT gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QNAT , QNAT , w1 , refl , refl , updRel-QNAT
step-updRel gc {n} {name} {f} {g} {.(LT a₁ b₁)} {.(LT a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-LT a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LT a₁ b₁ , LT a₂ b₂ , w1 , refl , refl , updRel-LT _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-QLT a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QLT a₁ b₁ , QLT a₂ b₂ , w1 , refl , refl , updRel-QLT _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(NUM x₁)} {.(NUM x₁)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-NUM x₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NUM x₁ , NUM x₁ , w1 , refl , refl , updRel-NUM _
step-updRel gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn eqn with is-NUM a₁
... | inj₁ (i1 , p) rewrite p | updRel-NUMₗ→ r with is-NUM b₁
... |    inj₁ (i2 , q) rewrite q | updRel-NUMₗ→ r₁ with i1 <? i2
... |       yes j rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 1 , c₁ , c₂ , w1 , refl , concl , r₂
  where
    concl : steps 1 (IFLT (NUM i1) (NUM i2) c₂ d₂ , w) ≡ (c₂ , w)
    concl with i1 <? i2
    ... | yes j' = refl
    ... | no j' = ⊥-elim (j' j)
... |       no j rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 1 , d₁ , d₂ , w1 , refl , concl , r₃
  where
    concl : steps 1 (IFLT (NUM i1) (NUM i2) c₂ d₂ , w) ≡ (d₂ , w)
    concl with i1 <? i2
    ... | yes j' = ⊥-elim (j j')
    ... | no j' = refl
step-updRel gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn eqn | inj₁ (i1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel-IFLT₂ r₂ r₃ ind'
  where
    ind' : ΣstepsUpdRel name f g b₁' w1' b₂ w
    ind' = step-updRel gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w1} {w1'} {w} nnf cf cg k z (stepsPresUpdRel-IFLT₂→ ind) r₁ gtn eqn
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn eqn | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel-IFLT₁ r₁ r₂ r₃ ind'
  where
    ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
    ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf cf cg k z (stepsPresUpdRel-IFLT₁→ ind) r gtn eqn
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel gc {n} {name} {f} {g} {.(SUC a₁)} {.(SUC a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-SUC a₁ a₂ r) gtn eqn = {!!}
step-updRel gc {n} {name} {f} {g} {.(PI a₁ b₁)} {.(PI a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-PI a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PI a₁ b₁ , PI a₂ b₂ , w1 , refl , refl , updRel-PI _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-LAMBDA a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LAMBDA a₁ , LAMBDA a₂ , w1 , refl , refl , updRel-LAMBDA _ _ r
step-updRel gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-APPLY a₁ a₂ b₁ b₂ r r₁) gtn eqn with is-LAM a₁
... | inj₁ (t , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  concl d --ret (sub a t) w
  where
    d : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel name f g t u)
        ⊎ (t ≡ updBody name f × a₂ ≡ force g)
    d = updRel-LAMBDAₗ→ r

    concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel name f g t u)
            ⊎ (t ≡ updBody name f × a₂ ≡ force g)
            → ΣstepsUpdRel name f g (sub b₁ t) w1 (APPLY a₂ b₂) w
    concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub b₁ t , sub b₂ u , w1 , refl , refl , updRel-sub cf cg ur r₁
    concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c2
      where
        ind' : stepsPresUpdRel n name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
        ind' rewrite e1 | e2 | sub-upd name f b₁ cf = ind

        c1 : ΣstepsUpdRel name f g (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 (APPLY (force g) b₂) w
        c1 = {!!} -- →ΣhighestUpdCtxt-upd gc {name} {f} {b₁} {w1} {n} compat wgt0 cf nnf ctxt₁ indb'

        c2 : ΣstepsUpdRel name f g (sub b₁ (updBody name f)) w1 (APPLY (force g) b₂) w
        c2 rewrite sub-upd name f b₁ cf = c1
... | inj₂ q with is-CS a₁
... |    inj₁ (name' , p) rewrite p = ⊥-elim (updRel-CSₗ→ r)
step-updRel gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-APPLY a₁ a₂ b₁ b₂ r r₁) gtn eqn | inj₂ q | inj₂ p with step⊎ a₁ w1
... | inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →ΣstepsUpdRel-APPLY₁ r₁ ind'
  where
    ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
    ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf cf cg k z (stepsPresUpdRel-APPLY₁→ ind) r gtn eqn
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
step-updRel gc {n} {name} {f} {g} {.(FIX a₁)} {.(FIX a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-FIX a₁ a₂ r) gtn eqn = {!!}
step-updRel gc {n} {name} {f} {g} {.(LET a₁ b₁)} {.(LET a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-LET a₁ a₂ b₁ b₂ r r₁) gtn eqn = {!!}
step-updRel gc {n} {name} {f} {g} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-SUM a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUM a₁ b₁ , SUM a₂ b₂ , w1 , refl , refl , updRel-SUM _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-PAIR a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , refl , refl , updRel-PAIR _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-SPREAD a₁ a₂ b₁ b₂ r r₁) gtn eqn = {!!}
step-updRel gc {n} {name} {f} {g} {.(SET a₁ b₁)} {.(SET a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-SET a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SET a₁ b₁ , SET a₂ b₂ , w1 , refl , refl , updRel-SET _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-TUNION a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , refl , refl , updRel-TUNION _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-UNION a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNION a₁ b₁ , UNION a₂ b₂ , w1 , refl , refl , updRel-UNION _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-QTUNION a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , refl , refl , updRel-QTUNION _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(INL a₁)} {.(INL a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-INL a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INL a₁ , INL a₂ , w1 , refl , refl , updRel-INL _ _ r
step-updRel gc {n} {name} {f} {g} {.(INR a₁)} {.(INR a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-INR a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INR a₁ , INR a₂ , w1 , refl , refl , updRel-INR _ _ r
step-updRel gc {n} {name} {f} {g} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) gtn eqn = {!!}
step-updRel gc {n} {name} {f} {g} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-EQ a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQ a₁ b₁ c₁ , EQ a₂ b₂ c₂ , w1 , refl , refl , {!updRel-EQ _ _ _ _ _ _ r r₁ r₂!}
step-updRel gc {n} {name} {f} {g} {.AX} {.AX} {x} {w1} {w2} {w} nnf cf cg k comp ind updRel-AX gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , AX , AX , w1 , refl , refl , updRel-AX
step-updRel gc {n} {name} {f} {g} {.FREE} {.FREE} {x} {w1} {w2} {w} nnf cf cg k comp ind updRel-FREE gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FREE , FREE , w1 , refl , refl , updRel-FREE
step-updRel gc {n} {name} {f} {g} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-CHOOSE a₁ a₂ b₁ b₂ r r₁) gtn eqn = {!!}
step-updRel gc {n} {name} {f} {g} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-TSQUASH a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TSQUASH a₁ , TSQUASH a₂ , w1 , refl , refl , updRel-TSQUASH _ _ r
step-updRel gc {n} {name} {f} {g} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-TTRUNC a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TTRUNC a₁ , TTRUNC a₂ , w1 , refl , refl , updRel-TTRUNC _ _ r
step-updRel gc {n} {name} {f} {g} {.(TCONST a₁)} {.(TCONST a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-TCONST a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TCONST a₁ , TCONST a₂ , w1 , refl , refl , updRel-TCONST _ _ r
step-updRel gc {n} {name} {f} {g} {.(SUBSING a₁)} {.(SUBSING a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-SUBSING a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUBSING a₁ , SUBSING a₂ , w1 , refl , refl , updRel-SUBSING _ _ r
step-updRel gc {n} {name} {f} {g} {.(DUM a₁)} {.(DUM a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-DUM a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , DUM a₁ , DUM a₂ , w1 , refl , refl , updRel-DUM _ _ r
step-updRel gc {n} {name} {f} {g} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-FFDEFS a₁ a₂ b₁ b₂ r r₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , refl , refl , updRel-FFDEFS _ _ _ _ r r₁
step-updRel gc {n} {name} {f} {g} {.(UNIV x₁)} {.(UNIV x₁)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-UNIV x₁) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNIV x₁ , UNIV x₁ , w1 , refl , refl , updRel-UNIV x₁
step-updRel gc {n} {name} {f} {g} {.(LIFT a₁)} {.(LIFT a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-LIFT a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LIFT a₁ , LIFT a₂ , w1 , refl , refl , updRel-LIFT _ _ r
step-updRel gc {n} {name} {f} {g} {.(LOWER a₁)} {.(LOWER a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-LOWER a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LOWER a₁ , LOWER a₂ , w1 , refl , refl , updRel-LOWER _ _ r
step-updRel gc {n} {name} {f} {g} {.(SHRINK a₁)} {.(SHRINK a₂)} {x} {w1} {w2} {w} nnf cf cg k comp ind (updRel-SHRINK a₁ a₂ r) gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SHRINK a₁ , SHRINK a₂ , w1 , refl , refl , updRel-SHRINK _ _ r
step-updRel gc {n} {name} {f} {g} {.(upd name f)} {.(force g)} {x} {w1} {w2} {w} nnf cf cg k comp ind updRel-upd gtn eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , upd name f , force g , w1 , refl , refl , updRel-upd
-- LAMBDA (LET (VAR 0) (LET (IFLT (APPLY (CS name) (NUM 0)) (VAR 0) (CHOOSE (NAME name) (VAR 0)) AX) (APPLY (shiftUp 0 f) (VAR 1))))
-- LAMBDA (LET (VAR 0) (APPLY g (VAR 0)))


steps-updRel-aux : (gc : getT-chooseT) {n : ℕ} {name : Name} {f g : Term}
                   → ¬Names f
                   → # f
                   → (k : ℕ)
                   → (ind : (k' : ℕ) → k' < k → presUpdRel n name f g k')
                   → presUpdRel n name f g k
steps-updRel-aux gc {n} {name} {f} {g} nnf cf 0 ind {a} {b} {v} {w1} {w2} {w} r eqw comp ish isv
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , b , refl , r
steps-updRel-aux gc {n} {name} {f} {g} nnf cf (suc k) ind {a} {b} {v} {w1} {w2} {w} r eqw comp ish isv
  with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z = {!!}
  where
    ind0 : (k' : ℕ) → k' < suc k → presUpdRel n name f g k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presUpdRel n name f g k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | stepVal a w1 isv =
  ⊥-elim (¬just≡nothing z)



steps-updRel : (gc : getT-chooseT) {n : ℕ} {name : Name} {f g : Term} {k : ℕ}
               → ¬Names f
               → # f
               → presUpdRel n name f g k
steps-updRel gc {n} {name} {f} {g} {k} nnf cf =
  <ℕind _ (steps-updRel-aux gc {n} {name} {f} {g} nnf cf) k



≡suc→< : {a b : ℕ} → a ≡ suc b → b < a
≡suc→< {a} {b} e rewrite e = ≤-refl



-- define an 'external' version of #νtestM that follows the computation of (APPLY F f), and keeps
-- track of the highest number f is applied to, and prove that this 'external' version returns
-- the same value as the 'internal' one (i.e., #νtestM)
eqfg : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
      {i : ℕ} {w : 𝕎·} {F f g : CTerm}
      → #¬Names F
      → #¬Names f
      → #¬Names g
      → ∈Type i w #BAIRE→NAT F
      → ∈Type i w #BAIRE f
      → ∈Type i w #BAIRE g
      → equalInType i w (#BAIREn (#νtestM F f)) f g
--       ((n : ℕ) → n < ? → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
      → equalInType i w #NAT (#APPLY F f) (#APPLY F g)
eqfg nc cn kb gc {i} {w} {F} {f} {g} nnF nnf nng ∈F ∈f ∈g eqb =
  equalInType-trans (equalInType-APPLY-force ∈F ∈f) (equalInType-trans eqf (equalInType-sym (equalInType-APPLY-force ∈F ∈g)))
  where
    neqt : NATeq w (#νtestM F f) (#νtestM F f)
    neqt = νtestM-NAT nc cn kb gc i w F f nnF nnf ∈F ∈f

    tn : ℕ
    tn = fst neqt

    x : NATeq w (#νtestM F f) (#NUM tn)
    x = tn , fst (snd neqt) , compAllRefl _ _

    cx : #νtestM F f #⇛ #NUM tn at w
    cx = NATeq→⇛ {w} {#νtestM F f} x

    eqb1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' (#NATn (#νtestM F f)) a₁ a₂
                         → equalInType i w' #NAT (#APPLY f a₁) (#APPLY g a₂))
    eqb1 = equalInType-FUN→ (≡CTerm→equalInType (≡BAIREn (#νtestM F f)) eqb)

    eqb2 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm)
                         → □· w' (λ w'' _ → Σ ℕ (λ k → a₁ #⇛ #NUM k at w'' × a₂ #⇛ #NUM k at w'' × k < tn))
                         → □· w' (λ w'' _ → NATeq w'' (#APPLY f a₁) (#APPLY g a₂)))
    eqb2 w1 e1 a₁ a₂ eqa = equalInType-NAT→ i w1 (#APPLY f a₁) (#APPLY g a₂) (eqb1 w1 e1 a₁ a₂ (→equalInType-NATn (∀𝕎-mon e1 cx) eqa))

    eqb3 : ∀𝕎 w (λ w' _ → (k : ℕ) → k < tn
                         → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
    eqb3 w1 e1 k ltk = kb z w1 (⊑-refl· _)
      where
        z : □· w1 (λ w'' _ → NATeq w'' (#APPLY f (#NUM k)) (#APPLY g (#NUM k)))
        z = eqb2 w1 e1 (#NUM k) (#NUM k) (Mod.∀𝕎-□ M (λ w2 e2 → k , #compAllRefl (#NUM k) w2 , #compAllRefl (#NUM k) w2 , ltk))

    inn : ∈Type i w #NAT (#APPLY F (#force f))
    inn = equalInType-refl (equalInType-sym (equalInType-APPLY-force ∈F ∈f))

    aw : ∀𝕎 w (λ w' _ → NATeq w' (#APPLY F (#force f)) (#APPLY F (#force f)) → NATeq w' (#APPLY F (#force f)) (#APPLY F (#force g)))
    aw w1 e1 (n , comp1 , comp2) = n , comp1 , ¬Names→⇓→⇛ w1 w1 ⌜ #APPLY F (#force g) ⌝ (NUM n) (#¬Names-APPLY {F} {#force g} nnF (#¬Names-force {g} nng)) compg
      where
        cxb : Σ 𝕎· (λ w2 → νtestM ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1 to w2)
        cxb = ⇓→from-to (lower (cx w1 e1))

        w2 : 𝕎·
        w2 = fst cxb

        compt : νtestM ⌜ F ⌝ ⌜ f ⌝ ⇓ NUM tn from w1 to w2
        compt = snd cxb

        compu : Σ Name (λ name → Σ Term (λ v → Σ ℕ (λ j →
                 APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) ⇓ v from (chooseT name (startNewChoiceT Res⊤ w1 (testM 0 ⌜ F ⌝ ⌜ f ⌝)) (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM j)
                 × tn ≡ suc j)))
        compu = #νtestM⇓→ nc cn {w1} {w2} {⌜ F ⌝} {⌜ f ⌝} {tn} (CTerm.closed F) (CTerm.closed f) nnF nnf compt

        name : Name
        name = fst compu

        v : Term
        v = fst (snd compu)

        j : ℕ
        j = fst (snd (snd compu))

        w1' : 𝕎·
        w1' = chooseT name (startNewChoiceT Res⊤ w1 (testM 0 ⌜ F ⌝ ⌜ f ⌝)) (NUM 0)

        k : ℕ
        k = fst (fst (snd (snd (snd compu))))

        compa : steps k (APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) , w1') ≡ (v , w2)
        compa = snd (fst (snd (snd (snd compu))))

        isvv : isValue v
        isvv = fst (snd (snd (snd (snd compu))))

        g0 : getT 0 name w2 ≡ just (NUM j)
        g0 = fst (snd (snd (snd (snd (snd compu)))))

        eqj : tn ≡ suc j
        eqj = snd (snd (snd (snd (snd (snd compu)))))

        ish : isHighestℕ {k} {w1'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} tn name compa
        ish = steps-sat-isHighestℕ
                gc {name} {⌜ f ⌝} {k} nnf (CTerm.closed f) {w1'} {w2} {APPLY ⌜ F ⌝ (upd name ⌜ f ⌝)} {v} {tn}
                compa isvv (updCtxt-APPLY ⌜ F ⌝ (upd name ⌜ f ⌝) (¬Names→updCtxt {name} {⌜ f ⌝} {⌜ F ⌝} nnF) updCtxt-upd)
                {!!}
                {!!}
                (j , g0 , ≡suc→< eqj)

        compg : #APPLY F (#force g) #⇓ #NUM n at w1
        compg = {!!}

-- We need to prove something like this, where w1 and w1' differ only in name
-- (we should be able to prove that for any world w3 between w1' and w2 (Σ ℕ (λ j → getT 0 name w3 ≡ just (NUM j) × j ≤ m0)) -- see steps-sat-isHighestℕ being proved below
-- (and then define a 'differ' relation relating CTXT(upd name f)/CTXT(force f)/CTXT(force g))
--  → APPLY F (upd name f) ⇓ NUM n from w1' to w2 -- These 3 hypotheses come from #νtestM⇓→
--  → getT 0 name w2 ≡ just (NUM m0)
--  → m0 ≤ m
--  → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < m → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k))) -- from eqb2
--  → APPLY F (force f) ⇓ NUM n at w1
--  → APPLY F (force g) ⇓ NUM n at w1

    eqf : equalInType i w #NAT (#APPLY F (#force f)) (#APPLY F (#force g))
    eqf = →equalInType-NAT i w (#APPLY F (#force f)) (#APPLY F (#force g)) (Mod.∀𝕎-□Func M aw (equalInType-NAT→ i w (#APPLY F (#force f)) (#APPLY F (#force f)) inn))





{--foo2 : {F f g : Term} {n m : ℕ} {w1 w1' w2 : 𝕎·}
       → APPLY F (upd name f) ⇓ NUM n from w1' to w2 -- These 2 hypotheses come from #νtestM⇓→
       → getT≤ℕ w2 m name
       → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < m → NATeq w' (#APPLY f (#NUM k)) (#APPLY g (#NUM k))) -- from eqb2
       → APPLY F (force f) ⇓ NUM n at w1
       → APPLY F (force g) ⇓ NUM n at w1
foo2 {F} {f} {g} {n} {m} {w1} {w1'} {w2} comp
--}



continuity : (nc : ℕℂ) (cn : comp→∀ℕ) (kb : K□) (gc : getT-chooseT)
             (i : ℕ) (w : 𝕎·) (F f : CTerm)
             → #¬Names F
             → #¬Names f
             → ∈Type i w #BAIRE→NAT F
             → ∈Type i w #BAIRE f
             → ∈Type i w (#contBody F f) (#PAIR (#νtestM F f) #lam3AX)
continuity nc cn kb gc i w F f nnF nnf ∈F ∈f =
  ≡CTerm→equalInType (sym (#contBody≡ F f)) h0
  where
    aw : ∀𝕎 w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestM F f) #lam3AX)
                                (#PAIR (#νtestM F f) #lam3AX))
    aw w1 e1 =
      #νtestM F f , #νtestM F f , #lam3AX , #lam3AX ,
      testM-NAT nc cn kb gc i w1 F f nnF nnf (equalInType-mon ∈F w1 e1) (equalInType-mon ∈f w1 e1) ,
      #compAllRefl (#PAIR (#νtestM F f) #lam3AX) w1 ,
      #compAllRefl (#PAIR (#νtestM F f) #lam3AX) w1 ,
      eql1
      where
        ea2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) (eg : equalInType i w2 #BAIRE g₁ g₂)
                             → equalTypes i w2
                                           (#FUN (#FFDEFS #BAIRE g₁) (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f))) (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                           (#FUN (#FFDEFS #BAIRE g₂) (#FUN (#EQ f g₂ (#BAIREn (#νtestM F f))) (#EQ (#APPLY F f) (#APPLY F g₂) #NAT))))
        ea2 w2 e2 g₁ g₂ eg =
          eqTypesFUN←
            (eqTypesFFDEFS← eqTypesBAIRE eg)
            (eqTypesFUN←
              (eqTypesEQ← (→equalTypesBAIREn i w2 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                          (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) eg))
              (eqTypesEQ← eqTypesNAT
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                          (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) eg)))

        eql2 : equalInType i w1 (#PI #BAIRE
                                     (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                              (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ #νtestM F f ⌟))
                                                       (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                  #lam3AX
                                  #lam3AX
        eql2 = equalInType-PI
                 (λ w2 e2 → eqTypesBAIRE)
                 (λ w2 e2 g₁ g₂ eg → ≡CTerm→eqTypes (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₁)) (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₂)) (ea2 w2 e2 g₁ g₂ eg))
                 aw2
          where
            aw3 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                                  → equalInType i w2 (#FUN (#FFDEFS #BAIRE g₁)
                                                           (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f)))
                                                                 (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)))
                                                 (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
            aw3 w2 e2 g₁ g₂ eg =
              equalInType-FUN
                (eqTypesFFDEFS← eqTypesBAIRE (equalInType-refl eg))
                (eqTypesFUN←
                  (eqTypesEQ← (→equalTypesBAIREn i w2 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))))
                              (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                              (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w2 F f nnF nnf (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2))) (equalInType-refl eg)))
                  (eqTypesEQ← eqTypesNAT
                              (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-mon ∈f w2 (⊑-trans· e1 e2)))
                              (∈BAIRE→NAT→ (equalInType-mon ∈F w2 (⊑-trans· e1 e2)) (equalInType-refl eg))))
                aw4
              where
                aw4 : ∀𝕎 w2 (λ w' _ → (x₁ x₂ : CTerm)
                                     → equalInType i w' (#FFDEFS #BAIRE g₁) x₁ x₂
                                     → equalInType i w' (#FUN (#EQ f g₁ (#BAIREn (#νtestM F f)))
                                                               (#EQ (#APPLY F f) (#APPLY F g₁) #NAT))
                                                         (#APPLY (#APPLY #lam3AX g₁) x₁)
                                                         (#APPLY (#APPLY #lam3AX g₂) x₂))
                aw4 w3 e3 x₁ x₂ ex =
                  equalInType-FUN
                    (eqTypesEQ← (→equalTypesBAIREn i w3 (#νtestM F f) (#νtestM F f) (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))))
                                 (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                                 (∈BAIRE→∈BAIREn (testM-NAT nc cn kb gc i w3 F f nnF nnf (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3)))) (equalInType-refl (equalInType-mon eg w3 e3))))
                    (eqTypesEQ← eqTypesNAT
                                 (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-mon ∈f w3 (⊑-trans· e1 (⊑-trans· e2 e3))))
                                 (∈BAIRE→NAT→ (equalInType-mon ∈F w3 (⊑-trans· e1 (⊑-trans· e2 e3))) (equalInType-refl (equalInType-mon eg w3 e3))))
                    aw5
                  where
                    aw5 : ∀𝕎 w3 (λ w' _ → (y₁ y₂ : CTerm)
                                        → equalInType i w' (#EQ f g₁ (#BAIREn (#νtestM F f))) y₁ y₂
                                        → equalInType i w' (#EQ (#APPLY F f) (#APPLY F g₁) #NAT)
                                                            (#APPLY (#APPLY (#APPLY #lam3AX g₁) x₁) y₁)
                                                            (#APPLY (#APPLY (#APPLY #lam3AX g₂) x₂) y₂))
                    aw5 w4 e4 y₁ y₂ ey =
                      equalInType-EQ
                        eqTypesNAT
                        concl
                      where
                        hyp : □· w4 (λ w5 _ → equalInType i w5 (#BAIREn (#νtestM F f)) f g₁)
                        hyp = equalInType-EQ→ ey

                        ff : □· w3 (λ w' _ → FFDEFSeq g₁ (equalInType i w' #BAIRE) w' x₁ x₂)
                        ff = equalInTypeFFDEFS→ ex

                        aw6 : ∀𝕎 w4 (λ w' e' → equalInType i w' (#BAIREn (#νtestM F f)) f g₁
                                              → ↑wPred (λ w'' _ → FFDEFSeq g₁ (equalInType i w'' #BAIRE) w'' x₁ x₂) e4 w' e'
                                              → equalInType i w' #NAT (#APPLY F f) (#APPLY F g₁))
                        aw6 w5 e5 h1 (g , h2 , nng) = equalInType-trans cc (∈BAIRE→NAT→ (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-sym h2))
                          where
                            h3 : equalInType i w5 (#BAIREn (#νtestM F f)) f g
                            h3 = equalInType-BAIREn-BAIRE-trans h2 h1 (testM-NAT nc cn kb gc i w5 F f nnF nnf (equalInType-mon ∈F w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))) (equalInType-mon ∈f w5 (⊑-trans· e1 (⊑-trans· e2 (⊑-trans· e3 (⊑-trans· e4 e5))))))

                            cc : equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)
                            cc = {!!}

-- → #¬Names F
-- → #¬Names f
-- → #¬Names g
-- → equalInType i w5 (#BAIREn (#νtestM F f)) f g
--       ((n : ℕ) → ⇓sameℕ w (APPLY f (NUM n)) (APPLY g (NUM n)))
-- → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g)

                        concl : □· w4 (λ w5 _ → equalInType i w5 #NAT (#APPLY F f) (#APPLY F g₁))
                        concl = ∀𝕎-□Func2 aw6 hyp (Mod.↑□ M ff e4)

            aw2 : ∀𝕎 w1 (λ w2 e2 → (g₁ g₂ : CTerm) → equalInType i w2 #BAIRE g₁ g₂
                                  → equalInType i w2 (sub0 g₁ (#[0]FUN (#[0]FFDEFS #[0]BAIRE #[0]VAR)
                                                                        (#[0]FUN (#[0]EQ ⌞ f ⌟ #[0]VAR (#[0]BAIREn ⌞ #νtestM F f ⌟))
                                                                                 (#[0]EQ (#[0]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[0]APPLY ⌞ F ⌟ #[0]VAR) #[0]NAT))))
                                                 (#APPLY #lam3AX g₁) (#APPLY #lam3AX g₂))
            aw2 w2 e2 g₁ g₂ eg = ≡CTerm→equalInType (sym (sub0-contBodyPI-PI F f (#νtestM F f) g₁)) (aw3 w2 e2 g₁ g₂ eg)

        eql1 : equalInType i w1 (sub0 (#νtestM F f)
                                      (#[0]PI #[0]BAIRE
                                              (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                       (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                                 #lam3AX
                                 #lam3AX
        eql1 = ≡CTerm→equalInType (sym (sub0-contBodyPI F f (#νtestM F f))) eql2

    seq : □· w (λ w' _ → SUMeq (equalInType i w' #NAT)
                                (λ a b ea → equalInType i w' (sub0 a (#[0]PI #[0]BAIRE
                                                                             (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                                                                      (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                                                               (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT))))))
                                w'
                                (#PAIR (#νtestM F f) #lam3AX)
                                (#PAIR (#νtestM F f) #lam3AX))
    seq = Mod.∀𝕎-□ M aw

    h0 : ∈Type i w (#SUM #NAT
                         (#[0]PI #[0]BAIRE
                                 (#[1]FUN (#[1]FFDEFS #[1]BAIRE #[1]VAR0)
                                          (#[1]FUN (#[1]EQ ⌞ f ⌟ #[1]VAR0 (#[1]BAIREn #[1]VAR1))
                                                   (#[1]EQ (#[1]APPLY ⌞ F ⌟ ⌞ f ⌟) (#[1]APPLY ⌞ F ⌟ #[1]VAR0) #[1]NAT)))))
                   (#PAIR (#νtestM F f) #lam3AX)
    h0 = equalInType-SUM (λ w' e' → eqTypesNAT) (equalTypes-contBodyPI i w F f ∈F ∈f) seq

\end{code}
