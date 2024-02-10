\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --auto-inline #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; trans ; subst)
--open import Relation.Binary.PropositionalEquality hiding ([_] ; Extensionality)
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
open import encode


module continuity5 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice)
                   (K : Compatible {L} W C)
                   (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G)
                   (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
open import terms5(W)(C)(K)(G)(X)(N)(EC)
open import terms6(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC)
open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)
open import encodeDef(EC)

open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
open import props4(W)(M)(C)(K)(G)(X)(N)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(G)(X)(N)(EC)
open import continuity2(W)(M)(C)(K)(G)(X)(N)(EC)
open import continuity3(W)(M)(C)(K)(G)(X)(N)(EC)
open import continuity4(W)(M)(C)(K)(G)(X)(N)(EC)


updRel-NATRECr : {name : Name} {f g : Term} {n : ℕ} {b1 b2 c1 c2 : Term} (cf : # f) (cg : # g)
               → updRel name f g b1 b2
               → updRel name f g c1 c2
               → updRel name f g (NATRECr n b1 c1) (NATRECr n b2 c2)
updRel-NATRECr {name} {f} {g} {0} {b1} {b2} {c1} {c2} cf cg ub uc = ub
updRel-NATRECr {name} {f} {g} {suc n} {b1} {b2} {c1} {c2} cf cg ub uc =
  updRel-APPLY _ _ _ _
    (updRel-APPLY _ _ _ _ uc (updRel-NUM _))
   (updRel-NATREC _ _ _ _ _ _ (updRel-NUM _) ub uc)


updRel-WRECr : {name : Name} {f g : Term} {r1 r2 f1 f2 : Term} (cf : # f) (cg : # g)
               → updRel name f g r1 r2
               → updRel name f g f1 f2
               → updRel name f g (WRECr r1 f1) (WRECr r2 f2)
updRel-WRECr {name} {f} {g} {r1} {r2} {f1} {f2} cf cg dr df =
  updRel-LAMBDA
    _ _
    (updRel-WREC
      _ _ _ _
      (updRel-APPLY _ _ _ _ (updRel-shiftUp 0 cf cg df) (updRel-VAR 0))
      (updRel-shiftUp 3 cf cg dr))


updRel-BOT : (name : Name) (f g : Term)
             → updRel name f g BOT BOT
updRel-BOT name f g = updRel-FIX ID ID (updRel-LAMBDA (VAR 0) (VAR 0) (updRel-VAR _))


updRel-ENCr : {name : Name} {f g : Term} {a : Term}
              → updRel name f g a a
              → updRel name f g (ENCr a) (ENCr a)
updRel-ENCr {name} {f} {g} {a} u =
  updRel-IFEQ
    (APPLY a (NUM (encode· (ENC a)))) (APPLY a (NUM (encode· (ENC a)))) N0 N0 BOT BOT N0 N0
    (updRel-APPLY a a (NUM (encode· (ENC a))) (NUM (encode· (ENC a))) u (updRel-NUM _))
    (updRel-NUM _)
    (updRel-BOT name f g)
    (updRel-NUM _)


abstract

  step-updRel : (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
                {a b x : Term} {w1 w2 w : 𝕎·}
                → ¬Names f
                → ¬Names g
                → # f
                → # g
                → step a w1 ≡ just (x , w2)
                → stepsPresUpdRel n name f g x w2
                → updRel name f g a b
                → getT≤ℕ w1 n name
                → compatible· name w1 Res⊤
                → ∀𝕎-get0-NUM w1 name
                → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n → strongMonEq w' (APPLY f (NUM k)) (APPLY g (NUM k)))
                → ΣstepsUpdRel name f g x w2 b w
--  step-updRel gc {n} {name} {f} {g} {.NAT} {.NAT} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-NAT gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAT , NAT , w1 , refl , refl , updRel-NAT
  step-updRel gc {n} {name} {f} {g} {.QNAT} {.QNAT} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-QNAT gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QNAT , QNAT , w1 , refl , refl , updRel-QNAT
--  step-updRel gc {n} {name} {f} {g} {.TNAT} {.TNAT} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-TNAT gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TNAT , TNAT , w1 , refl , refl , updRel-TNAT
  step-updRel gc {n} {name} {f} {g} {.(LT a₁ b₁)} {.(LT a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-LT a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LT a₁ b₁ , LT a₂ b₂ , w1 , refl , refl , updRel-LT _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-QLT a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QLT a₁ b₁ , QLT a₂ b₂ , w1 , refl , refl , updRel-QLT _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(NUM x₁)} {.(NUM x₁)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-NUM x₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NUM x₁ , NUM x₁ , w1 , refl , refl , updRel-NUM _
  step-updRel gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn compat wgt0 eqn with is-NUM a₁
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
  step-updRel gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn compat wgt0 eqn | inj₁ (i1 , p) | inj₂ q with step⊎ b₁ w1
  ... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-IFLT₂ r₂ r₃ ind'
    where
      ind' : ΣstepsUpdRel name f g b₁' w1' b₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-IFLT₂→ ind) r₁ gtn compat wgt0 eqn
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(IFLT a₁ b₁ c₁ d₁)} {.(IFLT a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn compat wgt0 eqn | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-IFLT₁ r₁ r₂ r₃ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-IFLT₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn compat wgt0 eqn with is-NUM a₁
  ... | inj₁ (i1 , p) rewrite p | updRel-NUMₗ→ r with is-NUM b₁
  ... |    inj₁ (i2 , q) rewrite q | updRel-NUMₗ→ r₁ with i1 ≟ i2
  ... |       yes j rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 1 , c₁ , c₂ , w1 , refl , concl , r₂
    where
      concl : steps 1 (IFEQ (NUM i1) (NUM i2) c₂ d₂ , w) ≡ (c₂ , w)
      concl with i1 ≟ i2
      ... | yes j' = refl
      ... | no j' = ⊥-elim (j' j)
  ... |       no j rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 1 , d₁ , d₂ , w1 , refl , concl , r₃
    where
      concl : steps 1 (IFEQ (NUM i1) (NUM i2) c₂ d₂ , w) ≡ (d₂ , w)
      concl with i1 ≟ i2
      ... | yes j' = ⊥-elim (j j')
      ... | no j' = refl
  step-updRel gc {n} {name} {f} {g} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn compat wgt0 eqn | inj₁ (i1 , p) | inj₂ q with step⊎ b₁ w1
  ... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-IFEQ₂ r₂ r₃ ind'
    where
      ind' : ΣstepsUpdRel name f g b₁' w1' b₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {b₁} {b₂} {b₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-IFEQ₂→ ind) r₁ gtn compat wgt0 eqn
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(IFEQ a₁ b₁ c₁ d₁)} {.(IFEQ a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn compat wgt0 eqn | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-IFEQ₁ r₁ r₂ r₃ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-IFEQ₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(SUC a₁)} {.(SUC a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-SUC a₁ a₂ r) gtn compat wgt0 eqn with is-NUM a₁
  ... | inj₁ (i , p)
    rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel-NUMₗ→ r =
    0 , 1 , NUM (suc i) , NUM (suc i) , w1 , refl , refl , updRel-NUM (suc i)
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z)
    rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-SUC₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-SUC₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(NATREC a₁ b₁ c₁)} {.(NATREC a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-NATREC a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) gtn compat wgt0 eqn with is-NUM a₁
  ... | inj₁ (i , p)
    rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel-NUMₗ→ r
    = 0 , 1 , NATRECr i b₁ c₁ , NATRECr i b₂ c₂ , w1 , refl , refl ,
      updRel-NATRECr {name} {f} {g} {i} {b₁} {b₂} {c₁} {c₂} cf cg r₁ r₂
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z)
    rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-NATREC₁ r₁ r₂ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-NATREC₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(PI a₁ b₁)} {.(PI a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-PI a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PI a₁ b₁ , PI a₂ b₂ , w1 , refl , refl , updRel-PI _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(LAMBDA a₁)} {.(LAMBDA a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-LAMBDA a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LAMBDA a₁ , LAMBDA a₂ , w1 , refl , refl , updRel-LAMBDA _ _ r
  step-updRel gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-APPLY a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn with is-LAM a₁
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
          c1 = fst (→ΣstepsUpdRel-upd gc {n} {name} {f} {g} {b₁} {b₂} {w1} {w} cf cg nng compat wgt0 r₁ eqn ind')

          c2 : ΣstepsUpdRel name f g (sub b₁ (updBody name f)) w1 (APPLY (force g) b₂) w
          c2 rewrite sub-upd name f b₁ cf = c1
  ... | inj₂ q with is-CS a₁
  ... |    inj₁ (name' , p) rewrite p = ⊥-elim (updRel-CSₗ→ r)
  step-updRel gc {n} {name} {f} {g} {.(APPLY a₁ b₁)} {.(APPLY a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-APPLY a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn | inj₂ q | inj₂ p with is-MSEQ a₁
  ... | inj₁ (sq , sqr) rewrite sqr | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel-MSEQₗ→ r =
    0 , 1 , MAPP sq b₁ , MAPP sq b₂ , w1 , refl , refl , updRel-MAPP sq b₁ b₂ r₁
  ... | inj₂ sqr with step⊎ a₁ w1
  ... |   inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-APPLY₁ r₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-APPLY₁→ ind) r gtn compat wgt0 eqn
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(FIX a₁)} {.(FIX a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-FIX a₁ a₂ r) gtn compat wgt0 eqn with is-LAM a₁
  ... | inj₁ (t , p)
    rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl d
    where
      d : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel name f g t u)
          ⊎ (t ≡ updBody name f × a₂ ≡ force g)
      d = updRel-LAMBDAₗ→ r

      concl : Σ Term (λ u → a₂ ≡ LAMBDA u × updRel name f g t u)
              ⊎ (t ≡ updBody name f × a₂ ≡ force g)
              → ΣstepsUpdRel name f g (sub (FIX (LAMBDA t)) t) w1 (FIX a₂) w
      concl (inj₁ (u , eqa , ur)) rewrite eqa = 0 , 1 , sub (FIX (LAMBDA t)) t , sub (FIX (LAMBDA u)) u , w1 , refl , refl , updRel-sub cf cg ur (updRel-FIX _ _ (updRel-LAMBDA _ _ ur))
      concl (inj₂ (e1 , e2)) rewrite e1 | e2 = c2
        where
          ind' : stepsPresUpdRel n name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1
          ind' rewrite e1 | e2 | sub-upd name f (FIX (upd name f)) cf = ind

          c1b : Σ (ΣstepsUpdRel name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 (APPLY (force g) (FIX (force g))) w)
                  (λ x → 0 < fst (snd x))
          c1b = →ΣstepsUpdRel-upd gc {n} {name} {f} {g} {FIX (upd name f)} {FIX (force g)} {w1} {w} cf cg nng compat wgt0 (updRel-FIX _ _ updRel-upd) eqn ind'

          c1 : ΣstepsUpdRel name f g (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))) w1 (FIX (force g)) w
          c1 = ΣstepsUpdRel-FIX-APPLY→ c1b

          c2 : ΣstepsUpdRel name f g (sub (FIX (upd name f)) (updBody name f)) w1 (FIX (force g)) w
          c2 rewrite sub-upd name f (FIX (upd name f)) cf = c1
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z)
    rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-FIX₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-FIX₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(LET a₁ b₁)} {.(LET a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-LET a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn with isValue⊎ a₁
  ... | inj₁ y rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    0 , 1 , sub a₁ b₁ , sub a₂ b₂ , w1 , refl , (snd (LET-val⇓ w a₂ b₂ (updRel→isValue r y))) , (updRel-sub cf cg r₁ r)
  ... | inj₂ y with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-LET₁ r₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-LET₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(WT a₁ b₁ c₁)} {.(WT a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-WT a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , WT a₁ b₁ c₁ , WT a₂ b₂ c₂ , w1 , refl , refl , updRel-WT _ _ _ _ _ _ r r₁ r₂
  step-updRel gc {n} {name} {f} {g} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-SUP a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUP a₁ b₁ , SUP a₂ b₂ , w1 , refl , refl , updRel-SUP _ _ _ _ r r₁
  {--step-updRel gc {n} {name} {f} {g} {.(DSUP a₁ b₁)} {.(DSUP a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-DSUP a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn with is-SUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl d
    where
      d : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ SUP x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
      d = updRel-SUPₗ→ r

      concl : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ SUP x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
              → ΣstepsUpdRel name f g (sub u₂ (sub u₁ b₁)) w1 (DSUP a₂ b₂) w
      concl (x₁ , x₂ , eqa , ur1 , ur2) rewrite eqa = 0 , 1 , sub u₂ (sub u₁ b₁) , sub x₂ (sub x₁ b₂) , w1 , refl , refl , updRel-sub cf cg (updRel-sub cf cg r₁ ur1) ur2
  ... | inj₂ y with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-DSUP₁ r₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-DSUP₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
  step-updRel gc {n} {name} {f} {g} {.(WREC a₁ b₁)} {.(WREC a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-WREC a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn with is-SUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl d
    where
      d : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ SUP x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
      d = updRel-SUPₗ→ r

      concl : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ SUP x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
              → ΣstepsUpdRel name f g (sub (WRECr b₁ u₂) (sub (shiftUp 0 u₂) (sub (shiftUp 0 (shiftUp 0 u₁)) b₁))) w1 (WREC a₂ b₂) w
      concl (x₁ , x₂ , eqa , ur1 , ur2) rewrite eqa =
        0 , 1 ,
        sub (WRECr b₁ u₂) (sub (shiftUp 0 u₂) (sub (shiftUp 0 (shiftUp 0 u₁)) b₁)) ,
        sub (WRECr b₂ x₂) (sub (shiftUp 0 x₂) (sub (shiftUp 0 (shiftUp 0 x₁)) b₂)) ,
        w1 , refl , refl ,
        updRel-sub cf cg
          (updRel-sub cf cg (updRel-sub cf cg r₁ (updRel-shiftUp 0 cf cg  (updRel-shiftUp 0 cf cg ur1))) (updRel-shiftUp 0 cf cg ur2))
          (updRel-WRECr cf cg r₁ ur2)
  ... | inj₂ y with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-WREC₁ r₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-WREC₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(MT a₁ b₁ c₁)} {.(MT a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-MT a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MT a₁ b₁ c₁ , MT a₂ b₂ c₂ , w1 , refl , refl , updRel-MT _ _ _ _ _ _ r r₁ r₂
  --step-updRel gc {n} {name} {f} {g} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-MSUP a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MSUP a₁ b₁ , MSUP a₂ b₂ , w1 , refl , refl , updRel-MSUP _ _ _ _ r r₁
  {--step-updRel gc {n} {name} {f} {g} {.(DMSUP a₁ b₁)} {.(DMSUP a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-DMSUP a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn with is-MSUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl d
    where
      d : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ MSUP x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
      d = updRel-MSUPₗ→ r

      concl : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ MSUP x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
              → ΣstepsUpdRel name f g (sub u₂ (sub u₁ b₁)) w1 (DMSUP a₂ b₂) w
      concl (x₁ , x₂ , eqa , ur1 , ur2) rewrite eqa = 0 , 1 , sub u₂ (sub u₁ b₁) , sub x₂ (sub x₁ b₂) , w1 , refl , refl , updRel-sub cf cg (updRel-sub cf cg r₁ ur1) ur2
  ... | inj₂ y with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-DMSUP₁ r₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-DMSUP₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))--}
  step-updRel gc {n} {name} {f} {g} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-SUM a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUM a₁ b₁ , SUM a₂ b₂ , w1 , refl , refl , updRel-SUM _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-PAIR a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , refl , refl , updRel-PAIR _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(SPREAD a₁ b₁)} {.(SPREAD a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-SPREAD a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn with is-PAIR a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl d
    where
      d : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ PAIR x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
      d = updRel-PAIRₗ→ r

      concl : Σ Term (λ x₁ → Σ Term (λ x₂ → a₂ ≡ PAIR x₁ x₂ × updRel name f g u₁ x₁ × updRel name f g u₂ x₂))
              → ΣstepsUpdRel name f g (sub u₂ (sub (shiftUp 0 u₁) b₁)) w1 (SPREAD a₂ b₂) w
      concl (x₁ , x₂ , eqa , ur1 , ur2) rewrite eqa =
        0 , 1 ,
        sub u₂ (sub (shiftUp 0 u₁) b₁) ,
        sub x₂ (sub (shiftUp 0 x₁) b₂) ,
        w1 , refl , refl ,
        updRel-sub cf cg (updRel-sub cf cg r₁ (updRel-shiftUp 0 cf cg ur1)) ur2
  ... | inj₂ y with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-SPREAD₁ r₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-SPREAD₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(SET a₁ b₁)} {.(SET a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-SET a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SET a₁ b₁ , SET a₂ b₂ , w1 , refl , refl , updRel-SET _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-ISECT a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , refl , refl , updRel-ISECT _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-TUNION a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , refl , refl , updRel-TUNION _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-UNION a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNION a₁ b₁ , UNION a₂ b₂ , w1 , refl , refl , updRel-UNION _ _ _ _ r r₁
--  step-updRel gc {n} {name} {f} {g} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-QTUNION a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , refl , refl , updRel-QTUNION _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(INL a₁)} {.(INL a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-INL a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INL a₁ , INL a₂ , w1 , refl , refl , updRel-INL _ _ r
  step-updRel gc {n} {name} {f} {g} {.(INR a₁)} {.(INR a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-INR a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INR a₁ , INR a₂ , w1 , refl , refl , updRel-INR _ _ r
  step-updRel gc {n} {name} {f} {g} {.(DECIDE a₁ b₁ c₁)} {.(DECIDE a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) gtn compat wgt0 eqn with is-INL a₁
  ... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl d --ret (sub t b) w
    where
      d : Σ Term (λ u → a₂ ≡ INL u × updRel name f g t u)
      d = updRel-INLₗ→ r

      concl : Σ Term (λ u → a₂ ≡ INL u × updRel name f g t u)
              → ΣstepsUpdRel name f g (sub t b₁) w1 (DECIDE a₂ b₂ c₂) w
      concl (u , eqa , ur) rewrite eqa = 0 , 1 , sub t b₁ , sub u b₂ , w1 , refl , refl , updRel-sub cf cg r₁ ur
  ... | inj₂ y with is-INR a₁
  ... |    inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    concl d --ret (sub -- TODO:  b) w
    where
      d : Σ Term (λ u → a₂ ≡ INR u × updRel name f g t u)
      d = updRel-INRₗ→ r

      concl : Σ Term (λ u → a₂ ≡ INR u × updRel name f g t u)
              → ΣstepsUpdRel name f g (sub t c₁) w1 (DECIDE a₂ b₂ c₂) w
      concl (u , eqa , ur) rewrite eqa = 0 , 1 , sub t c₁ , sub u c₂ , w1 , refl , refl , updRel-sub cf cg r₂ ur
  ... |    inj₂ j with step⊎ a₁ w1
  ... |       inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-DECIDE₁ r₁ r₂ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-DECIDE₁→ ind) r gtn compat wgt0 eqn
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-EQ a₁ a₂ b₁ b₂ c₁ c₂ r r₁ r₂) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQ a₁ b₁ c₁ , EQ a₂ b₂ c₂ , w1 , refl , refl , updRel-EQ _ _ _ _ _ _ r r₁ r₂
--  step-updRel gc {n} {name} {f} {g} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ r r₁ r₂ r₃) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQB a₁ b₁ c₁ d₁ , EQB a₂ b₂ c₂ d₂ , w1 , refl , refl , updRel-EQB _ _ _ _ _ _ _ _ r r₁ r₂ r₃
  step-updRel gc {n} {name} {f} {g} {.AX} {.AX} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-AX gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , AX , AX , w1 , refl , refl , updRel-AX
  step-updRel gc {n} {name} {f} {g} {.FREE} {.FREE} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-FREE gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FREE , FREE , w1 , refl , refl , updRel-FREE
  step-updRel gc {n} {name} {f} {g} {.(MSEQ s)} {.(MSEQ s)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-MSEQ s) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MSEQ s , MSEQ s , w1 , refl , refl , updRel-MSEQ s
  step-updRel gc {n} {name} {f} {g} {.(MAPP s a₁)} {.(MAPP s a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-MAPP s a₁ a₂ r) gtn compat wgt0 eqn with is-NUM a₁
  ... | inj₁ (k , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updRel-NUMₗ→ r =
    0 , 1 , NUM (s k) , NUM (s k) , w1 , refl , refl , updRel-NUM _
  ... | inj₂ q with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-MAPP₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-MAPP₁→ ind) r gtn compat wgt0 eqn
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
  step-updRel gc {n} {name} {f} {g} {.(CHOOSE a₁ b₁)} {.(CHOOSE a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-CHOOSE a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn with is-NAME a₁
  ... | inj₁ (name' , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = ⊥-elim (updRel-NAMEₗ→ r)
  ... | inj₂ q with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
    →ΣstepsUpdRel-CHOOSE₁ r₁ ind'
    where
      ind' : ΣstepsUpdRel name f g a₁' w1' a₂ w
      ind' = step-updRel gc {n} {name} {f} {g} {a₁} {a₂} {a₁'} {w1} {w1'} {w} nnf nng cf cg z (stepsPresUpdRel-CHOOSE₁→ ind) r gtn compat wgt0 eqn
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
--  step-updRel gc {n} {name} {f} {g} {.(TSQUASH a₁)} {.(TSQUASH a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-TSQUASH a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TSQUASH a₁ , TSQUASH a₂ , w1 , refl , refl , updRel-TSQUASH _ _ r
--  step-updRel gc {n} {name} {f} {g} {.(TTRUNC a₁)} {.(TTRUNC a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-TTRUNC a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TTRUNC a₁ , TTRUNC a₂ , w1 , refl , refl , updRel-TTRUNC _ _ r
  step-updRel gc {n} {name} {f} {g} {.NOWRITE} {.NOWRITE} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-NOWRITE gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NOWRITE , NOWRITE , w1 , refl , refl , updRel-NOWRITE
  step-updRel gc {n} {name} {f} {g} {.NOREAD}  {.NOREAD}  {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-NOREAD  gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NOREAD  , NOREAD  , w1 , refl , refl , updRel-NOREAD
  step-updRel gc {n} {name} {f} {g} {.(SUBSING a₁)} {.(SUBSING a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-SUBSING a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUBSING a₁ , SUBSING a₂ , w1 , refl , refl , updRel-SUBSING _ _ r
  step-updRel gc {n} {name} {f} {g} {.(PURE)} {.(PURE)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-PURE) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PURE , PURE , w1 , refl , refl , updRel-PURE
  step-updRel gc {n} {name} {f} {g} {.(NOSEQ)} {.(NOSEQ)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-NOSEQ) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NOSEQ , NOSEQ , w1 , refl , refl , updRel-NOSEQ
  step-updRel gc {n} {name} {f} {g} {.(NOENC)} {.(NOENC)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-NOENC) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NOENC , NOENC , w1 , refl , refl , updRel-NOENC
  step-updRel gc {n} {name} {f} {g} {.(TERM a₁)} {.(TERM a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-TERM a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TERM a₁ , TERM a₂ , w1 , refl , refl , updRel-TERM _ _ r
  step-updRel gc {n} {name} {f} {g} {.(ENC a)} {.(ENC a)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-ENC a r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 1 , ENCr a , ENCr a , w1 , refl , refl , updRel-ENCr r --0 , 0 , TERM a₁ , TERM a₂ , w1 , refl , refl , updRel-TERM _ _ r
  step-updRel gc {n} {name} {f} {g} {.(PARTIAL a₁)} {.(PARTIAL a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-PARTIAL a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PARTIAL a₁ , PARTIAL a₂ , w1 , refl , refl , updRel-PARTIAL _ _ r
  step-updRel gc {n} {name} {f} {g} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-FFDEFS a₁ a₂ b₁ b₂ r r₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , refl , refl , updRel-FFDEFS _ _ _ _ r r₁
  step-updRel gc {n} {name} {f} {g} {.(UNIV x₁)} {.(UNIV x₁)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-UNIV x₁) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNIV x₁ , UNIV x₁ , w1 , refl , refl , updRel-UNIV x₁
  step-updRel gc {n} {name} {f} {g} {.(LIFT a₁)} {.(LIFT a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-LIFT a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LIFT a₁ , LIFT a₂ , w1 , refl , refl , updRel-LIFT _ _ r
  step-updRel gc {n} {name} {f} {g} {.(LOWER a₁)} {.(LOWER a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-LOWER a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LOWER a₁ , LOWER a₂ , w1 , refl , refl , updRel-LOWER _ _ r
  step-updRel gc {n} {name} {f} {g} {.(SHRINK a₁)} {.(SHRINK a₂)} {x} {w1} {w2} {w} nnf nng cf cg comp ind (updRel-SHRINK a₁ a₂ r) gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SHRINK a₁ , SHRINK a₂ , w1 , refl , refl , updRel-SHRINK _ _ r
  step-updRel gc {n} {name} {f} {g} {.(upd name f)} {.(force g)} {x} {w1} {w2} {w} nnf nng cf cg comp ind updRel-upd gtn compat wgt0 eqn rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , upd name f , force g , w1 , refl , refl , updRel-upd


steps-decomp-isHighestℕ : {w w1 w2 : 𝕎·} {a b v : Term} {n m : ℕ} (i : ℕ) (name : Name)
              → isValue v
              → (comp1 : steps m (a , w) ≡ (b , w1))
              → (comp2 : steps n (a , w) ≡ (v , w2))
              → Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
                  isHighestℕ {n} {w} {w2} {a} {v} i name comp2
                  → isHighestℕ {k} {w1} {w2} {b} {v} i name comp))
steps-decomp-isHighestℕ {w} {w1} {w2} {a} {b} {v} {n} {0} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = n , ≤-refl , comp2 , λ x → x
steps-decomp-isHighestℕ {w} {w1} {w2} {a} {b} {v} {0} {suc m} i name isv comp1 comp2
  rewrite pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
        | stepVal a w isv
        | stepsVal a w m isv
        | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1)
  = 0 , ≤-refl , refl , λ (j , e , q) → j , e , <-≤-trans ≤-refl q
steps-decomp-isHighestℕ {w} {w1} {w2} {a} {b} {v} {suc n} {suc m} i name isv comp1 comp2 with step⊎ a w
... | inj₁ (a' , w' , z) rewrite z =
  fst q , ≤-trans (fst (snd q)) (<⇒≤ (n<1+n n)) , fst (snd (snd q)) , λ (x1 , x2) → snd (snd (snd q)) x2
  where
    q : Σ ℕ (λ k → k ≤ n × Σ (steps k (b , w1) ≡ (v , w2)) (λ comp →
           isHighestℕ {n} {w'} {w2} {a'} {v} i name comp2
           → isHighestℕ {k} {w1} {w2} {b} {v} i name comp))
    q = steps-decomp-isHighestℕ {w'} {w1} {w2} {a'} {b} {v} {n} {m} i name isv comp1 comp2
... | inj₂ z rewrite z
           | pair-inj₁ (sym comp2) | pair-inj₂ (sym comp2)
           | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = 0 , _≤_.z≤n , refl , λ x → x



steps-updRel-aux : (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term}
                   → ¬Names f
                   → ¬Names g
                   → # f
                   → # g
                   → (k : ℕ)
                   → (ind : (k' : ℕ) → k' < k → presUpdRel n name f g k')
                   → presUpdRel n name f g k
steps-updRel-aux gc {n} {name} {f} {g} nnf nng cf cg 0 ind {a} {b} {v} {w1} {w2} {w} r compat wgt0 eqw comp ish isv
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = 0 , b , refl , r
steps-updRel-aux gc {n} {name} {f} {g} nnf nng cf cg (suc k) ind {a} {b} {v} {w1} {w2} {w} r compat wgt0 eqw comp ish isv
  with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z =
  k2 + k4 , v' , steps-trans+ {k2} {k4} {b} {y2} {v'} {w} {w} {w} comp2 comp4 , ur'
  where
    ind0 : (k' : ℕ) → k' < suc k → presUpdRel n name f g k'
    ind0 = ind

    ind1 : (k' : ℕ) → k' ≤ k → presUpdRel n name f g k'
    ind1 k' ltk = ind0 k' (_≤_.s≤s ltk)

    spres : stepsPresUpdRel n name f g a' w1'
    spres = k , v , w2 , comp , isv , snd ish , ind1

    s : ΣstepsUpdRel name f g a' w1' b w
    s = step-updRel gc {n} {name} {f} {g} {a} {b} {a'} {w1} {w1'} {w} nnf nng cf cg z spres r (fst ish) compat wgt0 eqw

    k1 : ℕ
    k1 = fst s

    k2 : ℕ
    k2 = fst (snd s)

    y1 : Term
    y1 = fst (snd (snd s))

    y2 : Term
    y2 = fst (snd (snd (snd s)))

    w3 : 𝕎·
    w3 = fst (snd (snd (snd (snd s))))

    comp1 : steps k1 (a' , w1') ≡ (y1 , w3)
    comp1 = fst (snd (snd (snd (snd (snd s)))))

    comp2 : steps k2 (b , w) ≡ (y2 , w)
    comp2 = fst (snd (snd (snd (snd (snd (snd s))))))

    ur : updRel name f g y1 y2
    ur = snd (snd (snd (snd (snd (snd (snd s))))))

    q : Σ ℕ (λ k3 → k3 ≤ k × Σ (steps k3 (y1 , w3) ≡ (v , w2)) (λ comp' →
                  isHighestℕ {k} {w1'} {w2} {a'} {v} n name comp
                  → isHighestℕ {k3} {w3} {w2} {y1} {v} n name comp'))
    q = steps-decomp-isHighestℕ {w1'} {w3} {w2} {a'} {y1} {v} {k} {k1} n name isv comp1 comp

    k3 : ℕ
    k3 = fst q

    ltk2 : k3 ≤ k
    ltk2 = fst (snd q)

    comp3 : steps k3 (y1 , w3) ≡ (v , w2)
    comp3 = fst (snd (snd q))

    ish' : isHighestℕ {k3} {w3} {w2} {y1} {v} n name comp3
    ish' = snd (snd (snd q)) (snd ish)

    e3 : w1 ⊑· w3
    e3 = ⊑-trans· (step⊑ {w1} {w1'} {a} {a'} z) (steps→⊑ k1 a' y1 {w1'} {w3} comp1)

    c : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (y2 , w) ≡ (v' , w) × updRel name f g v v'))
    c = ind1 k3 ltk2 {y1} {y2} {v} {w3} {w2} {w} ur (⊑-compatible· e3 compat) (∀𝕎-mon e3 wgt0) (∀𝕎-mon e3 eqw) comp3 ish' isv

    k4 : ℕ
    k4 = fst c

    v' : Term
    v' = fst (snd c)

    comp4 : steps k4 (y2 , w) ≡ (v' , w)
    comp4 = fst (snd (snd c))

    ur' : updRel name f g v v'
    ur' = snd (snd (snd c))
... | inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | stepVal a w1 isv =
  ⊥-elim (¬just≡nothing z)



steps-updRel : (gc : get-choose-ℕ) {n : ℕ} {name : Name} {f g : Term} {k : ℕ}
               → ¬Names f
               → ¬Names g
               → # f
               → # g
               → presUpdRel n name f g k
steps-updRel gc {n} {name} {f} {g} {k} nnf nng cf cg =
  <ℕind _ (steps-updRel-aux gc {n} {name} {f} {g} nnf nng cf cg) k



abstract

  updRel-refl : {name : Name} {f g a : Term}
                → ¬names a ≡ true
                → updRel name f g a a
  updRel-refl {name} {f} {g} {VAR x} nn = updRel-VAR _
--  updRel-refl {name} {f} {g} {NAT} nn = updRel-NAT
  updRel-refl {name} {f} {g} {QNAT} nn = updRel-QNAT
--  updRel-refl {name} {f} {g} {TNAT} nn = updRel-TNAT
  updRel-refl {name} {f} {g} {LT a a₁} nn = updRel-LT _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {QLT a a₁} nn = updRel-QLT _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {NUM x} nn = updRel-NUM _
  updRel-refl {name} {f} {g} {IFLT a a₁ a₂ a₃} nn = updRel-IFLT _ _ _ _ _ _ _ _ (updRel-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updRel-refl {name} {f} {g} {IFEQ a a₁ a₂ a₃} nn = updRel-IFEQ _ _ _ _ _ _ _ _ (updRel-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updRel-refl {name} {f} {g} {SUC a} nn = updRel-SUC _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {NATREC a a₁ a₂} nn = updRel-NATREC _ _ _ _ _ _ (updRel-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  updRel-refl {name} {f} {g} {PI a a₁} nn = updRel-PI _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {LAMBDA a} nn = updRel-LAMBDA _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {APPLY a a₁} nn = updRel-APPLY _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {FIX a} nn = updRel-FIX _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {LET a a₁} nn = updRel-LET _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {WT a a₁ a₂} nn = updRel-WT _ _ _ _ _ _ (updRel-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  updRel-refl {name} {f} {g} {SUP a a₁} nn = updRel-SUP _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  --updRel-refl {name} {f} {g} {DSUP a a₁} nn = updRel-DSUP _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {WREC a a₁} nn = updRel-WREC _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {MT a a₁ a₂} nn = updRel-MT _ _ _ _ _ _ (updRel-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  --updRel-refl {name} {f} {g} {MSUP a a₁} nn = updRel-MSUP _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  --updRel-refl {name} {f} {g} {DMSUP a a₁} nn = updRel-DMSUP _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {SUM a a₁} nn = updRel-SUM _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {PAIR a a₁} nn = updRel-PAIR _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {SPREAD a a₁} nn = updRel-SPREAD _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {SET a a₁} nn = updRel-SET _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {ISECT a a₁} nn = updRel-ISECT _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {TUNION a a₁} nn = updRel-TUNION _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {UNION a a₁} nn = updRel-UNION _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
--  updRel-refl {name} {f} {g} {QTUNION a a₁} nn = updRel-QTUNION _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {INL a} nn = updRel-INL _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {INR a} nn = updRel-INR _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {DECIDE a a₁ a₂} nn = updRel-DECIDE _ _ _ _ _ _ (updRel-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  updRel-refl {name} {f} {g} {EQ a a₁ a₂} nn = updRel-EQ _ _ _ _ _ _ (updRel-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updRel-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
--  updRel-refl {name} {f} {g} {EQB a a₁ a₂ a₃} nn = updRel-EQB _ _ _ _ _ _ _ _ (updRel-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updRel-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updRel-refl {name} {f} {g} {AX} nn = updRel-AX
  updRel-refl {name} {f} {g} {FREE} nn = updRel-FREE
  updRel-refl {name} {f} {g} {MSEQ s} nn = updRel-MSEQ s
  updRel-refl {name} {f} {g} {MAPP s a} nn = updRel-MAPP _ _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {CHOOSE a a₁} nn = updRel-CHOOSE _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
--  updRel-refl {name} {f} {g} {TSQUASH a} nn = updRel-TSQUASH _ _ (updRel-refl nn)
--  updRel-refl {name} {f} {g} {TTRUNC a} nn = updRel-TTRUNC _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {NOWRITE} nn = updRel-NOWRITE
  updRel-refl {name} {f} {g} {NOREAD}  nn = updRel-NOREAD
  updRel-refl {name} {f} {g} {SUBSING a} nn = updRel-SUBSING _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {PURE} nn = updRel-PURE
  updRel-refl {name} {f} {g} {NOSEQ} nn = updRel-NOSEQ
  updRel-refl {name} {f} {g} {NOENC} nn = updRel-NOENC
  updRel-refl {name} {f} {g} {TERM a} nn = updRel-TERM _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {ENC a} nn = updRel-ENC _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {PARTIAL a} nn = updRel-PARTIAL _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {FFDEFS a a₁} nn = updRel-FFDEFS _ _ _ _ (updRel-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updRel-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updRel-refl {name} {f} {g} {UNIV x} nn = updRel-UNIV x
  updRel-refl {name} {f} {g} {LIFT a} nn = updRel-LIFT _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {LOWER a} nn = updRel-LOWER _ _ (updRel-refl nn)
  updRel-refl {name} {f} {g} {SHRINK a} nn = updRel-SHRINK _ _ (updRel-refl nn)


steps-updRel-app : (gc : get-choose-ℕ) {n : ℕ} {name : Name} {F f g v : Term} {k : ℕ} {w1 w2 w : 𝕎·}
                   → ¬Names F
                   → ¬Names f
                   → ¬Names g
                   → # f
                   → # g
                   → compatible· name w1 Res⊤
                   → ∀𝕎-get0-NUM w1 name
                   → ∀𝕎 w1 (λ w' _ → (k : ℕ) → k < n → strongMonEq w' (APPLY f (NUM k)) (APPLY g (NUM k)))
                   → (comp : steps k (APPLY F (upd name f)  , w1) ≡ (v , w2))
                   → isHighestℕ {k} {w1} {w2} {APPLY F (upd name f)} {v} n name comp
                   → isValue v
                   → Σ ℕ (λ k' → Σ Term (λ v' → steps k' (APPLY F (force g) , w) ≡ (v' , w) × updRel name f g v v'))
steps-updRel-app gc {n} {name} {F} {f} {g} {v} {k} {w1} {w2} {w} nnF nnf nng cf cg compat wgt0 eqn comp ish isv =
  steps-updRel
    gc {n} {name} {f} {g} {k}
    nnf nng cf cg
    {APPLY F (upd name f)} {APPLY F (force g)} {v} {w1} {w2} {w}
    (updRel-APPLY F F (upd name f) (force g) (updRel-refl nnF) updRel-upd)
    compat wgt0 eqn comp ish isv
\end{code}
