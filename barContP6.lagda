\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --experimental-lossy-unification #-}
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
open import encode


module barContP6 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
                 (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC)
open import terms4(W)(C)(K)(G)(X)(N)(EC)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
--open import terms6(W)(C)(K)(G)(X)(N)(EC)
--open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC) using (#APPLY2)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (NATmem)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-TPURE→ₗ ; equalInType-TPURE→)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#upd)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (isHighestℕ→getT≤ℕ ; ¬Names→updCtxt ; steps-sat-isHighestℕ)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (steps-trans+)
open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (steps-decomp-isHighestℕ)
--open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (updSeq-step)



abstract
  updSeq-refl : {r : Name} {s : 𝕊} {n : ℕ} {a : Term}
                → ¬names a ≡ true
                → updSeq r s n a a
  updSeq-refl {r} {s} {n} {VAR x} nn = updSeq-VAR _
  updSeq-refl {r} {s} {n} {NAT} nn = updSeq-NAT
  updSeq-refl {r} {s} {n} {QNAT} nn = updSeq-QNAT
  updSeq-refl {r} {s} {n} {TNAT} nn = updSeq-TNAT
  updSeq-refl {r} {s} {n} {LT a a₁} nn = updSeq-LT _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {QLT a a₁} nn = updSeq-QLT _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {NUM x} nn = updSeq-NUM _
  updSeq-refl {r} {s} {n} {IFLT a a₁ a₂ a₃} nn = updSeq-IFLT _ _ _ _ _ _ _ _ (updSeq-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updSeq-refl {r} {s} {n} {IFEQ a a₁ a₂ a₃} nn = updSeq-IFEQ _ _ _ _ _ _ _ _ (updSeq-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updSeq-refl {r} {s} {n} {SUC a} nn = updSeq-SUC _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {PI a a₁} nn = updSeq-PI _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {LAMBDA a} nn = updSeq-LAMBDA _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {APPLY a a₁} nn = updSeq-APPLY _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {FIX a} nn = updSeq-FIX _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {LET a a₁} nn = updSeq-LET _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {WT a a₁} nn = updSeq-WT _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {SUP a a₁} nn = updSeq-SUP _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  --updSeq-refl {r} {s} {n} {DSUP a a₁} nn = updSeq-DSUP _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {WREC a a₁} nn = updSeq-WREC _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {MT a a₁} nn = updSeq-MT _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  --updSeq-refl {r} {s} {n} {MSUP a a₁} nn = updSeq-MSUP _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  --updSeq-refl {r} {s} {n} {DMSUP a a₁} nn = updSeq-DMSUP _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {SUM a a₁} nn = updSeq-SUM _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {PAIR a a₁} nn = updSeq-PAIR _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {SPREAD a a₁} nn = updSeq-SPREAD _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {SET a a₁} nn = updSeq-SET _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {ISECT a a₁} nn = updSeq-ISECT _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {TUNION a a₁} nn = updSeq-TUNION _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {UNION a a₁} nn = updSeq-UNION _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {QTUNION a a₁} nn = updSeq-QTUNION _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {INL a} nn = updSeq-INL _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {INR a} nn = updSeq-INR _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {DECIDE a a₁ a₂} nn = updSeq-DECIDE _ _ _ _ _ _ (updSeq-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updSeq-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updSeq-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  updSeq-refl {r} {s} {n} {EQ a a₁ a₂} nn = updSeq-EQ _ _ _ _ _ _ (updSeq-refl (∧≡true→1-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updSeq-refl (∧≡true→2-3 {¬names a} {¬names a₁} {¬names a₂} nn)) (updSeq-refl (∧≡true→3-3 {¬names a} {¬names a₁} {¬names a₂} nn))
  updSeq-refl {r} {s} {n} {EQB a a₁ a₂ a₃} nn = updSeq-EQB _ _ _ _ _ _ _ _ (updSeq-refl (∧≡true→1-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→2-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→3-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn)) (updSeq-refl (∧≡true→4-4 {¬names a} {¬names a₁} {¬names a₂} {¬names a₃} nn))
  updSeq-refl {r} {s} {n} {AX} nn = updSeq-AX
  updSeq-refl {r} {s} {n} {FREE} nn = updSeq-FREE
  updSeq-refl {r} {s} {n} {MSEQ x} nn = updSeq-MSEQ x
  updSeq-refl {r} {s} {n} {MAPP x a} nn = updSeq-MAPP _ _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {CHOOSE a a₁} nn = updSeq-CHOOSE _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {TSQUASH a} nn = updSeq-TSQUASH _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {TTRUNC a} nn = updSeq-TTRUNC _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {TCONST a} nn = updSeq-TCONST _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {SUBSING a} nn = updSeq-SUBSING _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {PURE} nn = updSeq-PURE
  updSeq-refl {r} {s} {n} {TERM a} nn = updSeq-TERM _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {ENC a} nn = updSeq-ENC _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {DUM a} nn = updSeq-DUM _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {FFDEFS a a₁} nn = updSeq-FFDEFS _ _ _ _ (updSeq-refl (∧≡true→ₗ (¬names a) (¬names a₁) nn)) (updSeq-refl (∧≡true→ᵣ (¬names a) (¬names a₁) nn))
  updSeq-refl {r} {s} {n} {UNIV x} nn = updSeq-UNIV x
  updSeq-refl {r} {s} {n} {LIFT a} nn = updSeq-LIFT _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {LOWER a} nn = updSeq-LOWER _ _ (updSeq-refl nn)
  updSeq-refl {r} {s} {n} {SHRINK a} nn = updSeq-SHRINK _ _ (updSeq-refl nn)


updSeq-steps-aux : (cn : cℕ) (gc : get-choose-ℕ) (r : Name) (s : 𝕊) (n : ℕ)
                   (k : ℕ)
                   (ind : (k' : ℕ) → k' < k → updSeqSteps r s n k')
                   → updSeqSteps r s n k
updSeq-steps-aux cn gc r s n 0 ind {t} {u} {x} {w1} {w2} compat us comp ish isv
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp)
  = 0 , u , refl , us
updSeq-steps-aux cn gc r s n (suc k) ind {t} {u} {x} {w1} {w2} compat us comp ish isv with step⊎ t w1
... | inj₁ (t' , w1' , p) rewrite p =
  concl
  where
    ind0 : (k' : ℕ) → k' ≤ k → updSeqSteps r s n k'
    ind0 k' ltk = ind k' (_≤_.s≤s ltk)

    ind' : updSeqStepInd r s n t' w1'
    ind' = k , x , w2 , comp , snd ish , isv , ind0

    gtn : getT≤ℕ w1' n r
    gtn = isHighestℕ→getT≤ℕ {k} {w1'} {w2} {t'} {x} n r comp (snd ish)

    concl : Σ ℕ (λ k' → Σ Term (λ v' → Σ (steps k' (u , w1) ≡ (v' , w2)) (λ x₁ → updSeq r s n x v')))
    concl with updSeq-step cn gc w1 w1' r s n t u t' us gtn compat p ind'
    ... | (k1 , k2 , y , z , w3 , comp1 , comp2 , us1)
      with steps-decomp-isHighestℕ {w1'} {w3} {w2} {t'} {y} {x} {k} {k1} n r isv comp1 comp
    ... | (k3 , ltk , comp' , ishi) =
      k2 + fst q , fst (snd q) ,
      steps-trans+ {k2} {fst q} {u} {z} {fst (snd q)} {w1} {w3} {w2} comp2 (fst (snd (snd q))) ,
      snd (snd (snd q))
      where
        e3 : w1 ⊑· w3
        e3 = steps→⊑ k2 u z {w1} {w3} comp2

        q : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (z , w3) ≡ (v' , w2) × updSeq r s n x v'))
        q = ind k3 (<-transʳ ltk ≤-refl) {y} {z} {x} {w3} {w2} (⊑-compatible· e3 compat) us1 comp' (ishi (snd ish)) isv
... | inj₂ q rewrite q | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) | stepVal t w1 isv = ⊥-elim (¬just≡nothing q)


updSeq-steps : (cn : cℕ) (gc : get-choose-ℕ) (r : Name) (s : 𝕊) (n : ℕ)
               (k : ℕ)
               → updSeqSteps r s n k
updSeq-steps cn gc r s n k = <ℕind _ (updSeq-steps-aux cn gc r s n) k


updSeq-steps-NUM : (cn : cℕ) (gc : get-choose-ℕ) (r : Name) (s : 𝕊) (n : ℕ)
                   (k : ℕ)
                   (a b : Term) (m : ℕ) (w1 w2 : 𝕎·)
                   → compatible· r w1 Res⊤
                   → updSeq r s n a b
                   → (comp : steps k (a , w1) ≡ (NUM m , w2))
                   → isHighestℕ {k} {w1} {w2} {a} {NUM m} n r comp
                   → Σ ℕ (λ k' → steps k' (b , w1) ≡ (NUM m , w2))
updSeq-steps-NUM cn gc r s n k a b m w1 w2 compat us comp ish
  with updSeq-steps cn gc r s n k {a} {b} {NUM m} {w1} {w2} compat us comp ish tt
... | (k' , v' , comp' , us') rewrite updSeq-NUM→ r s n m v' us' = k' , comp'


seq2list≡ : (s : 𝕊) (n : ℕ) → ⌜ seq2list s n ⌝ ≡ s2l s n
seq2list≡ s 0 = refl
seq2list≡ s (suc n) rewrite seq2list≡ s n = refl


#updSeq-upd : (r : Name) (s : 𝕊) (n : ℕ)
              → updSeq r s n ⌜ #upd r (#MSEQ s) ⌝ ⌜ #upd r (seq2list s n) ⌝
#updSeq-upd r s n rewrite seq2list≡ s n = updSeq-upd


#updSeq-updr : (r : Name) (s : 𝕊) (n : ℕ)
               → updSeq r s n ⌜ #upd r (seq2list s n) ⌝ ⌜ #upd r (#MSEQ s) ⌝
#updSeq-updr r s n rewrite seq2list≡ s n = updSeq-updr


#updSeq-APPLY-upd : (r : Name) (s : 𝕊) (n : ℕ) (F : CTerm) (nnF : #¬Names F)
                    → updSeq r s n ⌜ #APPLY F (#upd r (#MSEQ s)) ⌝ ⌜ #APPLY F (#upd r (seq2list s n)) ⌝
#updSeq-APPLY-upd r s n F nnF =
  updSeq-APPLY ⌜ F ⌝ ⌜ F ⌝ ⌜ #upd r (#MSEQ s) ⌝ ⌜ #upd r (seq2list s n) ⌝ (updSeq-refl nnF) (#updSeq-upd r s n)


#updSeq-APPLY-updr : (r : Name) (s : 𝕊) (n : ℕ) (F : CTerm) (nnF : #¬Names F)
                     → updSeq r s n ⌜ #APPLY F (#upd r (seq2list s n)) ⌝ ⌜ #APPLY F (#upd r (#MSEQ s)) ⌝
#updSeq-APPLY-updr r s n F nnF =
  updSeq-APPLY ⌜ F ⌝ ⌜ F ⌝ ⌜ #upd r (seq2list s n) ⌝ ⌜ #upd r (#MSEQ s) ⌝ (updSeq-refl nnF) (#updSeq-updr r s n)


≡getT≤ℕ→< : (w w' : 𝕎·) (r : Name) (n j : ℕ)
             → w ≡ w'
             → getT 0 r w ≡ just (NUM j)
             → getT≤ℕ w' n r
             → j < n
≡getT≤ℕ→< w w' r n j e gt1 (k , gt2 , ltj) rewrite e | gt2 | NUMinj (just-inj gt1) = ltj


path-mon : {i : ℕ} {w w' : 𝕎·} {A : CTerm} {B : CTerm0}
           → w ⊑· w'
           → path i w A B
           → path i w' A B
path-mon {i} {w} {w'} {A} {B} e p n with p n
... | inj₁ (a , b , a∈ , b∈) = inj₁ (a , b , equalInType-mon a∈ w' e , equalInType-mon b∈ w' e)
... | inj₂ x = inj₂ tt


correctPathN-mon : (i : ℕ) (w w' : 𝕎·) (e : w ⊑· w') (t : CTerm) (A : CTerm) (B : CTerm0) (p : path i w A B) (n : ℕ)
                  → correctPathN {i} {w} {A} {B} t p n
                  → correctPathN {i} {w'} {A} {B} t (path-mon {i} {w} {w'} {A} {B} e p) n
correctPathN-mon i w w' e t A B p 0 cor = cor
correctPathN-mon i w w' e t A B p (suc n) cor with p 0
... | inj₁ (a , b , a∈ , b∈) with p n
... |    inj₁ (a0 , b0 , a0∈ , b0∈) =
  fst cor ,
  ∀𝕎-mon e (fst (snd cor)) ,
  correctPathN-mon i w w' e (#APPLY (proj₁ cor) b) A B _ n (snd (snd cor))
... |    inj₂ x =
  fst cor ,
  ∀𝕎-mon e (fst (snd cor)) ,
  correctPathN-mon i w w' e (#APPLY (proj₁ cor) b) A B _ n (snd (snd cor))
correctPathN-mon i w w' e t A B p (suc n) cor | inj₂ x = cor


correctPath-mon : (i : ℕ) (w w' : 𝕎·) (e : w ⊑· w') (t : CTerm) (A : CTerm) (B : CTerm0) (p : path i w A B)
                  → correctPath {i} {w} {A} {B} t p
                  → correctPath {i} {w'} {A} {B} t (path-mon {i} {w} {w'} {A} {B} e p)
correctPath-mon i w w' e t A B p cor n =
  correctPathN-mon i w w' e t A B p n (cor n)


isInfPath-mon : (i : ℕ) (w w' : 𝕎·) (e : w ⊑· w') (A : CTerm) (B : CTerm0) (p : path i w A B)
                → isInfPath {i} {w} {A} {B} p
                → isInfPath {i} {w'} {A} {B} (path-mon {i} {w} {w'} {A} {B} e p)
isInfPath-mon i w w' e A B p j n with j n
... | y with p n
... | inj₁ (a , b , a∈ , b∈) = tt
... | inj₂ x = y


infPath-mon : (i : ℕ) (w w' : 𝕎·) (t : CTerm) (A : CTerm) (B : CTerm0)
              → w ⊑· w'
              → (p : path i w A B)
              → correctPath {i} {w} {A} {B} t p
              → isInfPath {i} {w} {A} {B} p
              → Σ (path i w' A B) (λ p' →
                  correctPath {i} {w'} {A} {B} t p'
                  × isInfPath {i} {w'} {A} {B} p')
infPath-mon i w w' t A B e p cor inf =
  path-mon {i} {w} {w'} {A} {B} e p ,
  correctPath-mon i w w' e t A B p cor ,
  isInfPath-mon i w w' e A B p inf


-- We want to create a Term ∈ BAIRE from this path.
noInfPath : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (r : Name) (P : ℕ → Set) (T F : CTerm)
            (tyn : type-#⇛!-NUM P T) (prest : type-preserves-#⇛ T) (tyt : isType i w T)
            → #¬Names F -- This is currently required by continuity
            → compatible· r w Res⊤
            → ∈Type i w (#FunBar T) F
            → (p : path i w #IndBarB (#IndBarC T))
            → correctPath {i} {w} {#IndBarB} {#IndBarC T} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
            → isInfPath {i} {w} {#IndBarB} {#IndBarC T} p
            → ⊥
noInfPath kb cn can exb gc i w r P T F tyn prest tyt nnF compat F∈ p cor inf =
  ltsn (≡getT≤ℕ→< w0 w' r (suc n) j eqw' gt0 gtn)
  where
    s : 𝕊
    s = path2𝕊 kb P tyn p

    f : CTerm
    f = #MSEQ s

    nnf : #¬Names f
    nnf = refl

    f∈ : ∈Type i w #BAIRE f
    f∈ = mseq∈baire i w s

    a∈1 : ∈Type i w #NAT (#APPLY F (#upd r f))
    a∈1 = equalInType-FUN→ F∈ w (⊑-refl· _) (#upd r f) (#upd r f) (upd∈BAIRE cn i w r T f compat prest {!tyt!} {!!}) -- f∈

    a∈2 : NATmem w (#APPLY F (#upd r f))
    a∈2 = kb (equalInType-NAT→ i w (#APPLY F (#upd r f)) (#APPLY F (#upd r f)) a∈1) w (⊑-refl· w)

    k : ℕ
    k = fst a∈2

    w1 : 𝕎·
    w1 = chooseT r w N0

    e1 : w ⊑· w1
    e1 = choose⊑· r w (T→ℂ· N0)

    ca1 : Σ 𝕎· (λ w' → #APPLY F (#upd r f) #⇓ #NUM k from w1 to w')
    ca1 = #⇓→from-to {w1} {#APPLY F (#upd r f)} {#NUM k} (lower (fst (snd a∈2) w1 e1)) --w (⊑-refl· w)))

    w' : 𝕎·
    w' = fst ca1

    ca2 : #APPLY F (#upd r f) #⇓ #NUM k from w1 to w'
    ca2 = snd ca1

    e' : w ⊑· w'
    e' = ⊑-trans· e1 (#⇓from-to→⊑ {w1} {w'} {#APPLY F (#upd r f)} {#NUM k} ca2)

    d1 : Σ ℕ (λ n → getT 0 r w' ≡ just (NUM n))
    d1 = lower (cn r w compat w' e')

    n : ℕ
    n = fst d1

    gt : getT 0 r w' ≡ just (NUM n)
    gt = snd d1

    wgt0 : ∀𝕎-get0-NUM w1 r
    wgt0 = cn r w1 (⊑-compatible· e1 compat)

    gtn : getT≤ℕ w' (suc n) r
    gtn = n , gt , ≤-refl

    uc : updCtxt r ⌜ f ⌝ ⌜ #APPLY F (#upd r f) ⌝
    uc = updCtxt-APPLY ⌜ F ⌝ ⌜ #upd r f ⌝ (¬Names→updCtxt {r} {⌜ f ⌝} {⌜ F ⌝} nnF) updCtxt-upd

    -- all values of r along (snd ca2) are strictly less than (suc n) - the modulus of continuity
    ish : isHighestℕ {fst ca2} {w1} {w'} {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} (suc n) r (snd ca2)
    ish = steps-sat-isHighestℕ
            gc {r} {⌜ f ⌝} {fst ca2} nnf (CTerm.closed f) {w1} {w'}
            {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} {suc n} (snd ca2)
            tt uc (⊑-compatible· e1 compat) wgt0 gtn

    cs : correctSeq r w F s
    cs = corSeq→correctSeq r w F s (→corSeq kb cn i w r P T F tyn compat F∈ p cor inf)

    csn : correctSeqN r w F 0 #INIT s (suc (suc n))
    csn = cs (suc (suc n))

    inv : Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
            #APPLY F (#upd r (seq2list s (suc n))) #⇓ #NUM m from (chooseT r w N0) to w'
            × getT 0 r w' ≡ just (NUM j)
            × ¬ j < (suc n))))
    inv = correctSeqN-inv0 i r w F s (suc n) csn

    m0 : ℕ
    m0 = fst inv

    w0 : 𝕎·
    w0 = fst (snd inv)

    j : ℕ
    j = fst (snd (snd inv))

    comp0 : #APPLY F (#upd r (seq2list s (suc n))) #⇓ #NUM m0 from (chooseT r w N0) to w0
    comp0 = fst (snd (snd (snd inv)))

    gt0 : getT 0 r w0 ≡ just (NUM j)
    gt0 = fst (snd (snd (snd (snd inv))))

    ltsn : ¬ j < (suc n)
    ltsn = snd (snd (snd (snd (snd inv))))

    c : Σ ℕ (λ k' → steps k' (⌜ #APPLY F (#upd r (seq2list s (suc n))) ⌝ , chooseT r w N0) ≡ (NUM k , w'))
    c = updSeq-steps-NUM
          cn gc r s (suc n) (fst ca2)
          ⌜ #APPLY F (#upd r f) ⌝ ⌜ #APPLY F (#upd r (seq2list s (suc n))) ⌝
          k w1 w' (⊑-compatible· e1 compat)
          (#updSeq-APPLY-upd r s (suc n) F nnF)
          (snd ca2) ish

    eqw' : w0 ≡ w'
    eqw' = steps→≡𝕎 (chooseT r w N0) w0 w' ⌜ #APPLY F (#upd r (seq2list s (suc n))) ⌝ (NUM m0) (NUM k) (fst comp0) (fst c) tt tt (snd comp0) (snd c)


FunBarP : Term → Term
FunBarP T = TPURE (FunBar T)


barThesisP : Term → Term
barThesisP T = FUN (FunBarP T) (IndBar T)


#FunBarP : CTerm → CTerm
#FunBarP T = #TPURE (#FunBar T)


#barThesisP : CTerm → CTerm
#barThesisP T = #FUN (#FunBarP T) (#IndBar T)


-- comp→∀ℕ is stronger than cℕ. get rid of cℕ?
sem : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
      (i : ℕ) (w : 𝕎·) (r : Name) (P : ℕ → Set) (T F : CTerm)
--      → #¬Names F -- This is currently required by continuity (captured by #FunBarP)
      → type-preserves-#⇛ T
      → type-#⇛!-NUM P T
      → #⇛!-NUM-type P T
      → isType i w T
      → compatible· r w Res⊤
      → ∈Type i w (#FunBarP T) F
      → ∈Type i w (#IndBar T) (#APPLY2 (#loop r F) (#NUM 0) #INIT)
sem kb cn can exb gc i w r P T F {--nnF--} prest tyn nty tyt compat F∈P = concl
  where
    nnF  : #¬Names F
    nnF = equalInType-TPURE→ₗ F∈P

    F∈ : ∈Type i w (#FunBar T) F
    F∈ = equalInType-TPURE→ F∈P

    co : ∈Type i w (#CoIndBar T) (#APPLY2 (#loop r F) (#NUM 0) #INIT)
    co = coSem can gc kb cn i w r P T F (#NUM 0) #INIT refl refl nnF prest tyn nty tyt compat F∈ (NUM-equalInType-NAT! i w 0) {!!} --(LAM0∈BAIRE i w)

    concl : ∈Type i w (#IndBar T) (#APPLY2 (#loop r F) (#NUM 0) #INIT)
    concl with EM {∃𝕎 w (λ w' _ → Σ (path i w' #IndBarB (#IndBarC T))
                                   (λ p → correctPath {i} {w'} {#IndBarB} {#IndBarC T} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
                                         × isInfPath {i} {w'} {#IndBarB} {#IndBarC T} p))}
    ... | yes (w' , e' , p , cor , inf) = c
      where
        c : ∈Type i w (#IndBar T) (#APPLY2 (#loop r F) (#NUM 0) #INIT)
        c = ⊥-elim (noInfPath kb cn can exb gc i w' r P T F tyn prest {!eqTypes-mon!} nnF (⊑-compatible· e' compat) (equalInType-mon F∈ w' e') p cor inf )
    ... | no pp = CoIndBar2IndBar i w T (#APPLY2 (#loop r F) (#NUM 0) #INIT) tyt cond co
      where
        cond : ∀𝕎 w (λ w' _ → (p : path i w' #IndBarB (#IndBarC T))
               → correctPath {i} {w'} {#IndBarB} {#IndBarC T} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
               → isFinPath {i} {w'} {#IndBarB} {#IndBarC T} p)
        cond w1 e1 p cor with EM {Lift {0ℓ} (lsuc(L)) (isFinPath {i} {w1} {#IndBarB} {#IndBarC T} p)}
        ... | yes qq = lower qq
        ... | no qq = ⊥-elim (pp (w1 , e1 , p , cor , ¬isFinPath→isInfPath {i} {w1} {#IndBarB} {#IndBarC T} p (λ z → qq (lift z))))

--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?



{--

Plan:

(1) Prove by coinduction that if (F ∈ FunBar) then (loop r F ∈ CoIndBar) which does not require to proving termination
    - see coSem, which uses coSemM [DONE]
(2) We now have an inhabitant (t ∈ CoIndBar). Using classical logic, either t's paths are all finite,
    or it has an inifite path.
    - see sem [DONE]
(3) If all its paths are finite then we get that (t ∈ IndBar)
    - see m2w [DONE]
(4) If it has an inifite path:
    - That path corresponds to an (α ∈ Baire).
    - Given (F ∈ FunBar), by continuity let n be F's modulus of continuity w.r.t. α.
    - So, it must be that F(generic r α|n) returns r:=BTRUE and so loop returns ETA, and the path cannot be infinite
          (where α|n is the initial segment of α of length n)

 --}

\end{code}
