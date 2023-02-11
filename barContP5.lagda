\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --experimental-lossy-unification #-}
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


module barContP5 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)

open import terms2(W)(C)(K)(G)(X)(N)
open import terms3(W)(C)(K)(G)(X)(N)
--open import terms4(W)(C)(K)(G)(X)(N)
--open import terms5(W)(C)(K)(G)(X)(N)
open import terms6(W)(C)(K)(G)(X)(N)
--open import terms7(W)(C)(K)(G)(X)(N)
open import terms8(W)(C)(K)(G)(X)(N)

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

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)




updSeq→isValue : {r : Name} {s : 𝕊} {n : ℕ} {a b : Term}
                  → updSeq r s n a b
                  → isValue a
                  → isValue b
updSeq→isValue {r} {s} {n} {.NAT} {.NAT} updSeq-NAT isv = tt
updSeq→isValue {r} {s} {n} {.QNAT} {.QNAT} updSeq-QNAT isv = tt
updSeq→isValue {r} {s} {n} {.TNAT} {.TNAT} updSeq-TNAT isv = tt
updSeq→isValue {r} {s} {n} {.(LT a₁ b₁)} {.(LT a₂ b₂)} (updSeq-LT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(QLT a₁ b₁)} {.(QLT a₂ b₂)} (updSeq-QLT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(NUM x)} {.(NUM x)} (updSeq-NUM x) isv = tt
updSeq→isValue {r} {s} {n} {.(PI a₁ b₁)} {.(PI a₂ b₂)} (updSeq-PI a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(LAMBDA a₁)} {.(LAMBDA a₂)} (updSeq-LAMBDA a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(WT a₁ b₁)} {.(WT a₂ b₂)} (updSeq-WT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(SUP a₁ b₁)} {.(SUP a₂ b₂)} (updSeq-SUP a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(MT a₁ b₁)} {.(MT a₂ b₂)} (updSeq-MT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(MSUP a₁ b₁)} {.(MSUP a₂ b₂)} (updSeq-MSUP a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(SUM a₁ b₁)} {.(SUM a₂ b₂)} (updSeq-SUM a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(PAIR a₁ b₁)} {.(PAIR a₂ b₂)} (updSeq-PAIR a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(SET a₁ b₁)} {.(SET a₂ b₂)} (updSeq-SET a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(ISECT a₁ b₁)} {.(ISECT a₂ b₂)} (updSeq-ISECT a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(TUNION a₁ b₁)} {.(TUNION a₂ b₂)} (updSeq-TUNION a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(UNION a₁ b₁)} {.(UNION a₂ b₂)} (updSeq-UNION a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(QTUNION a₁ b₁)} {.(QTUNION a₂ b₂)} (updSeq-QTUNION a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(INL a₁)} {.(INL a₂)} (updSeq-INL a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(INR a₁)} {.(INR a₂)} (updSeq-INR a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(EQ a₁ b₁ c₁)} {.(EQ a₂ b₂ c₂)} (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ u u₁ u₂) isv = tt
updSeq→isValue {r} {s} {n} {.(EQB a₁ b₁ c₁ d₁)} {.(EQB a₂ b₂ c₂ d₂)} (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ u u₁ u₂ u₃) isv = tt
updSeq→isValue {r} {s} {n} {.AX} {.AX} updSeq-AX isv = tt
updSeq→isValue {r} {s} {n} {.FREE} {.FREE} updSeq-FREE isv = tt
updSeq→isValue {r} {s} {n} {.(MSEQ x)} {.(MSEQ x)} (updSeq-MSEQ x) isv = tt
updSeq→isValue {r} {s} {n} {.(TSQUASH a₁)} {.(TSQUASH a₂)} (updSeq-TSQUASH a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(TTRUNC a₁)} {.(TTRUNC a₂)} (updSeq-TTRUNC a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(TCONST a₁)} {.(TCONST a₂)} (updSeq-TCONST a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(SUBSING a₁)} {.(SUBSING a₂)} (updSeq-SUBSING a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(PURE)} {.(PURE)} (updSeq-PURE) isv = tt
updSeq→isValue {r} {s} {n} {.(DUM a₁)} {.(DUM a₂)} (updSeq-DUM a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(FFDEFS a₁ b₁)} {.(FFDEFS a₂ b₂)} (updSeq-FFDEFS a₁ a₂ b₁ b₂ u u₁) isv = tt
updSeq→isValue {r} {s} {n} {.(UNIV x)} {.(UNIV x)} (updSeq-UNIV x) isv = tt
updSeq→isValue {r} {s} {n} {.(LIFT a₁)} {.(LIFT a₂)} (updSeq-LIFT a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(LOWER a₁)} {.(LOWER a₂)} (updSeq-LOWER a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(SHRINK a₁)} {.(SHRINK a₂)} (updSeq-SHRINK a₁ a₂ u) isv = tt
updSeq→isValue {r} {s} {n} {.(upd r (MSEQ s))} {.(upd r (s2l s n))} updSeq-upd isv = tt


≡sub-updSeqStepInd : (r : Name) (s : 𝕊) (n : ℕ) (b : Term) (t u : Term) (w : 𝕎·)
                     → t ≡ u
                     → updSeqStepInd r s n (sub b t) w
                     → updSeqStepInd r s n (sub b u) w
≡sub-updSeqStepInd r s n b t u w e h rewrite e = h


≡sub-FIX-updSeqStepInd : (r : Name) (s : 𝕊) (n : ℕ) (t u : Term) (w : 𝕎·)
                         → t ≡ u
                         → updSeqStepInd r s n (sub (FIX (LAMBDA t)) t) w
                         → updSeqStepInd r s n (sub (FIX (LAMBDA u)) u) w
≡sub-FIX-updSeqStepInd r s n t u w e h rewrite e = h


⇓ₗ→updSeqStep : (w1 w2 : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a a' b : Term)
                 → a ⇓ a' from w1 to w1
                 → updSeqStep w1 w2 r s n a' b
                 → updSeqStep w1 w2 r s n a b
⇓ₗ→updSeqStep w1 w2 r s n a a' b comp (k1 , k2 , y , z , w3 , comp1 , comp2 , u) =
  k1 , fst comp + k2 , y , z , w3 , comp1 ,
  steps-trans+ {fst comp} {k2} {a} {a'} {z} {w1} {w1} {w3} (snd comp) comp2 ,
  u


updSeqStep-upd : (cn : cℕ) (gc : get-choose-ℕ) (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                 → compatible· r w Res⊤
                 → updSeq r s n a b
                 → updSeqStepInd r s n (updBodyL r a (MSEQ s)) w
                 → updSeqStep w w r s n (updBodyL r b (s2l s n)) (updBodyL r a (MSEQ s))
updSeqStep-upd cn gc w r s n a b compat u (k , v , w' , comp , ish , isv , ind)
  with upd-decomp {k} {r} {MSEQ s} {a} {v} {w} {w'} refl (cn r w compat) comp isv
... | (k1 , k2 , w1' , m , m' , ltk1 , ltk2 , gt0 , comp1 , comp2) =
  k2 + 2 , fst comp3c , NUM (s m) , NUM (s m) , w2 , comp2b , snd comp3c , updSeq-NUM (s m)
  where
    comp1b : steps k1 (a , w) ≡ (NUM m , w1')
    comp1b = ssteps→steps {k1} {a} {NUM m} {w} {w1'} comp1

    e' : w ⊑· w1'
    e' = ⇓from-to→⊑ {w} {w1'} {a} {NUM m} (k1 , comp1b)

    w2 : 𝕎·
    w2 = chooseT0if r w1' m' m

    ish1 : isHighestℕ {k1} {w} {w1'} {a} {NUM m} n r comp1b
    ish1 = isHighestℕ-LET→ {n} {k1} {k} {r} {a} {SEQ (updGt r (VAR 0)) (APPLY (MSEQ s) (VAR 0))} {NUM m} {v} {w} {w1'} {w'} comp1b comp isv ish

    h1 : Σ ℕ (λ k' → Σ Term (λ v' → steps k' (b , w) ≡ (v' , w1') × updSeq r s n (NUM m) v'))
    h1 = ind k1 (<⇒≤ ltk1) compat u comp1b ish1 tt

    h2 : Σ ℕ (λ k' → steps k' (b , w) ≡ (NUM m , w1'))
    h2 = Σsteps-updSeq-NUM→ w w1' r s n m b h1

    comp2b : steps (k2 + 2) (updBodyL r a (MSEQ s) , w) ≡ (NUM (s m) , w2)
    comp2b = steps-trans+
               {k2} {2}
               {updBodyL r a (MSEQ s)}
               {APPLY (MSEQ s) (NUM m)} {NUM (s m)} {w} {w2} {w2}
               comp2 refl

    eqv : v ≡ NUM (s m)
    eqv = steps→≡ w w' w2 (updBodyL r a (MSEQ s)) v (NUM (s m)) k (k2 + 2) isv tt comp comp2b

    eqw' : w' ≡ w2
    eqw' = steps→≡𝕎 w w' w2 (updBodyL r a (MSEQ s)) v (NUM (s m)) k (k2 + 2) isv tt comp comp2b

-- From comp and comp2b we can prove that v ≡ NUM (s m) and w' ≡ w2
-- From w' ≡ w2 & ish, we should be able to prove that m < n

    ltn : m < n
    ltn = isHighestℕ→<≡upd gc {k} {w} {w'} {w1'}
            {updBodyL r a (MSEQ s)} {v} {m}
            {m'} n r comp ish gt0 (⊑-compatible· e' compat) eqw'

    comp3 : updBodyL r b (s2l s n) ⇓ APPLY (s2l s n) (NUM m) from w to u𝕎 r m w1'
    comp3 = updBodyL⇓APPLY cn r b (s2l s n) w w1' m (s2l# s n) compat h2

    comp3b : updBodyL r b (s2l s n) ⇓ NUM (s m) from w to u𝕎 r m w1'
    comp3b = ⇓-trans₂ {w} {u𝕎 r m w1'} {u𝕎 r m w1'} {updBodyL r b (s2l s n)}
               {APPLY (s2l s n) (NUM m)} {NUM (s m)} comp3 (s2l⇓ (u𝕎 r m w1') s n m ltn)

    comp3c : updBodyL r b (s2l s n) ⇓ NUM (s m) from w to w2
    comp3c = ≡𝕎→⇓from-to w (u𝕎 r m w1') w2 (updBodyL r b (s2l s n)) (NUM (s m)) (sym (chooseT0if≡u𝕎 w1' r m m' gt0)) comp3b


updSeqStep-sub-sub-upd : (cn : cℕ) (gc : get-choose-ℕ) (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                         → compatible· r w Res⊤
                         → updSeq r s n a b
                         → updSeqStepInd r s n (sub a (updBody r (MSEQ s))) w
                         → updSeqStep w w r s n (sub b (updBody r (s2l s n))) (sub a (updBody r (MSEQ s)))
updSeqStep-sub-sub-upd cn gc w r s n a b compat u ind
  rewrite sub-upd r (MSEQ s) a refl | sub-upd r (s2l s n) b (s2l# s n) =
  updSeqStep-upd cn gc w r s n a b compat u ind


updSeqStep-sub-upd : (cn : cℕ) (gc : get-choose-ℕ) (w : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (a b : Term)
                     → compatible· r w Res⊤
                     → updSeq r s n a b
                     → updSeqStepInd r s n (sub a (updBody r (MSEQ s))) w
                     → updSeqStep w w r s n (APPLY (upd r (s2l s n)) b) (sub a (updBody r (MSEQ s)))
updSeqStep-sub-upd cn gc w r s n a b compat u ind =
  ⇓ₗ→updSeqStep
    w w r s n
    (APPLY (upd r (s2l s n)) b)
    (sub b (updBody r (s2l s n)))
    (sub a (updBody r (MSEQ s)))
    (1 , refl)
    (updSeqStep-sub-sub-upd cn gc w r s n a b compat u ind)


updSeq-step : (cn : cℕ) (gc : get-choose-ℕ) (w1 w2 : 𝕎·) (r : Name) (s : 𝕊) (n : ℕ) (t u x : Term)
              → updSeq r s n t u
              → getT≤ℕ w2 n r
              → compatible· r w1 Res⊤
              → step t w1 ≡ just (x , w2)
              → updSeqStepInd r s n x w2
              → updSeqStep w1 w2 r s n u x
updSeq-step cn gc w1 w2 r s n .NAT .NAT u updSeq-NAT gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NAT , NAT , w1 , refl , refl , updSeq-NAT
updSeq-step cn gc w1 w2 r s n .QNAT .QNAT u updSeq-QNAT gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QNAT , QNAT , w1 , refl , refl , updSeq-QNAT
updSeq-step cn gc w1 w2 r s n .TNAT .TNAT u updSeq-TNAT gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TNAT , TNAT , w1 , refl , refl , updSeq-TNAT
updSeq-step cn gc w1 w2 r s n .(LT a₁ b₁) .(LT a₂ b₂) u (updSeq-LT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LT a₁ b₁ , LT a₂ b₂ , w1 , refl , refl , updSeq-LT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(QLT a₁ b₁) .(QLT a₂ b₂) u (updSeq-QLT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QLT a₁ b₁ , QLT a₂ b₂ , w1 , refl , refl , updSeq-QLT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(NUM x) .(NUM x) u (updSeq-NUM x) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , NUM x , NUM x , w1 , refl , refl , updSeq-NUM x
updSeq-step cn gc w1 w2 r s n .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn compat comp sind with is-NUM a₁
... | inj₁ (k1 , p) rewrite p | updSeq-NUM→ r s n k1 a₂ upd₁ with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q | updSeq-NUM→ r s n k2 b₂ upd₂ with k1 <? k2
... |       yes z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , c₁ , c₂ , w1 , refl , concl , upd₃
  where
    concl : steps 1 (IFLT (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (c₂ , w1)
    concl with k1 <? k2
    ... | yes z' = refl
    ... | no z' = ⊥-elim (z' z)
... |       no z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , d₁ , d₂ , w1 , refl , concl , upd₄
  where
    concl : steps 1 (IFLT (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (d₂ , w1)
    concl with k1 <? k2
    ... | yes z' = ⊥-elim (z z')
    ... | no z' = refl
updSeq-step cn gc w1 w2 r s n .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn compat comp sind | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-IFLT₂ w1 w1' r s n k1 b₁' b₂ c₁ c₂ d₁ d₂ upd₃ upd₄ ind
  where
    ind : updSeqStep w1 w1' r s n b₂ b₁'
    ind = updSeq-step cn gc w1 w1' r s n b₁ b₂ b₁' upd₂ gtn compat z (updSeqStepInd-IFLT₂→ w1' r s n k1 b₁' c₁ d₁ sind)
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) u (updSeq-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn compat comp sind | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-IFLT₁ w1 w1' r s n a₁' a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₂ upd₃ upd₄ ind
  where
    ind : updSeqStep w1 w1' r s n a₂ a₁'
    ind = updSeq-step cn gc w1 w1' r s n a₁ a₂ a₁' upd₁ gtn compat z (updSeqStepInd-IFLT₁→ w1' r s n a₁' b₁ c₁ d₁ sind)
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn compat comp sind with is-NUM a₁
... | inj₁ (k1 , p) rewrite p | updSeq-NUM→ r s n k1 a₂ upd₁ with is-NUM b₁
... |    inj₁ (k2 , q) rewrite q | updSeq-NUM→ r s n k2 b₂ upd₂ with k1 ≟ k2
... |       yes z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , c₁ , c₂ , w1 , refl , concl , upd₃
  where
    concl : steps 1 (IFEQ (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (c₂ , w1)
    concl with k1 ≟ k2
    ... | yes z' = refl
    ... | no z' = ⊥-elim (z' z)
... |       no z rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , d₁ , d₂ , w1 , refl , concl , upd₄
  where
    concl : steps 1 (IFEQ (NUM k1) (NUM k2) c₂ d₂ , w1) ≡ (d₂ , w1)
    concl with k1 ≟ k2
    ... | yes z' = ⊥-elim (z z')
    ... | no z' = refl
updSeq-step cn gc w1 w2 r s n .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn compat comp sind | inj₁ (k1 , p) | inj₂ q with step⊎ b₁ w1
... |       inj₁ (b₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-IFEQ₂ w1 w1' r s n k1 b₁' b₂ c₁ c₂ d₁ d₂ upd₃ upd₄ ind
  where
    ind : updSeqStep w1 w1' r s n b₂ b₁'
    ind = updSeq-step cn gc w1 w1' r s n b₁ b₂ b₁' upd₂ gtn compat z (updSeqStepInd-IFEQ₂→ w1' r s n k1 b₁' c₁ d₁ sind)
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(IFEQ a₁ b₁ c₁ d₁) .(IFEQ a₂ b₂ c₂ d₂) u (updSeq-IFEQ a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn compat comp sind | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-IFEQ₁ w1 w1' r s n a₁' a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₂ upd₃ upd₄ ind
  where
    ind : updSeqStep w1 w1' r s n a₂ a₁'
    ind = updSeq-step cn gc w1 w1' r s n a₁ a₂ a₁' upd₁ gtn compat z (updSeqStepInd-IFEQ₁→ w1' r s n a₁' b₁ c₁ d₁ sind)
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(SUC a₁) .(SUC a₂) u (updSeq-SUC a₁ a₂ upd₁) gtn compat comp sind with is-NUM a₁
... | inj₁ (k , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updSeq-NUM→ r s n k a₂ upd₁ =
  0 , 1 , NUM (suc k) , NUM (suc k) , w1 , refl , refl , updSeq-NUM (suc k)
... | inj₂ p with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , z) rewrite z | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-SUC₁ w1 w1' r s n a₁' a₂ ind
  where
    ind : updSeqStep w1 w1' r s n a₂ a₁'
    ind = updSeq-step cn gc w1 w1' r s n a₁ a₂ a₁' upd₁ gtn compat z (updSeqStepInd-SUC₁→ w1' r s n a₁' sind)
... |    inj₂ q rewrite q = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(PI a₁ b₁) .(PI a₂ b₂) u (updSeq-PI a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PI a₁ b₁ , PI a₂ b₂ , w1 , refl , refl , updSeq-PI a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(LAMBDA a₁) .(LAMBDA a₂) u (updSeq-LAMBDA a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LAMBDA a₁ , LAMBDA a₂ , w1 , refl , refl , updSeq-LAMBDA a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(APPLY a₁ b₁) .(APPLY a₂ b₂) u (updSeq-APPLY a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind with is-LAM a₁
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl d
  where
    d : Σ Term (λ t' → a₂ ≡ LAMBDA t' × updSeq r s n t t') ⊎ (t ≡ updBody r (MSEQ s) × a₂ ≡ upd r (s2l s n))
    d = updSeq-LAMBDA→ {r} {s} {n} {t} {a₂} upd₁

    concl : Σ Term (λ t' → a₂ ≡ LAMBDA t' × updSeq r s n t t') ⊎ (t ≡ updBody r (MSEQ s) × a₂ ≡ upd r (s2l s n))
            → updSeqStep w1 w1 r s n (APPLY a₂ b₂) (sub b₁ t)
    concl (inj₁ (t' , e , u')) rewrite e = 0 , 1 , sub b₁ t , sub b₂ t' , w1 , refl , refl , updSeq-sub u' upd₂
    concl (inj₂ (e , f)) rewrite e | f = c0
      where
        c0 : updSeqStep w1 w1 r s n (APPLY (upd r (s2l s n)) b₂) (sub b₁ (updBody r (MSEQ s)))
        c0 = updSeqStep-sub-upd cn gc w1 r s n b₁ b₂ compat upd₂ (≡sub-updSeqStepInd r s n b₁ t (updBody r (MSEQ s)) w1 e sind)
... | inj₂ x with is-CS a₁
... |    inj₁ (nm , p) rewrite p = ⊥-elim (updSeq-CS→ r s n nm a₂ upd₁)
updSeq-step cn gc w1 w2 r s n .(APPLY a₁ b₁) .(APPLY a₂ b₂) u (updSeq-APPLY a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind | inj₂ x {-- ¬LAM --} | inj₂ name {-- ¬SEQ --} with is-MSEQ a₁
... | inj₁ (sq , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) | updSeq-MSEQ→ r s n sq a₂ upd₁ =
  0 , 1 , MAPP sq b₁ , MAPP sq b₂ , w1 , refl , refl , updSeq-MAPP sq b₁ b₂ upd₂
... | inj₂ z with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-APPLY₁ w1 w1' r s n a₁' a₂ b₁ b₂ upd₂ ind
  where
    ind : updSeqStep w1 w1' r s n a₂ a₁'
    ind = updSeq-step cn gc w1 w1' r s n a₁ a₂ a₁' upd₁ gtn compat q (updSeqStepInd-APPLY₁→ w1' r s n a₁' b₁ sind)
... |    inj₂ q rewrite q = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(FIX a₁) .(FIX a₂) u (updSeq-FIX a₁ a₂ upd₁) gtn compat comp sind with is-LAM a₁
... | inj₁ (t , p) rewrite p | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = concl d
  where
    d : Σ Term (λ t' → a₂ ≡ LAMBDA t' × updSeq r s n t t') ⊎ (t ≡ updBody r (MSEQ s) × a₂ ≡ upd r (s2l s n))
    d = updSeq-LAMBDA→ {r} {s} {n} {t} {a₂} upd₁

    concl : Σ Term (λ t' → a₂ ≡ LAMBDA t' × updSeq r s n t t') ⊎ (t ≡ updBody r (MSEQ s) × a₂ ≡ upd r (s2l s n))
            → updSeqStep w1 w1 r s n (FIX a₂) (sub (FIX (LAMBDA t)) t)
    concl (inj₁ (t' , e , u')) rewrite e = 0 , 1 , sub (FIX (LAMBDA t)) t , sub (FIX (LAMBDA t')) t' , w1 , refl , refl , updSeq-sub u' (updSeq-FIX (LAMBDA t) (LAMBDA t') (updSeq-LAMBDA t t' u'))
    concl (inj₂ (e , f)) rewrite e | f = c0
      where
        c0 : updSeqStep w1 w1 r s n (FIX (upd r (s2l s n))) (sub (FIX (LAMBDA (updBody r (MSEQ s)))) (updBody r (MSEQ s)))
        c0 = ⇓ₗ→updSeqStep
               w1 w1 r s n
               (FIX (upd r (s2l s n)))
               (sub (FIX (upd r (s2l s n))) (updBody r (s2l s n)))
               (sub (FIX (upd r (MSEQ s))) (updBody r (MSEQ s)))
               (1 , refl)
               (updSeqStep-sub-sub-upd
                 cn gc w1 r s n (FIX (upd r (MSEQ s))) (FIX (upd r (s2l s n))) compat
                 (updSeq-FIX (upd r (MSEQ s)) (upd r (s2l s n)) updSeq-upd)
                 (≡sub-FIX-updSeqStepInd r s n t (updBody r (MSEQ s)) w1 e sind))
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-FIX₁ w1 w1' r s n a₁' a₂ ind
  where
    ind : updSeqStep w1 w1' r s n a₂ a₁'
    ind = updSeq-step cn gc w1 w1' r s n a₁ a₂ a₁' upd₁ gtn compat q (updSeqStepInd-FIX₁→ w1' r s n a₁' sind)
... |    inj₂ q rewrite q = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(LET a₁ b₁) .(LET a₂ b₂) u (updSeq-LET a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind with isValue⊎ a₁
... | inj₁ x rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  0 , 1 , sub a₁ b₁ , sub a₂ b₂ , w1 , refl , snd (LET-val⇓ w1 a₂ b₂ (updSeq→isValue upd₁ x)) , updSeq-sub upd₂ upd₁
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1' , q) rewrite q | pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) =
  →updSeqStep-LET₁ w1 w1' r s n a₁' a₂ b₁ b₂ upd₂ ind
  where
    ind : updSeqStep w1 w1' r s n a₂ a₁'
    ind = updSeq-step cn gc w1 w1' r s n a₁ a₂ a₁' upd₁ gtn compat q (updSeqStepInd-LET₁→ w1' r s n a₁' b₁ sind)
... |    inj₂ q rewrite q = ⊥-elim (¬just≡nothing (sym comp))
updSeq-step cn gc w1 w2 r s n .(WT a₁ b₁) .(WT a₂ b₂) u (updSeq-WT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , WT a₁ b₁ , WT a₂ b₂ , w1 , refl , refl , updSeq-WT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(SUP a₁ b₁) .(SUP a₂ b₂) u (updSeq-SUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUP a₁ b₁ , SUP a₂ b₂ , w1 , refl , refl , updSeq-SUP a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(DSUP a₁ b₁) .(DSUP a₂ b₂) u (updSeq-DSUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind = {!!}
updSeq-step cn gc w1 w2 r s n .(MT a₁ b₁) .(MT a₂ b₂) u (updSeq-MT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MT a₁ b₁ , MT a₂ b₂ , w1 , refl , refl , updSeq-MT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(MSUP a₁ b₁) .(MSUP a₂ b₂) u (updSeq-MSUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MSUP a₁ b₁ , MSUP a₂ b₂ , w1 , refl , refl , updSeq-MSUP a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(DMSUP a₁ b₁) .(DMSUP a₂ b₂) u (updSeq-DMSUP a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind = {!!}
updSeq-step cn gc w1 w2 r s n .(SUM a₁ b₁) .(SUM a₂ b₂) u (updSeq-SUM a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUM a₁ b₁ , SUM a₂ b₂ , w1 , refl , refl , updSeq-SUM a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(PAIR a₁ b₁) .(PAIR a₂ b₂) u (updSeq-PAIR a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , refl , refl , updSeq-PAIR a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) u (updSeq-SPREAD a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind = {!!}
updSeq-step cn gc w1 w2 r s n .(SET a₁ b₁) .(SET a₂ b₂) u (updSeq-SET a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SET a₁ b₁ , SET a₂ b₂ , w1 , refl , refl , updSeq-SET a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(ISECT a₁ b₁) .(ISECT a₂ b₂) u (updSeq-ISECT a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , refl , refl , updSeq-ISECT a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(TUNION a₁ b₁) .(TUNION a₂ b₂) u (updSeq-TUNION a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , refl , refl , updSeq-TUNION a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(UNION a₁ b₁) .(UNION a₂ b₂) u (updSeq-UNION a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNION a₁ b₁ , UNION a₂ b₂ , w1 , refl , refl , updSeq-UNION a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(QTUNION a₁ b₁) .(QTUNION a₂ b₂) u (updSeq-QTUNION a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , refl , refl , updSeq-QTUNION a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(INL a₁) .(INL a₂) u (updSeq-INL a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INL a₁ , INL a₂ , w1 , refl , refl , updSeq-INL a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(INR a₁) .(INR a₂) u (updSeq-INR a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , INR a₁ , INR a₂ , w1 , refl , refl , updSeq-INR a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) u (updSeq-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃) gtn compat comp sind = {!!}
updSeq-step cn gc w1 w2 r s n .(EQ a₁ b₁ c₁) .(EQ a₂ b₂ c₂) u (updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQ a₁ b₁ c₁ , EQ a₂ b₂ c₂ , w1 , refl , refl , updSeq-EQ a₁ a₂ b₁ b₂ c₁ c₂ upd₁ upd₂ upd₃
updSeq-step cn gc w1 w2 r s n .(EQB a₁ b₁ c₁ d₁) .(EQB a₂ b₂ c₂ d₂) u (updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , EQB a₁ b₁ c₁ d₁ , EQB a₂ b₂ c₂ d₂ , w1 , refl , refl , updSeq-EQB a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ upd₁ upd₂ upd₃ upd₄
updSeq-step cn gc w1 w2 r s n .AX .AX u updSeq-AX gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , AX , AX , w1 , refl , refl , updSeq-AX
updSeq-step cn gc w1 w2 r s n .FREE .FREE u updSeq-FREE gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FREE , FREE , w1 , refl , refl , updSeq-FREE
updSeq-step cn gc w1 w2 r s n .(MSEQ x) .(MSEQ x) u (updSeq-MSEQ x) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , MSEQ x , MSEQ x , w1 , refl , refl , updSeq-MSEQ x
updSeq-step cn gc w1 w2 r s n .(MAPP x a₁) .(MAPP x a₂) u (updSeq-MAPP x a₁ a₂ upd₁) gtn compat comp sind = {!!}
updSeq-step cn gc w1 w2 r s n .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) u (updSeq-CHOOSE a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind = {!!}
updSeq-step cn gc w1 w2 r s n .(TSQUASH a₁) .(TSQUASH a₂) u (updSeq-TSQUASH a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TSQUASH a₁ , TSQUASH a₂ , w1 , refl , refl , updSeq-TSQUASH a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(TTRUNC a₁) .(TTRUNC a₂) u (updSeq-TTRUNC a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TTRUNC a₁ , TTRUNC a₂ , w1 , refl , refl , updSeq-TTRUNC a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(TCONST a₁) .(TCONST a₂) u (updSeq-TCONST a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , TCONST a₁ , TCONST a₂ , w1 , refl , refl , updSeq-TCONST a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(SUBSING a₁) .(SUBSING a₂) u (updSeq-SUBSING a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SUBSING a₁ , SUBSING a₂ , w1 , refl , refl , updSeq-SUBSING a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .PURE .PURE u updSeq-PURE gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , PURE , PURE , w1 , refl , refl , updSeq-PURE
updSeq-step cn gc w1 w2 r s n .(DUM a₁) .(DUM a₂) u (updSeq-DUM a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , DUM a₁ , DUM a₂ , w1 , refl , refl , updSeq-DUM a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) u (updSeq-FFDEFS a₁ a₂ b₁ b₂ upd₁ upd₂) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , refl , refl , updSeq-FFDEFS a₁ a₂ b₁ b₂ upd₁ upd₂
updSeq-step cn gc w1 w2 r s n .(UNIV x) .(UNIV x) u (updSeq-UNIV x) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , UNIV x , UNIV x , w1 , refl , refl , updSeq-UNIV x
updSeq-step cn gc w1 w2 r s n .(LIFT a₁) .(LIFT a₂) u (updSeq-LIFT a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LIFT a₁ , LIFT a₂ , w1 , refl , refl , updSeq-LIFT a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(LOWER a₁) .(LOWER a₂) u (updSeq-LOWER a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , LOWER a₁ , LOWER a₂ , w1 , refl , refl , updSeq-LOWER a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(SHRINK a₁) .(SHRINK a₂) u (updSeq-SHRINK a₁ a₂ upd₁) gtn compat comp sind rewrite pair-inj₁ (just-inj (sym comp)) | pair-inj₂ (just-inj (sym comp)) = 0 , 0 , SHRINK a₁ , SHRINK a₂ , w1 , refl , refl , updSeq-SHRINK a₁ a₂ upd₁
updSeq-step cn gc w1 w2 r s n .(upd r (MSEQ s)) .(upd r (s2l s n)) u updSeq-upd gtn compat comp sind = {!!}



\end{code}


-- We want to create a Term ∈ BAIRE from this path.
noInfPath : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
            (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
            → #¬Names F -- This is currently required by continuity
            → compatible· r w Res⊤
            → ∈Type i w #FunBar F
            → (p : path i w #IndBarB #IndBarC)
            → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
            → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
            → ⊥
noInfPath kb cn can exb gc i w r F nnF compat F∈ p cor inf =
  {!!}
  where
    s : 𝕊
    s = path2𝕊 kb p

    f : CTerm
    f = #MSEQ s

    nnf : #¬Names f
    nnf = refl

    cs : correctSeq r w F s
    cs = corSeq→correctSeq r w F s (→corSeq kb cn i w r F compat F∈ p cor inf)

    f∈ : ∈Type i w #BAIRE f
    f∈ = mseq∈baire i w s

    a∈1 : ∈Type i w #NAT (#APPLY F (#upd r f))
    a∈1 = equalInType-FUN→ F∈ w (⊑-refl· _) (#upd r f) (#upd r f) (upd∈BAIRE cn i w r f compat f∈)

    a∈2 : NATmem w (#APPLY F (#upd r f))
    a∈2 = kb (equalInType-NAT→ i w (#APPLY F (#upd r f)) (#APPLY F (#upd r f)) a∈1) w (⊑-refl· w)

    k : ℕ
    k = fst a∈2

    ca1 : Σ 𝕎· (λ w' → #APPLY F (#upd r f) #⇓ #NUM k from w to w')
    ca1 = #⇓→from-to {w} {#APPLY F (#upd r f)} {#NUM k} (lower (fst (snd a∈2) w (⊑-refl· w)))

    w' : 𝕎·
    w' = fst ca1

    ca2 : #APPLY F (#upd r f) #⇓ #NUM k from w to w'
    ca2 = snd ca1

    e' : w ⊑· w'
    e' = #⇓from-to→⊑ {w} {w'} {#APPLY F (#upd r f)} {#NUM k} ca2

    d1 : Σ ℕ (λ n → getT 0 r w' ≡ just (NUM n))
    d1 = lower (cn r w compat w' e')

    n : ℕ
    n = fst d1

    gt : getT 0 r w' ≡ just (NUM n)
    gt = snd d1

    wgt0 : ∀𝕎-get0-NUM w r
    wgt0 = cn r w compat

    gtn : getT≤ℕ w' (suc n) r
    gtn = n , gt , ≤-refl

    uc : updCtxt r ⌜ f ⌝ ⌜ #APPLY F (#upd r f) ⌝
    uc = updCtxt-APPLY ⌜ F ⌝ ⌜ #upd r f ⌝ (¬Names→updCtxt {r} {⌜ f ⌝} {⌜ F ⌝} nnF) updCtxt-upd

    -- all values of r along (snd ca2) are strictly less than (suc n) - the modulus of continuity
    ish : isHighestℕ {fst ca2} {w} {w'} {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} (suc n) r (snd ca2)
    ish = steps-sat-isHighestℕ
            gc {r} {⌜ f ⌝} {fst ca2} nnf (CTerm.closed f) {w} {w'}
            {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} {suc n} (snd ca2)
            tt uc compat wgt0 gtn

    csn : correctSeqN r w F 0 #INIT s (suc (suc n))
    csn = cs (suc (suc n))

    inv : Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
            #APPLY F (#upd r (seq2list s (suc n))) #⇓ #NUM m from (chooseT r w N0) to w'
            × getT 0 r w' ≡ just (NUM j)
            × ¬ j < (suc n))))
    inv = correctSeqN-inv0 i r w F s (suc n) csn



sem : (kb : K□) (cn : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
        → compatible· r w Res⊤
        → ∈Type i w #FunBar F
        → ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
sem kb cn i w r F compat F∈ = concl
  where
    co : ∈Type i w #CoIndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
    co = coSem kb cn i w r F (#NUM 0) #INIT compat F∈ (NUM-equalInType-NAT! i w 0) (LAM0∈BAIRE i w)

    concl : ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
    concl with EM {∃𝕎 w (λ w' _ → Σ (path i w' #IndBarB #IndBarC)
                                   (λ p → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
                                         × isInfPath {i} {w'} {#IndBarB} {#IndBarC} p))}
    ... | yes pp = c
      where
        c : ∈Type i w #IndBar (#APPLY2 (#loop r F) (#NUM 0) #INIT)
        c = {!!}
    ... | no pp = CoIndBar2IndBar i w (#APPLY2 (#loop r F) (#NUM 0) #INIT) cond co
      where
        cond : ∀𝕎 w (λ w' _ → (p : path i w' #IndBarB #IndBarC)
               → correctPath {i} {w'} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
               → isFinPath {i} {w'} {#IndBarB} {#IndBarC} p)
        cond w1 e1 p cor with EM {Lift {0ℓ} (lsuc(L)) (isFinPath {i} {w1} {#IndBarB} {#IndBarC} p)}
        ... | yes qq = lower qq
        ... | no qq = ⊥-elim (pp (w1 , e1 , p , cor , ¬isFinPath→isInfPath {i} {w1} {#IndBarB} {#IndBarC} p (λ z → qq (lift z))))

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
