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


module continuity2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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



testM⇓→step : {F f v : Term} {w1 w2 : 𝕎·} {name : Name}
               → isValue v
               → testM name F f ⇓ v from w1 to w2
               → probeM name F f ⇓ v from (chooseT name w1 (NUM 0)) to w2
testM⇓→step {F} {f} {v} {w1} {w2} {name} isv (0 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
testM⇓→step {F} {f} {v} {w1} {w2} {name} isv (1 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
testM⇓→step {F} {f} {v} {w1} {w2} {name} isv (suc (suc k) , comp) =
  k , z
  where
    z : steps k (probeM name F f , chooseT name w1 (NUM 0)) ≡ (v , w2)
    z = begin
          steps k (probeM name F f , chooseT name w1 (NUM 0))
        ≡⟨ cong (λ x → steps k (x , chooseT name w1 (NUM 0))) (sym (sub-shiftUp0≡ AX (probeM name F f)))  ⟩
          steps k (sub AX (shiftUp 0 (probeM name F f)) , chooseT name w1 (NUM 0))
        ≡⟨ comp ⟩
          (v , w2)
        ∎


{--
testM⇓→ : {w1 w2 : 𝕎·} {F f : Term} {n : ℕ} {name : Name}
            → testM name F f ⇓ NUM n from w1 to w2
            → Σ ℕ (λ k →
                APPLY F (upd name f) ⇓ NUM k from (chooseT name w1 (NUM 0)) to w2
                × getT 0 name w2 ≡ just (NUM n))
testM⇓→ {w1} {w2} {F} {f} {n} {name} comp = {!!}
--}


SEQ→hasValue-decomp : (k : ℕ) (a b v : Term) (w w' : 𝕎·)
                       → steps k (SEQ a b , w) ≡ (v , w')
                       → isValue v
                       → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
                           Σ (steps k1 (a , w) ≡ (u , w1)) (λ comp1 →
                           isValue u
                           × steps k2 (b , w1) ≡ (v , w')
                           × Σ (steps (suc k1) (SEQ a b , w) ≡ (b , w1)) (λ comp2 →
                           steps→𝕎s {k1} {w} {w1} {a} {u} comp1 ++ Data.List.[ w1 ] ≡ steps→𝕎s {suc k1} {w} {w1} {SEQ a b} {b} comp2
                           × k1 + k2 < k))))))
SEQ→hasValue-decomp k a b v w w' comp isv =
  fst z , fst (snd z) , fst (snd (snd z)) , fst (snd (snd (snd z))) ,
  fst (snd (snd (snd (snd z)))) ,
  fst (snd (snd (snd (snd (snd z))))) ,
  cb ,
  cc ,
  eqws ,
  snd (snd (snd (snd (snd (snd (snd (snd (snd z))))))))
  where
    z : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
          Σ (steps k1 (a , w) ≡ (u , w1)) (λ comp1 →
          isValue u
          × steps k2 (sub u (shiftUp 0 b) , w1) ≡ (v , w')
          × Σ (steps (suc k1) (SEQ a b , w) ≡ (sub u (shiftUp 0 b) , w1)) (λ comp2 →
          steps→𝕎s {k1} {w} {w1} {a} {u} comp1 ++ Data.List.[ w1 ] ≡ steps→𝕎s {suc k1} {w} {w1} {SEQ a b} {sub u (shiftUp 0 b)} comp2
          × k1 + k2 < k))))))
    z = LET→hasValue-decomp k a (shiftUp 0 b) v w w' comp isv

    cb : steps (fst (snd z)) (b , fst (snd (snd z))) ≡ (v , w')
    cb = begin
           steps (fst (snd z)) (b , fst (snd (snd z)))
         ≡⟨ cong (λ x → steps (fst (snd z)) (x , fst (snd (snd z)))) (sym (sub-shiftUp0≡ (fst (snd (snd (snd z)))) b)) ⟩
           steps (fst (snd z)) (sub (fst (snd (snd (snd z)))) (shiftUp 0 b) , fst (snd (snd z)))
         ≡⟨ fst (snd (snd (snd (snd (snd (snd z)))))) ⟩
           (v , w')
         ∎

    cc : steps (suc (fst z)) (SEQ a b , w) ≡ (b , fst (snd (snd z)))
    cc = begin
           steps (suc (fst z)) (SEQ a b , w)
         ≡⟨ fst (snd (snd (snd (snd (snd (snd (snd z))))))) ⟩
           (sub (fst (snd (snd (snd z)))) (shiftUp 0 b) , fst (snd (snd z)))
         ≡⟨ cong (λ x → x , fst (snd (snd z))) (sub-shiftUp0≡ (fst (snd (snd (snd z)))) b) ⟩
           (b , fst (snd (snd z)))
         ∎

    eqws : steps→𝕎s {fst z} {w} {fst (snd (snd z))} {a} {fst (snd (snd (snd z)))} (fst (snd (snd (snd (snd z))))) ++ Data.List.[ fst (snd (snd z)) ]
           ≡ steps→𝕎s {suc (fst z)} {w} {fst (snd (snd z))} {SEQ a b} {b} cc
    eqws = fst (snd (snd (snd (snd (snd (snd (snd (snd z))))))))



SEQ⇓-decomp : (a b v : Term) (w w' : 𝕎·)
              → SEQ a b ⇓ v from w to w'
              → isValue v
              → Σ 𝕎· (λ w1 → Σ Term (λ u →
                    a ⇓ u from w to w1
                    × isValue u
                    × b ⇓ v from w1 to w'))
SEQ⇓-decomp a b v w w' (k , comp) isv =
  fst (snd (snd z)) ,
  fst (snd (snd (snd z))) ,
  (fst z , fst (snd (snd (snd (snd z))))) ,
  fst (snd (snd (snd (snd (snd z))))) ,
  (fst (snd z) , fst (snd (snd (snd (snd (snd (snd z)))))))
  where
    z : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1 → Σ Term (λ u →
          Σ (steps k1 (a , w) ≡ (u , w1)) (λ comp1 →
          isValue u
          × steps k2 (b , w1) ≡ (v , w')
          × Σ (steps (suc k1) (SEQ a b , w) ≡ (b , w1)) (λ comp2 →
          steps→𝕎s {k1} {w} {w1} {a} {u} comp1 ++ Data.List.[ w1 ] ≡ steps→𝕎s {suc k1} {w} {w1} {SEQ a b} {b} comp2
          × k1 + k2 < k))))))
    z = SEQ→hasValue-decomp k a b v w w' comp isv



probeM⇓-decomp : (name : Name) (F f v : Term) (w w' : 𝕎·)
                 → probeM name F f ⇓ v from w to w'
                 → isValue v
                 → ∀𝕎-getT-NUM w name
                 → Σ Term (λ u →
                     appUpd name F f ⇓ u from w to w'
                     × isValue u
                     × get0 name ⇓ v from w' to w'
                     × getT 0 name w' ≡ just v)
probeM⇓-decomp name F f v w w' comp isv g0 =
  u , comp1' , isv1 , comp2' , g3
  where
    z : Σ 𝕎· (λ w1 → Σ Term (λ u →
          appUpd name F f ⇓ u from w to w1
          × isValue u
          × get0 name ⇓ v from w1 to w'))
    z = SEQ⇓-decomp (appUpd name F f) (get0 name) v w w' comp isv

    w1 : 𝕎·
    w1 = fst z

    u : Term
    u = fst (snd z)

    comp1 : appUpd name F f ⇓ u from w to w1
    comp1 = fst (snd (snd z))

    e1 : w ⊑· w1
    e1 = steps→⊑ (fst comp1) (appUpd name F f) u (snd comp1)

    isv1 : isValue u
    isv1 = fst (snd (snd (snd z)))

    comp2 : get0 name ⇓ v from w1 to w'
    comp2 = snd (snd (snd (snd z)))

    g2 : Σ ℕ (λ k → getT 0 name w1 ≡ just (NUM k))
    g2 = lower (g0 w1 e1)

    k : ℕ
    k = fst g2

    g1 : steps 1 (get0 name , w1) ≡ (NUM k , w1)
    g1 rewrite snd g2 = refl

    comp3 : get0 name ⇓ NUM k from w1 to w1
    comp3 = 1 , g1

    eqw : w1 ≡ w'
    eqw = snd (⇓-from-to→≡𝕎 tt isv comp3 comp2)

    eqv : v ≡ NUM k
    eqv = fst (⇓-from-to→≡𝕎 isv tt comp2 comp3)

    comp1' : appUpd name F f ⇓ u from w to w'
    comp1' = ⇓-from-to≡wᵣ eqw comp1

    comp2' : get0 name ⇓ v from w' to w'
    comp2' = ⇓-from-to≡wₗ eqw comp2

    g3 : getT 0 name w' ≡ just v
    g3 = begin
           getT 0 name w'
         ≡⟨ cong (getT 0 name) (sym eqw) ⟩
           getT 0 name w1
         ≡⟨ snd g2 ⟩
           just (NUM k)
         ≡⟨ cong just (sym eqv) ⟩
           just v
         ∎



shiftNameDown-renn : {name : Name} {F f : Term}
                     → # F
                     → # f
                     → ¬Names F
                     → ¬Names f
                     → shiftNameDown 0 (renn 0 (suc name) (testM 0 F f)) ≡ testM name F f
shiftNameDown-renn {name} {F} {f} cF cf nnF nnf =
  begin
    shiftNameDown 0 (renn 0 (suc name) (testM 0 F f))
  ≡⟨ cong (λ x → shiftNameDown 0 (renn 0 (suc name) (testM 0 x f))) (sym (¬Names→shiftNameUp≡ F 0 nnF)) ⟩
    shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) f))
  ≡⟨ cong (λ x → shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) x))) (sym (¬Names→shiftNameUp≡ f 0 nnf)) ⟩
    shiftNameDown 0 (renn 0 (suc name) (testM 0 (shiftNameUp 0 F) (shiftNameUp 0 f)))
  ≡⟨ shiftNameDown-renn-shiftNameUp name F f cF cf ⟩
    testM name F f
  ∎


νtestM⇓→step : {F f v : Term} {w1 w2 : 𝕎·}
                → # F
                → # f
                → ¬Names F
                → ¬Names f
                → isValue v
                → νtestM F f ⇓ v from w1 to w2
                → testM (newChoiceT w1 (testM 0 F f)) F f ⇓ v from startNewChoiceT Res⊤ w1 (testM 0 F f) to w2
νtestM⇓→step {F} {f} {v} {w1} {w2} cF cf nnF nnf isv (0 , comp) rewrite pair-inj₁ (sym comp) = ⊥-elim isv
νtestM⇓→step {F} {f} {v} {w1} {w2} cF cf nnF nnf isv (suc k , comp) = k , z
  where
    z : steps k (testM (newChoiceT w1 (testM 0 F f)) F f , startNewChoiceT Res⊤ w1 (testM 0 F f)) ≡ (v , w2)
    z = begin
          steps k (testM (newChoiceT w1 (testM 0 F f)) F f , startNewChoiceT Res⊤ w1 (testM 0 F f))
        ≡⟨ cong (λ x → steps k (x , startNewChoiceT Res⊤ w1 (testM 0 F f))) (sym (shiftNameDown-renn cF cf nnF nnf))  ⟩
          steps k (shiftNameDown 0 (renn 0 (newChoiceT+ w1 (testM 0 F f)) (testM 0 F f)) , startNewChoiceT Res⊤ w1 (testM 0 F f))
        ≡⟨ comp ⟩
          (v , w2)
        ∎



#νtestM⇓→ : (nc : ℕℂ) (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ}
             → # F
             → # f
             → ¬Names F
             → ¬Names f
             → νtestM F f ⇓ NUM n from w1 to w2
             → Σ Name (λ name → Σ Term (λ v →
                 APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoiceT Res⊤ w1 (testM 0 F f)) (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM n)))
#νtestM⇓→ nc cn {w1} {w2} {F} {f} {n} cF cf nnF nnf comp =
  newChoiceT w1 (testM 0 F f) ,
  fst comp3 ,
  fst (snd comp3) ,
  fst (snd (snd comp3)) ,
  snd (snd (snd (snd comp3)))
  where
    name : Name
    name = newChoiceT w1 (testM 0 F f)

    w1' : 𝕎·
    w1' = startNewChoiceT Res⊤ w1 (testM 0 F f)

    comp1 : testM name F f ⇓ NUM n from w1' to w2
    comp1 = νtestM⇓→step cF cf nnF nnf tt comp

    w1'' : 𝕎·
    w1'' = chooseT name w1' (NUM 0)

    comp2 : probeM name F f ⇓ NUM n from w1'' to w2
    comp2 = testM⇓→step tt comp1

    compat1 : compatible· name w1' Res⊤
    compat1 = startChoiceCompatible· Res⊤ w1 name (¬newChoiceT∈dom𝕎 w1 (testM 0 F f))

    comp3 : Σ Term (λ u →
               appUpd name F f ⇓ u from w1'' to w2
               × isValue u
               × get0 name ⇓ NUM n from w2 to w2
               × getT 0 name w2 ≡ just (NUM n))
    comp3 = probeM⇓-decomp name F f (NUM n) w1'' w2 comp2 tt (cn nc name w1' 0 compat1)





data updCtxt (name : Name) (f : Term) : Term → Set where
  updCtxt-VAR     : (x : Var) → updCtxt name f (VAR x)
  updCtxt-NAT     : updCtxt name f NAT
  updCtxt-QNAT    : updCtxt name f QNAT
  updCtxt-LT      : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (LT a b)
  updCtxt-QLT     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (QLT a b)
  updCtxt-NUM     : (x : ℕ) → updCtxt name f (NUM x)
  updCtxt-IFLT    : (a b c d : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f d → updCtxt name f (IFLT a b c d)
  updCtxt-PI      : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (PI a b)
  updCtxt-LAMBDA  : (a : Term) → updCtxt name f a → updCtxt name f (LAMBDA a)
  updCtxt-APPLY   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (APPLY a b)
  updCtxt-FIX     : (a : Term) → updCtxt name f a → updCtxt name f (FIX a)
  updCtxt-LET     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (LET a b)
  updCtxt-SUM     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SUM a b)
  updCtxt-PAIR    : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (PAIR a b)
  updCtxt-SPREAD  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SPREAD a b)
  updCtxt-SET     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SET a b)
  updCtxt-TUNION  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (TUNION a b)
  updCtxt-UNION   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (UNION a b)
  updCtxt-QTUNION : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (QTUNION a b)
  updCtxt-INL     : (a : Term) → updCtxt name f a → updCtxt name f (INL a)
  updCtxt-INR     : (a : Term) → updCtxt name f a → updCtxt name f (INR a)
  updCtxt-DECIDE  : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (DECIDE a b c)
  updCtxt-EQ      : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (EQ a b c)
  updCtxt-AX      : updCtxt name f AX
  updCtxt-FREE    : updCtxt name f FREE
  --updCtxt-CS      : updCtxt name1 name2 f (CS name1) (CS name2)
  --updCtxt-CS      : updCtxt name1 name2 f (CS name1) (CS name2)
  --updCtxt-NAME    : updCtxt name1 name2 f (NAME name1) (NAME name2)
  --updCtxt-FRESH   : (a b : Term) → updCtxt name1 name2 f a b → updCtxt name1 name2 f (FRESH a) (FRESH b)
  updCtxt-CHOOSE  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (CHOOSE a b)
--  updCtxt-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updCtxt name1 name2 f a₁ a₂ → updCtxt name1 name2 f b₁ b₂ → updCtxt name1 name2 f c₁ c₂ → updCtxt name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
  updCtxt-TSQUASH : (a : Term) → updCtxt name f a → updCtxt name f (TSQUASH a)
  updCtxt-TTRUNC  : (a : Term) → updCtxt name f a → updCtxt name f (TTRUNC a)
  updCtxt-TCONST  : (a : Term) → updCtxt name f a → updCtxt name f (TCONST a)
  updCtxt-SUBSING : (a : Term) → updCtxt name f a → updCtxt name f (SUBSING a)
  updCtxt-DUM     : (a : Term) → updCtxt name f a → updCtxt name f (DUM a)
  updCtxt-FFDEFS  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (FFDEFS a b)
  updCtxt-UNIV    : (x : ℕ) → updCtxt name f (UNIV x)
  updCtxt-LIFT    : (a : Term) → updCtxt name f a → updCtxt name f (LIFT a)
  updCtxt-LOWER   : (a : Term) → updCtxt name f a → updCtxt name f (LOWER a)
  updCtxt-SHRINK  : (a : Term) → updCtxt name f a → updCtxt name f (SHRINK a)
  updCtxt-upd     : updCtxt name f (upd name f)


→updCtxt-shiftDown : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                     → updCtxt name f a
                     → updCtxt name f (shiftDown v a)
→updCtxt-shiftDown v {name} {f} cf {.(VAR x)} (updCtxt-VAR x) = updCtxt-VAR _
→updCtxt-shiftDown v {name} {f} cf {.NAT} updCtxt-NAT = updCtxt-NAT
→updCtxt-shiftDown v {name} {f} cf {.QNAT} updCtxt-QNAT = updCtxt-QNAT
→updCtxt-shiftDown v {name} {f} cf {.(LT a b)} (updCtxt-LT a b ctxt ctxt₁) = updCtxt-LT _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(QLT a b)} (updCtxt-QLT a b ctxt ctxt₁) = updCtxt-QLT _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(NUM x)} (updCtxt-NUM x) = updCtxt-NUM _
→updCtxt-shiftDown v {name} {f} cf {.(IFLT a b c d)} (updCtxt-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) = updCtxt-IFLT _ _ _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁) (→updCtxt-shiftDown v cf ctxt₂) (→updCtxt-shiftDown v cf ctxt₃)
→updCtxt-shiftDown v {name} {f} cf {.(PI a b)} (updCtxt-PI a b ctxt ctxt₁) = updCtxt-PI _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(LAMBDA a)} (updCtxt-LAMBDA a ctxt) = updCtxt-LAMBDA _ (→updCtxt-shiftDown (suc v) cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(APPLY a b)} (updCtxt-APPLY a b ctxt ctxt₁) = updCtxt-APPLY _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(FIX a)} (updCtxt-FIX a ctxt) = updCtxt-FIX _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(LET a b)} (updCtxt-LET a b ctxt ctxt₁) = updCtxt-LET _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(SUM a b)} (updCtxt-SUM a b ctxt ctxt₁) = updCtxt-SUM _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(PAIR a b)} (updCtxt-PAIR a b ctxt ctxt₁) = updCtxt-PAIR _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(SPREAD a b)} (updCtxt-SPREAD a b ctxt ctxt₁) = updCtxt-SPREAD _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc (suc v)) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(SET a b)} (updCtxt-SET a b ctxt ctxt₁) = updCtxt-SET _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(TUNION a b)} (updCtxt-TUNION a b ctxt ctxt₁) = updCtxt-TUNION _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(UNION a b)} (updCtxt-UNION a b ctxt ctxt₁) = updCtxt-UNION _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(QTUNION a b)} (updCtxt-QTUNION a b ctxt ctxt₁) = updCtxt-QTUNION _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(INL a)} (updCtxt-INL a ctxt) = updCtxt-INL _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(INR a)} (updCtxt-INR a ctxt) = updCtxt-INR _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(DECIDE a b c)} (updCtxt-DECIDE a b c ctxt ctxt₁ ctxt₂) = updCtxt-DECIDE _ _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown (suc v) cf ctxt₁) (→updCtxt-shiftDown (suc v) cf ctxt₂)
→updCtxt-shiftDown v {name} {f} cf {.(EQ a b c)} (updCtxt-EQ a b c ctxt ctxt₁ ctxt₂) = updCtxt-EQ _ _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁) (→updCtxt-shiftDown v cf ctxt₂)
→updCtxt-shiftDown v {name} {f} cf {.AX} updCtxt-AX = updCtxt-AX
→updCtxt-shiftDown v {name} {f} cf {.FREE} updCtxt-FREE = updCtxt-FREE
→updCtxt-shiftDown v {name} {f} cf {.(CHOOSE a b)} (updCtxt-CHOOSE a b ctxt ctxt₁) = updCtxt-CHOOSE _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(TSQUASH a)} (updCtxt-TSQUASH a ctxt) = updCtxt-TSQUASH _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(TTRUNC a)} (updCtxt-TTRUNC a ctxt) = updCtxt-TTRUNC _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(TCONST a)} (updCtxt-TCONST a ctxt) = updCtxt-TCONST _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(SUBSING a)} (updCtxt-SUBSING a ctxt) = updCtxt-SUBSING _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(DUM a)} (updCtxt-DUM a ctxt) = updCtxt-DUM _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(FFDEFS a b)} (updCtxt-FFDEFS a b ctxt ctxt₁) = updCtxt-FFDEFS _ _ (→updCtxt-shiftDown v cf ctxt) (→updCtxt-shiftDown v cf ctxt₁)
→updCtxt-shiftDown v {name} {f} cf {.(UNIV x)} (updCtxt-UNIV x) = updCtxt-UNIV _
→updCtxt-shiftDown v {name} {f} cf {.(LIFT a)} (updCtxt-LIFT a ctxt) = updCtxt-LIFT _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(LOWER a)} (updCtxt-LOWER a ctxt) = updCtxt-LOWER _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(SHRINK a)} (updCtxt-SHRINK a ctxt) = updCtxt-SHRINK _ (→updCtxt-shiftDown v cf ctxt)
→updCtxt-shiftDown v {name} {f} cf {.(upd name f)} updCtxt-upd rewrite #shiftDown (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updCtxt-upd



→updCtxt-shiftUp : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                     → updCtxt name f a
                     → updCtxt name f (shiftUp v a)
→updCtxt-shiftUp v {name} {f} cf {.(VAR x)} (updCtxt-VAR x) = updCtxt-VAR _
→updCtxt-shiftUp v {name} {f} cf {.NAT} updCtxt-NAT = updCtxt-NAT
→updCtxt-shiftUp v {name} {f} cf {.QNAT} updCtxt-QNAT = updCtxt-QNAT
→updCtxt-shiftUp v {name} {f} cf {.(LT a b)} (updCtxt-LT a b ctxt ctxt₁) = updCtxt-LT _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(QLT a b)} (updCtxt-QLT a b ctxt ctxt₁) = updCtxt-QLT _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(NUM x)} (updCtxt-NUM x) = updCtxt-NUM _
→updCtxt-shiftUp v {name} {f} cf {.(IFLT a b c d)} (updCtxt-IFLT a b c d ctxt ctxt₁ ctxt₂ ctxt₃) = updCtxt-IFLT _ _ _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁) (→updCtxt-shiftUp v cf ctxt₂) (→updCtxt-shiftUp v cf ctxt₃)
→updCtxt-shiftUp v {name} {f} cf {.(PI a b)} (updCtxt-PI a b ctxt ctxt₁) = updCtxt-PI _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp (suc v) cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(LAMBDA a)} (updCtxt-LAMBDA a ctxt) = updCtxt-LAMBDA _ (→updCtxt-shiftUp (suc v) cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(APPLY a b)} (updCtxt-APPLY a b ctxt ctxt₁) = updCtxt-APPLY _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(FIX a)} (updCtxt-FIX a ctxt) = updCtxt-FIX _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(LET a b)} (updCtxt-LET a b ctxt ctxt₁) = updCtxt-LET _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp (suc v) cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(SUM a b)} (updCtxt-SUM a b ctxt ctxt₁) = updCtxt-SUM _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp (suc v) cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(PAIR a b)} (updCtxt-PAIR a b ctxt ctxt₁) = updCtxt-PAIR _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(SPREAD a b)} (updCtxt-SPREAD a b ctxt ctxt₁) = updCtxt-SPREAD _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp (suc (suc v)) cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(SET a b)} (updCtxt-SET a b ctxt ctxt₁) = updCtxt-SET _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp (suc v) cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(TUNION a b)} (updCtxt-TUNION a b ctxt ctxt₁) = updCtxt-TUNION _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp (suc v) cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(UNION a b)} (updCtxt-UNION a b ctxt ctxt₁) = updCtxt-UNION _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(QTUNION a b)} (updCtxt-QTUNION a b ctxt ctxt₁) = updCtxt-QTUNION _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(INL a)} (updCtxt-INL a ctxt) = updCtxt-INL _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(INR a)} (updCtxt-INR a ctxt) = updCtxt-INR _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(DECIDE a b c)} (updCtxt-DECIDE a b c ctxt ctxt₁ ctxt₂) = updCtxt-DECIDE _ _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp (suc v) cf ctxt₁) (→updCtxt-shiftUp (suc v) cf ctxt₂)
→updCtxt-shiftUp v {name} {f} cf {.(EQ a b c)} (updCtxt-EQ a b c ctxt ctxt₁ ctxt₂) = updCtxt-EQ _ _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁) (→updCtxt-shiftUp v cf ctxt₂)
→updCtxt-shiftUp v {name} {f} cf {.AX} updCtxt-AX = updCtxt-AX
→updCtxt-shiftUp v {name} {f} cf {.FREE} updCtxt-FREE = updCtxt-FREE
→updCtxt-shiftUp v {name} {f} cf {.(CHOOSE a b)} (updCtxt-CHOOSE a b ctxt ctxt₁) = updCtxt-CHOOSE _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(TSQUASH a)} (updCtxt-TSQUASH a ctxt) = updCtxt-TSQUASH _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(TTRUNC a)} (updCtxt-TTRUNC a ctxt) = updCtxt-TTRUNC _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(TCONST a)} (updCtxt-TCONST a ctxt) = updCtxt-TCONST _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(SUBSING a)} (updCtxt-SUBSING a ctxt) = updCtxt-SUBSING _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(DUM a)} (updCtxt-DUM a ctxt) = updCtxt-DUM _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(FFDEFS a b)} (updCtxt-FFDEFS a b ctxt ctxt₁) = updCtxt-FFDEFS _ _ (→updCtxt-shiftUp v cf ctxt) (→updCtxt-shiftUp v cf ctxt₁)
→updCtxt-shiftUp v {name} {f} cf {.(UNIV x)} (updCtxt-UNIV x) = updCtxt-UNIV _
→updCtxt-shiftUp v {name} {f} cf {.(LIFT a)} (updCtxt-LIFT a ctxt) = updCtxt-LIFT _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(LOWER a)} (updCtxt-LOWER a ctxt) = updCtxt-LOWER _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(SHRINK a)} (updCtxt-SHRINK a ctxt) = updCtxt-SHRINK _ (→updCtxt-shiftUp v cf ctxt)
→updCtxt-shiftUp v {name} {f} cf {.(upd name f)} updCtxt-upd rewrite #shiftUp (suc (suc (suc v))) (ct (shiftUp 0 f) (→#shiftUp 0 {f} cf)) = updCtxt-upd



→updCtxt-subv : (v : Var) {name : Name} {f : Term} (cf : # f) {a b : Term}
                 → updCtxt name f a
                 → updCtxt name f b
                 → updCtxt name f (subv v b a)
→updCtxt-subv v {name} {f} cf {.(VAR x)} {b} (updCtxt-VAR x) ub with x ≟ v
... | yes p = ub
... | no p = updCtxt-VAR _
→updCtxt-subv v {name} {f} cf {.NAT} {b} updCtxt-NAT ub = updCtxt-NAT
→updCtxt-subv v {name} {f} cf {.QNAT} {b} updCtxt-QNAT ub = updCtxt-QNAT
→updCtxt-subv v {name} {f} cf {.(LT a b₁)} {b} (updCtxt-LT a b₁ ua ua₁) ub = updCtxt-LT _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(QLT a b₁)} {b} (updCtxt-QLT a b₁ ua ua₁) ub = updCtxt-QLT _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(NUM x)} {b} (updCtxt-NUM x) ub = updCtxt-NUM _
→updCtxt-subv v {name} {f} cf {.(IFLT a b₁ c d)} {b} (updCtxt-IFLT a b₁ c d ua ua₁ ua₂ ua₃) ub = updCtxt-IFLT _ _ _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub) (→updCtxt-subv v cf ua₂ ub) (→updCtxt-subv v cf ua₃ ub)
→updCtxt-subv v {name} {f} cf {.(PI a b₁)} {b} (updCtxt-PI a b₁ ua ua₁) ub = updCtxt-PI _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv (suc v) cf ua₁ (→updCtxt-shiftUp 0 cf ub))
→updCtxt-subv v {name} {f} cf {.(LAMBDA a)} {b} (updCtxt-LAMBDA a ua) ub = updCtxt-LAMBDA _ (→updCtxt-subv (suc v) cf ua (→updCtxt-shiftUp 0 cf ub))
→updCtxt-subv v {name} {f} cf {.(APPLY a b₁)} {b} (updCtxt-APPLY a b₁ ua ua₁) ub = updCtxt-APPLY _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(FIX a)} {b} (updCtxt-FIX a ua) ub = updCtxt-FIX _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(LET a b₁)} {b} (updCtxt-LET a b₁ ua ua₁) ub = updCtxt-LET _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv (suc v) cf ua₁ (→updCtxt-shiftUp 0 cf ub))
→updCtxt-subv v {name} {f} cf {.(SUM a b₁)} {b} (updCtxt-SUM a b₁ ua ua₁) ub = updCtxt-SUM _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv (suc v) cf ua₁ (→updCtxt-shiftUp 0 cf ub))
→updCtxt-subv v {name} {f} cf {.(PAIR a b₁)} {b} (updCtxt-PAIR a b₁ ua ua₁) ub = updCtxt-PAIR _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(SPREAD a b₁)} {b} (updCtxt-SPREAD a b₁ ua ua₁) ub = updCtxt-SPREAD _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv (suc (suc v)) cf ua₁ (→updCtxt-shiftUp 0 cf (→updCtxt-shiftUp 0 cf ub)))
→updCtxt-subv v {name} {f} cf {.(SET a b₁)} {b} (updCtxt-SET a b₁ ua ua₁) ub = updCtxt-SET _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv (suc v) cf ua₁ (→updCtxt-shiftUp 0 cf ub))
→updCtxt-subv v {name} {f} cf {.(TUNION a b₁)} {b} (updCtxt-TUNION a b₁ ua ua₁) ub = updCtxt-TUNION _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv (suc v) cf ua₁ (→updCtxt-shiftUp 0 cf ub))
→updCtxt-subv v {name} {f} cf {.(UNION a b₁)} {b} (updCtxt-UNION a b₁ ua ua₁) ub = updCtxt-UNION _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(QTUNION a b₁)} {b} (updCtxt-QTUNION a b₁ ua ua₁) ub = updCtxt-QTUNION _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(INL a)} {b} (updCtxt-INL a ua) ub = updCtxt-INL _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(INR a)} {b} (updCtxt-INR a ua) ub = updCtxt-INR _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(DECIDE a b₁ c)} {b} (updCtxt-DECIDE a b₁ c ua ua₁ ua₂) ub = updCtxt-DECIDE _ _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv (suc v) cf ua₁ (→updCtxt-shiftUp 0 cf ub)) (→updCtxt-subv (suc v) cf ua₂ (→updCtxt-shiftUp 0 cf ub))
→updCtxt-subv v {name} {f} cf {.(EQ a b₁ c)} {b} (updCtxt-EQ a b₁ c ua ua₁ ua₂) ub = updCtxt-EQ _ _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub) (→updCtxt-subv v cf ua₂ ub)
→updCtxt-subv v {name} {f} cf {.AX} {b} updCtxt-AX ub = updCtxt-AX
→updCtxt-subv v {name} {f} cf {.FREE} {b} updCtxt-FREE ub = updCtxt-FREE
→updCtxt-subv v {name} {f} cf {.(CHOOSE a b₁)} {b} (updCtxt-CHOOSE a b₁ ua ua₁) ub = updCtxt-CHOOSE _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(TSQUASH a)} {b} (updCtxt-TSQUASH a ua) ub = updCtxt-TSQUASH _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(TTRUNC a)} {b} (updCtxt-TTRUNC a ua) ub = updCtxt-TTRUNC _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(TCONST a)} {b} (updCtxt-TCONST a ua) ub = updCtxt-TCONST _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(SUBSING a)} {b} (updCtxt-SUBSING a ua) ub = updCtxt-SUBSING _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(DUM a)} {b} (updCtxt-DUM a ua) ub = updCtxt-DUM _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(FFDEFS a b₁)} {b} (updCtxt-FFDEFS a b₁ ua ua₁) ub = updCtxt-FFDEFS _ _ (→updCtxt-subv v cf ua ub) (→updCtxt-subv v cf ua₁ ub)
→updCtxt-subv v {name} {f} cf {.(UNIV x)} {b} (updCtxt-UNIV x) ub = updCtxt-UNIV _
→updCtxt-subv v {name} {f} cf {.(LIFT a)} {b} (updCtxt-LIFT a ua) ub = updCtxt-LIFT _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(LOWER a)} {b} (updCtxt-LOWER a ua) ub = updCtxt-LOWER _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(SHRINK a)} {b} (updCtxt-SHRINK a ua) ub = updCtxt-SHRINK _ (→updCtxt-subv v cf ua ub)
→updCtxt-subv v {name} {f} cf {.(upd name f)} {b} updCtxt-upd ub
  rewrite subv# (suc (suc (suc v))) (shiftUp 0 (shiftUp 0 (shiftUp 0 b))) (shiftUp 0 f) (→#shiftUp 0 {f} cf)
  = updCtxt-upd



updCtxt-sub : {name : Name} {f : Term} {a b : Term}
              → # f
              → updCtxt name f a
              → updCtxt name f b
              → updCtxt name f (sub a b)
updCtxt-sub {name} {f} {a} {b} cf ua ub = →updCtxt-shiftDown 0 cf (→updCtxt-subv 0 cf ub (→updCtxt-shiftUp 0 cf ua))


updCtxt-LAMBDA→ : {name : Name} {f t : Term}
                   → updCtxt name f (LAMBDA t)
                   → updCtxt name f t ⊎ t ≡ updBody name f
updCtxt-LAMBDA→ {name} {f} {t} (updCtxt-LAMBDA .t u) = inj₁ u
updCtxt-LAMBDA→ {name} {f} {.(updBody name f)} updCtxt-upd = inj₂ refl


updCtxt-CS→ : {name n : Name} {f : Term}
               → updCtxt name f (CS n)
               → ⊥
updCtxt-CS→ {name} {n} {f} ()


getT≤ℕ : 𝕎· → ℕ → Name → Set
getT≤ℕ w1 n name = Σ ℕ (λ j → getT 0 name w1 ≡ just (NUM j) × j ≤ n)


isHighestℕ : {k : ℕ} {w1 w2 : 𝕎·} {a b : Term} (n : ℕ) (name : Name)
              → steps k (a , w1) ≡ (b , w2)
              → Set
isHighestℕ {0} {w1} {w2} {a} {b} n name comp = getT≤ℕ w1 n name
isHighestℕ {suc k} {w1} {w2} {a} {b} n name comp with step a w1
... | just (x , w) = getT≤ℕ w1 n name × isHighestℕ {k} {w} {w2} {x} {b} n name comp
... | nothing = getT≤ℕ w1 n name



ΣhighestUpdCtxtAux : (k' : ℕ) (name : Name) (f : Term) (n : ℕ) (a a' : Term) (w0 w w' : 𝕎·) → Set(L)
ΣhighestUpdCtxtAux k' name f n a a' w0 w w' =
  Σ (steps k' (a , w) ≡ (a' , w')) (λ comp →
    (getT≤ℕ w' n name → (getT≤ℕ w0 n name × isHighestℕ {k'} {w} {w'} {a} {a'} n name comp))
    × updCtxt name f a')



ΣhighestUpdCtxt : (name : Name) (f : Term) (n : ℕ) (a : Term) (w0 w : 𝕎·) → Set(L)
ΣhighestUpdCtxt name f n a w0 w =
  Σ ℕ (λ k' → Σ Term (λ a' → Σ 𝕎· (λ w' →
    ΣhighestUpdCtxtAux k' name f n a a' w0 w w')))


isHighestℕ-IFLT₁ : {k : ℕ} {a a' : Term} {w w' : 𝕎·} {n : ℕ} {name : Name} (b c d : Term)
                    → (comp : steps k (a , w) ≡ (a' , w'))
                    → isHighestℕ {k} {w} {w'} {a} {a'} n name comp
                    → Σ ℕ (λ k' → Σ (steps k' (IFLT a b c d , w) ≡ (IFLT a' b c d , w'))
                         (isHighestℕ {k'} {w} {w'} {IFLT a b c d} {IFLT a' b c d} n name))
isHighestℕ-IFLT₁ {0} {a} {a'} {w} {w'} {n} {name} b c d comp h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) =
  0 , refl , h
isHighestℕ-IFLT₁ {suc k} {a} {a'} {w} {w'} {n} {name} b c d comp h with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ x rewrite stepVal a w x | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) = ind
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFLT a b c d , w) ≡ (IFLT a' b c d , w'))
            (isHighestℕ {k'} {w} {w'} {IFLT a b c d} {IFLT a' b c d} n name))
    ind = isHighestℕ-IFLT₁ {k} {a} {a'} {w} {w'} {n} {name} b c d comp (snd h)
... |    inj₂ x = suc (fst ind) , comp1
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFLT a1 b c d , w1) ≡ (IFLT a' b c d , w'))
            (isHighestℕ {k'} {w1} {w'} {IFLT a1 b c d} {IFLT a' b c d} n name))
    ind = isHighestℕ-IFLT₁ {k} {a1} {a'} {w1} {w'} {n} {name} b c d comp (snd h)

    comp1 : Σ (steps (suc (fst ind)) (IFLT a b c d , w) ≡ (IFLT a' b c d , w'))
              (isHighestℕ {suc (fst ind)} {w} {w'} {IFLT a b c d} {IFLT a' b c d} n name)
    comp1 with is-NUM a
    ... | inj₁ (na , pa) rewrite pa = ⊥-elim (x tt)
    ... | inj₂ pa rewrite z = fst (snd ind) , fst h , snd (snd ind)
isHighestℕ-IFLT₁ {suc k} {a} {a'} {w} {w'} {n} {name} b c d comp h | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl , h



isHighestℕ-IFLT₂ : {k : ℕ} {b b' : Term} {w w' : 𝕎·} {n : ℕ} {name : Name} (m : ℕ) (c d : Term)
                    → (comp : steps k (b , w) ≡ (b' , w'))
                    → isHighestℕ {k} {w} {w'} {b} {b'} n name comp
                    → Σ ℕ (λ k' → Σ (steps k' (IFLT (NUM m) b c d , w) ≡ (IFLT (NUM m) b' c d , w'))
                         (isHighestℕ {k'} {w} {w'} {IFLT (NUM m) b c d} {IFLT (NUM m) b' c d} n name))
isHighestℕ-IFLT₂ {0} {b} {b'} {w} {w'} {n} {name} m c d comp h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) =
  0 , refl , h
isHighestℕ-IFLT₂ {suc k} {b} {b'} {w} {w'} {n} {name} m c d comp h with step⊎ b w
... | inj₁ (b1 , w1 , z) rewrite z with isValue⊎ b
... |    inj₁ x rewrite stepVal b w x | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) = ind
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFLT (NUM m) b c d , w) ≡ (IFLT (NUM m) b' c d , w'))
            (λ comp' → isHighestℕ {k'} {w} {w'} {IFLT (NUM m) b c d} {IFLT (NUM m) b' c d} n name comp'))
    ind = isHighestℕ-IFLT₂ {k} {b} {b'} {w} {w'} {n} {name} m c d comp (snd h)
... |    inj₂ x = suc (fst ind) , comp1
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFLT (NUM m) b1 c d , w1) ≡ (IFLT (NUM m) b' c d , w'))
            (λ comp' → isHighestℕ {k'} {w1} {w'} {IFLT (NUM m) b1 c d} {IFLT (NUM m) b' c d} n name comp'))
    ind = isHighestℕ-IFLT₂ {k} {b1} {b'} {w1} {w'} {n} {name} m c d comp (snd h)

    comp1 : Σ (steps (suc (fst ind)) (IFLT (NUM m) b c d , w) ≡ (IFLT (NUM m) b' c d , w'))
              (isHighestℕ {suc (fst ind)} {w} {w'} {IFLT (NUM m) b c d} {IFLT (NUM m) b' c d} n name)
    comp1 with is-NUM b
    ... | inj₁ (nb , pb) rewrite pb = ⊥-elim (x tt)
    ... | inj₂ pb rewrite z = fst (snd ind) , fst h , snd (snd ind)
isHighestℕ-IFLT₂ {suc k} {b} {b'} {w} {w'} {n} {name} m c d comp h | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl , h




presHighestℕ : (name : Name) (f : Term) (k : ℕ) → Set(L)
presHighestℕ name f k =
  {w1 w2 : 𝕎·} {a b : Term} {n : ℕ}
  (comp : steps k (a , w1) ≡ (b , w2))
  → isValue b
  → updCtxt name f a
  → getT≤ℕ w2 n name --getT 0 name w2 ≡ just (NUM n)
  → isHighestℕ {k} {w1} {w2} {a} {b} n name comp


stepsPresHighestℕ : (name : Name) (f : Term) (b : Term) (w : 𝕎·) → Set(L)
stepsPresHighestℕ name f b w =
  Σ ℕ (λ k → Σ Term (λ v → Σ 𝕎· (λ w' →
    steps k (b , w) ≡ (v , w')
    × isValue v
    × ((k' : ℕ) → k' ≤ k → presHighestℕ name f k'))))




stepsPresHighestℕ-IFLT₁→ : {name : Name} {f : Term} {a b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (IFLT a b c d) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-IFLT₁→ {name} {f} {a} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = IFLT→hasValue k a b c d v w w' comp isv



stepsPresHighestℕ-IFLT₂→ : {name : Name} {f : Term} {n : ℕ} {b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (IFLT (NUM n) b c d) w
                            → stepsPresHighestℕ name f b w
stepsPresHighestℕ-IFLT₂→ {name} {f} {n} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k b w
    hv = IFLT-NUM→hasValue k n b c d v w w' comp isv


→step-IFLT₂ : {w w' : 𝕎·} {n : ℕ} {b b' : Term} (c d : Term)
               → ¬ isValue b
               → step b w ≡ just (b' , w')
               → step (IFLT (NUM n) b c d) w ≡ just (IFLT (NUM n) b' c d , w')
→step-IFLT₂ {w} {w'} {n} {b} {b'} c d nv s with is-NUM b
... | inj₁ (k , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite s = refl



ΣhighestUpdCtxtAux-IFLT₂-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {b b1 b' : Term} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {c d : Term}
                               → ¬ isValue b
                               → step b w ≡ just (b1 , w1)
                               → (comp : steps k (b1 , w1) ≡ (b' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {b1} {b'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (IFLT (NUM m) b1 c d) (IFLT (NUM m) b' c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (IFLT (NUM m) b c d) (IFLT (NUM m) b' c d) w0 w w'
ΣhighestUpdCtxtAux-IFLT₂-aux {j} {k} {w} {w0} {w1} {w'} {b} {b1} {b'} {name} {f} {n} {m} {c} {d} nv comp0 comp i (comp1 , g , u) with is-NUM b
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-IFLT₂ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b b' c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxtAux k name f n b b' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFLT (NUM m) b c d) (IFLT (NUM m) b' c d) w0 w w')
ΣhighestUpdCtxtAux-IFLT₂ {0} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFLT _ _ _ _ (updCtxt-NUM m) u uc ud
ΣhighestUpdCtxtAux-IFLT₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , u) with step⊎ b w
... | inj₁ (b1 , w1 , z) rewrite z with isValue⊎ b
... |    inj₁ y rewrite stepVal b w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-IFLT₂ {k} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-IFLT₂-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFLT (NUM m) b1 c d) (IFLT (NUM m) b' c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-IFLT₂ {k} {name} {f} {n} {m} {b1} {b'} {c} {d} {w0} {w1} {w'} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-IFLT₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFLT _ _ _ _ (updCtxt-NUM m) u uc ud



ΣhighestUpdCtxt-IFLT₂ : {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b c d : Term} {w0 w : 𝕎·}
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxt name f n b w0 w
                        → ΣhighestUpdCtxt name f n (IFLT (NUM m) b c d) w0 w
ΣhighestUpdCtxt-IFLT₂ {name} {f} {n} {m} {b} {c} {d} {w0} {w} uc ud (k , b' , w' , wcomp , i , u) =
  fst q , IFLT (NUM m) b' c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFLT (NUM m) b c d) (IFLT (NUM m) b' c d) w0 w w')
    q = ΣhighestUpdCtxtAux-IFLT₂ {k} uc ud (wcomp , i , u)





ΣhighestUpdCtxtAux-IFLT₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b c d : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (IFLT a1 b c d) (IFLT a' b c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (IFLT a b c d) (IFLT a' b c d) w0 w w'
ΣhighestUpdCtxtAux-IFLT₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} {c} {d} nv comp0 comp i (comp1 , g , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-IFLT₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFLT a b c d) (IFLT a' b c d) w0 w w')
ΣhighestUpdCtxtAux-IFLT₁ {0} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFLT _ _ _ _ u ub uc ud
ΣhighestUpdCtxtAux-IFLT₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-IFLT₁ {k} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-IFLT₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFLT a1 b c d) (IFLT a' b c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-IFLT₁ {k} {name} {f} {n} {a1} {a'} {b} {c} {d} {w0} {w1} {w'} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-IFLT₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFLT _ _ _ _ u ub uc ud



ΣhighestUpdCtxt-IFLT₁ : {name : Name} {f : Term} {n : ℕ} {a b c d : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (IFLT a b c d) w0 w
ΣhighestUpdCtxt-IFLT₁ {name} {f} {n} {a} {b} {c} {d} {w0} {w} ub uc ud (k , a' , w' , wcomp , i , u) =
  fst q , IFLT a' b c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFLT a b c d) (IFLT a' b c d) w0 w w')
    q = ΣhighestUpdCtxtAux-IFLT₁ {k} ub uc ud (wcomp , i , u)




{--
→steps-LET : {k : ℕ} {a b v : Term} {w1 w2 : 𝕎·}
              → steps k (a , w1) ≡ (v , w2)
              → isValue v
              → Σ ℕ (λ k' → k' ≤ k × steps k' (LET a b , w1) ≡ (sub v b , w2))
→steps-LET {k} {a} {b} {v} {w1} {w2} comp1 isv = {!!}



→steps-upd-body : {k1 k2 : ℕ} {f a v : Term} {name : Name} {m : ℕ} {w1 w2 w3 : 𝕎·}
                   → steps k1 (a , w1) ≡ (NUM m , w2)
                   → steps k2 (updGt name (NAME m) , w2) ≡ (v , w3)
                   → isValue v
                   → Σ ℕ (λ k → k ≤ k1 + k2 × steps k (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , w3))
→steps-upd-body {k1} {k2} {a} {v} {name} {m} {w1} {w2} {w3} comp1 comp2 isv = {!!}
--}


sub-APPLY-shift-NUM : {a f u : Term} {m : ℕ}
                      → # f
                      → u ≡ NUM m
                      → sub a (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) ≡ APPLY f (NUM m)
sub-APPLY-shift-NUM {a} {f} {u} {m} cf equ rewrite equ | subNotIn a f cf = refl



steps-trans : {k1 k2 : ℕ} {a b c : Term} {w1 w2 w3 : 𝕎·}
              → steps k1 (a , w1) ≡ (b , w2)
              → steps k2 (b , w2) ≡ (c , w3)
              → Σ ℕ (λ k → k ≤ k1 + k2 × steps k (a , w1) ≡ (c , w3))
steps-trans {0} {k2} {a} {b} {c} {w1} {w2} {w3} comp1 comp2
   rewrite pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = k2 , ≤-refl , comp2
steps-trans {suc k1} {k2} {a} {b} {c} {w1} {w2} {w3} comp1 comp2 with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z =
  suc (fst ind) , _≤_.s≤s (fst (snd ind)) ,
  step-steps-trans {w1} {w1'} {w3} {a} {a'} {c} {fst ind} z (snd (snd ind))
  where
    ind : Σ ℕ (λ k → k ≤ k1 + k2 × steps k (a' , w1') ≡ (c , w3))
    ind = steps-trans {k1} {k2} {a'} {b} {c} {w1'} {w2} {w3} comp1 comp2
... | inj₂ z rewrite z | pair-inj₁ (sym comp1) | pair-inj₂ (sym comp1) = k2 , m≤n+m k2 (suc k1) , comp2


+0 : (n : ℕ) → n + 0 ≡ n
+0 0 = refl
+0 (suc n) rewrite +0 n = refl


steps-counter-aux1 : {k1 k2 k3 k4 : ℕ} → 0 < k4 → k3 + k4 < k2 → suc k1 + suc k3 ≤ k1 + k2
steps-counter-aux1 {k1} {k2} {k3} {k4} h q rewrite sym (+-suc k1 (suc k3)) =
  +-monoʳ-≤ k1 (≤-trans (≤-trans c (+-monoʳ-≤ (suc k3) h)) q)
  where
    c : suc (suc k3) ≤ suc (k3 + 1)
    c rewrite +-suc k3 0 | +0 k3 = ≤-refl



steps-APPLY-to-val>0 : {k : ℕ} {a b v : Term} {w1 w2 : 𝕎·}
                       → steps k (APPLY a b , w1) ≡ (v , w2)
                       → isValue v
                       → 0 < k
steps-APPLY-to-val>0 {0} {a} {b} {v} {w1} {w2} comp isv rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv
steps-APPLY-to-val>0 {suc k} {a} {b} {v} {w1} {w2} comp isv = _≤_.s≤s _≤_.z≤n



chooseT0if : (name : Name) (w : 𝕎·) (n m : ℕ) → 𝕎·
chooseT0if name w n m with n <? m
... | yes x = chooseT name w (NUM m)
... | no x = w



steps-CHOOSE-NAME→𝕎 : {k : ℕ} {name : Name} {w1 w2 : 𝕎·} {t u : Term}
                        → isValue u
                        → steps k (CHOOSE (NAME name) t , w1) ≡ (u , w2)
                        → w2 ≡ chooseT name w1 t
steps-CHOOSE-NAME→𝕎 {0} {name} {w1} {w2} {t} {u} isv comp
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv
steps-CHOOSE-NAME→𝕎 {suc k} {name} {w1} {w2} {t} {u} isv comp
  rewrite stepsVal AX (chooseT name w1 t) k tt | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = refl



⊎→≡chooseT0if : {n m : ℕ} {k : ℕ} {name : Name} {u : Term} {w1 w2 : 𝕎·}
                 → isValue u
--                 → getT 0 name w1 ≡ just (NUM n)
                 → ((n < m × steps k (setT name (NUM m) , w1) ≡ (u , w2)) ⊎ (m ≤ n × steps k (AX , w1) ≡ (u , w2)))
                 → w2 ≡ chooseT0if name w1 n m
⊎→≡chooseT0if {n} {m} {k} {name} {u} {w1} {w2} isv {--g0--} (inj₁ (ltm , comp))
--  rewrite g0
  with n <? m
... | yes x = steps-CHOOSE-NAME→𝕎 {k} isv comp
... | no x = ⊥-elim (x ltm)
⊎→≡chooseT0if {n} {m} {k} {name} {u} {w1} {w2} isv {--g0--} (inj₂ (ltm , comp))
  rewrite {--g0 |--} stepsVal AX w1 k tt | pair-inj₁ (sym comp) | pair-inj₂ (sym comp)
  with n <? m
... | yes x = ⊥-elim (≤⇒≯ ltm x)
... | no x = refl



upd-decomp : {k : ℕ} {name : Name} {f a v : Term} {w1 w2 : 𝕎·}
             → # f
             → ∀𝕎-get0-NUM w1 name
             → steps k (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w2)
             → isValue v
             → Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w1' → Σ ℕ (λ m → Σ ℕ (λ m' →
                 k1 < k
                 × k2 < k
                 × getT 0 name w1' ≡ just (NUM m')
                 × ssteps k1 (a , w1) ≡ just (NUM m , w1')
                 × steps k2 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (APPLY f (NUM m) , chooseT0if name w1' m' m))))))
--                 steps→𝕎s {k1} {w1} {w1'} {a} {NUM m} comp1 ++ w1' ∷ chooseT0if name w1' m' m ∷ chooseT0if name w1' m' m ∷ []
--                 ≡ steps→𝕎s {k2} {w1} {chooseT0if name w1' m' m} {LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0)))} {APPLY f (NUM m)} comp2
--)))))
upd-decomp {k} {name} {f} {a} {v} {w1} {w2} cf gtn comp isv =
  k1 , k8 , w3 , m , n ,
  <-transʳ (m≤m+n k1 k2) ltk12 ,
  k8<k ,
  g2a ,
  comp1b ,
  comp9b
  where
    seqv : Term
    seqv = SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))

    h1 : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w → Σ Term (λ u →
            ssteps k1 (a , w1) ≡ just (u , w)
            × isValue u
            × steps k2 (sub u seqv , w) ≡ (v , w2)
            × steps (suc k1) (LET a seqv , w1) ≡ (sub u seqv , w)
--            steps→𝕎s {k1} {w1} {w} {a} {u} comp1 ++ Data.List.[ w ] ≡ steps→𝕎s {suc k1} {w1} {w} {LET a seqv} {sub u seqv} comp2
            × k1 + k2 < k))))
    h1 = strict-LET→hasValue-decomp k a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) v w1 w2 comp isv

    k1 : ℕ
    k1 = fst h1

    k2 : ℕ
    k2 = fst (snd h1)

    w3 : 𝕎·
    w3 = fst (snd (snd h1))

    u : Term
    u = fst (snd (snd (snd h1)))

    comp1 : ssteps k1 (a , w1) ≡ just (u , w3)
    comp1 = fst (snd (snd (snd (snd h1))))

    isvu : isValue u
    isvu = fst (snd (snd (snd (snd (snd h1)))))

    comp2 : steps k2 (sub u (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w3) ≡ (v , w2)
    comp2 = fst (snd (snd (snd (snd (snd (snd h1))))))

    comp2x : steps (suc k1) (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))), w1) ≡ (sub u (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w3)
    comp2x = fst (snd (snd (snd (snd (snd (snd (snd h1)))))))

    ltk12 : k1 + k2 < k
    ltk12 = snd (snd (snd (snd (snd (snd (snd (snd h1)))))))

    comp2xb : steps (suc k1) (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))), w1) ≡ (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3)
    comp2xb rewrite sym (sub-SEQ-updGt u name f cf) = comp2x

    comp3 : steps k2 (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (v , w2)
    comp3 rewrite sym (sub-SEQ-updGt u name f cf) = comp2

--    eqws1 : steps→𝕎s {k1} {w1} {w3} {a} {u} comp1 ++ Data.List.[ w3 ] ≡ steps→𝕎s {suc k1} {w1} {w3} {LET a seqv} {sub u seqv} comp2x
--    eqws1 = fst (snd (snd (snd (snd (snd (snd (snd (snd h1))))))))

    e13 : w1 ⊑· w3
    e13 = steps→⊑ k1 a u (ssteps→steps {k1} {a} {u} {w1} {w3} comp1)

    h2 : Σ ℕ (λ k3 → Σ ℕ (λ k4 → Σ 𝕎· (λ w4 → Σ Term (λ u' →
           ssteps k3 (updGt name u , w3) ≡ just (u' , w4)
           × isValue u'
           × steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
           × steps (suc k3) (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4)
--           steps→𝕎s {k3} {w3} {w4} {updGt name u} {u'} comp1 ++ Data.List.[ w4 ] ≡ steps→𝕎s {suc k3} {w3} {w4} {LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} {sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} comp2
           × k3 + k4 < k2))))
    h2 = strict-LET→hasValue-decomp k2 (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) v w3 w2 comp3 isv

    k3 : ℕ
    k3 = fst h2

    k4 : ℕ
    k4 = fst (snd h2)

    w4 : 𝕎·
    w4 = fst (snd (snd h2))

    u' : Term
    u' = fst (snd (snd (snd h2)))

    comp4 : ssteps k3 (updGt name u , w3) ≡ just (u' , w4)
    comp4 = fst (snd (snd (snd (snd h2))))

    isvu' : isValue u'
    isvu' = fst (snd (snd (snd (snd (snd h2)))))

    comp5 : steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
    comp5 = fst (snd (snd (snd (snd (snd (snd h2))))))

    comp5x : steps (suc k3) (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4)
    comp5x = fst (snd (snd (snd (snd (snd (snd (snd h2)))))))

--    eqws2 : steps→𝕎s {k3} {w3} {w4} {updGt name u} {u'} comp4 ++ Data.List.[ w4 ] ≡ steps→𝕎s {suc k3} {w3} {w4} {LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} {sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} comp5x
--    eqws2 = fst (snd (snd (snd (snd (snd (snd (snd (snd h2))))))))

    ltk34 : k3 + k4 < k2
    ltk34 = snd (snd (snd (snd (snd (snd (snd (snd h2)))))))

    h3 : Σ ℕ (λ k5 → Σ ℕ (λ k6 → Σ ℕ (λ k7 → Σ 𝕎· (λ w5 → Σ 𝕎· (λ w6 → Σ ℕ (λ n → Σ ℕ (λ m →
           steps k5 (get0 name , w3) ≡ (NUM n , w5)
           × steps k6 (u , w5) ≡ (NUM m , w6)
           × ((n < m × steps k7 (setT name u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
           × k5 + k6 + k7 < k3)))))))
    h3 = IFLT→hasValue-decomp k3 (get0 name) u (setT name u) AX u' w3 w4 (ssteps→steps {k3} {updGt name u} {u'} {w3} {w4} comp4) isvu'

    k5 : ℕ
    k5 = fst h3

    k6 : ℕ
    k6 = fst (snd h3)

    k7 : ℕ
    k7 = fst (snd (snd h3))

    w5 : 𝕎·
    w5 = fst (snd (snd (snd h3)))

    w6 : 𝕎·
    w6 = fst (snd (snd (snd (snd h3))))

    n : ℕ
    n = fst (snd (snd (snd (snd (snd h3)))))

    m : ℕ
    m = fst (snd (snd (snd (snd (snd (snd h3))))))

    comp6 : steps k5 (get0 name , w3) ≡ (NUM n , w5)
    comp6 = fst (snd (snd (snd (snd (snd (snd (snd h3)))))))

    comp7 : steps k6 (u , w5) ≡ (NUM m , w6)
    comp7 = fst (snd (snd (snd (snd (snd (snd (snd (snd h3))))))))

    comp8 : ((n < m × steps k7 (setT name u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
    comp8 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))

    ltk567 : k5 + k6 + k7 < k3
    ltk567 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))

    eqm : u ≡ NUM m
    eqm = stepsVal→ₗ u (NUM m) w5 w6 k6 isvu comp7

    eqw56 : w5 ≡ w6
    eqw56 = stepsVal→ᵣ u (NUM m) w5 w6 k6 isvu comp7

    comp1b : ssteps k1 (a , w1) ≡ just (NUM m , w3)
    comp1b rewrite sym eqm = comp1

    comp5b : steps k4 (APPLY f (NUM m) , w4) ≡ (v , w2)
    comp5b = sym (begin
                    (v , w2)
                  ≡⟨ sym comp5 ⟩
                    steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4)
                  ≡⟨ cong (λ x → steps k4 (x , w4)) (sub-APPLY-shift-NUM {u'} {f} {u} {m} cf eqm) ⟩
                   steps k4 (APPLY f (NUM m) , w4)
                  ∎)

    ltk04 : 0 < k4
    ltk04 = steps-APPLY-to-val>0 comp5b isv

    comp5xb : steps (suc k3) (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (APPLY f (NUM m) , w4)
    comp5xb = begin
                steps (suc k3) (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3)
              ≡⟨ comp5x ⟩
                (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4)
              ≡⟨ cong (λ x → (x , w4)) (sub-APPLY-shift-NUM cf eqm) ⟩
                (APPLY f (NUM m) , w4)
              ∎

-- need comp2xb to be a ssteps and k3 to be 2/3
    cc1 : Σ ℕ (λ k → k ≤ suc k1 + suc k3 × steps k (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))), w1) ≡ (APPLY f (NUM m) , w4))
    cc1 = steps-trans comp2xb comp5xb

    k8 : ℕ
    k8 = fst cc1

    ltk8 : k8 ≤ suc k1 + suc k3
    ltk8 = fst (snd cc1)

    k8<k : k8 < k
    k8<k = <-transʳ ltk8 (<-transʳ (steps-counter-aux1 ltk04 ltk34) ltk12)

    comp9 : steps k8 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))), w1) ≡ (APPLY f (NUM m) , w4)
    comp9 = snd (snd cc1)

    h5 : Σ Term (λ u → Σ ℕ (λ k5' → k5' < k5 × getT 0 name w3 ≡ just u × steps k5' (u , w3) ≡ (NUM n , w5)))
    h5 = steps-get0 k5 name w3 w5 (NUM n) tt comp6

    c1 : Term
    c1 = fst h5

    k5' : ℕ
    k5' = fst (snd h5)

    ltk5' : k5' < k5
    ltk5' = fst (snd (snd h5))

    g2 : getT 0 name w3 ≡ just c1
    g2 = fst (snd (snd (snd h5)))

    comp6b : steps k5' (c1 , w3) ≡ (NUM n , w5)
    comp6b = snd (snd (snd (snd h5)))

    gtn0 : Σ ℕ (λ j → getT 0 name w3 ≡ just (NUM j))
    gtn0 = lower (gtn w3 e13)

    eqc1 : c1 ≡ NUM n
    eqc1 = fst (Σ≡just-NUM×steps→≡NUM k5' (getT 0 name w3) c1 n w3 w5 gtn0 g2 comp6b)

    eqw35 : w3 ≡ w5
    eqw35 = snd (Σ≡just-NUM×steps→≡NUM k5' (getT 0 name w3) c1 n w3 w5 gtn0 g2 comp6b)

    g2a : getT 0 name w3 ≡ just (NUM n)
    g2a rewrite sym eqc1 = g2

    g2b : getT 0 name w6 ≡ just (NUM n)
    g2b rewrite sym eqw56 | sym eqw35 = g2a

    comp8b : ((n < m × steps k7 (setT name (NUM m) , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
    comp8b rewrite sym eqm = comp8

    eqw4' : w4 ≡ chooseT0if name w6 n m
    eqw4' = ⊎→≡chooseT0if {n} {m} {k7} isvu' {--g2b--} comp8b

    eqw4 : w4 ≡ chooseT0if name w3 n m
    eqw4 = begin
             w4
           ≡⟨ eqw4' ⟩
             chooseT0if name w6 n m
           ≡⟨ cong (λ x → chooseT0if name x n m) (sym (trans eqw35 eqw56)) ⟩
             chooseT0if name w3 n m
           ∎

    comp9b : steps k8 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))), w1) ≡ (APPLY f (NUM m) , chooseT0if name w3 n m)
    comp9b = begin
               steps k8 (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))), w1)
             ≡⟨ comp9 ⟩
               (APPLY f (NUM m) , w4)
             ≡⟨ cong (λ x → (APPLY f (NUM m) , x)) eqw4 ⟩
               (APPLY f (NUM m) , chooseT0if name w3 n m)
             ∎

\end{code}

