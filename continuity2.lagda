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


module continuity2 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                   (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                   (X : ChoiceExt W C)
                   (N : NewChoice {L} W C K G)
                   (E : Axiom.Extensionality.Propositional.Extensionality 0ℓ (lsuc(lsuc(L))))
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
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (⇓-from-to→≡𝕎 ; ⇓-from-to≡wᵣ ; ⇓-from-to≡wₗ)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)



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



SUC⇓val→steps : {n : ℕ} {t v : Term} {w1 w2 : 𝕎·}
                → steps n (SUC t , w1) ≡ (v , w2)
                → isValue v
                → Σ ℕ (λ k → steps n (t , w1) ≡ (NUM k , w2) × v ≡ NUM (suc k))
SUC⇓val→steps {0} {t} {v} {w1} {w2} comp isv
  rewrite pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv
SUC⇓val→steps {suc n} {t} {v} {w1} {w2} comp isv with is-NUM t
... | inj₁ (k , p) rewrite p | stepsVal (NUM (suc k)) w1 n tt | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = k , stepsVal (NUM k) w1 n tt , refl
... | inj₂ p with step⊎ t w1
... |    inj₁ (t' , w1' , z) rewrite z = ind
  where
    ind : Σ ℕ (λ k → steps n (t' , w1') ≡ (NUM k , w2) × v ≡ NUM (suc k))
    ind = SUC⇓val→steps {n} {t'} {v} {w1'} {w2} comp isv
... |    inj₂ z rewrite z | pair-inj₁ (sym comp) | pair-inj₂ (sym comp) = ⊥-elim isv



SUC⇓val→ : {t v : Term} {w1 w2 : 𝕎·}
            → SUC t ⇓ v from w1 to w2
            → isValue v
            → Σ ℕ (λ k → t ⇓ NUM k from w1 to w2 × v ≡ NUM (suc k))
SUC⇓val→ {t} {v} {w1} {w2} (n , comp) isv =
  fst h , (n , fst (snd h)) , snd (snd h)
  where
    h : Σ ℕ (λ k → steps n (t , w1) ≡ (NUM k , w2) × v ≡ NUM (suc k))
    h = SUC⇓val→steps {n} {t} {v} {w1} {w2} comp isv



probeM⇓-decomp : (name : Name) (F f v : Term) (w w' : 𝕎·)
                 → probeM name F f ⇓ v from w to w'
                 → isValue v
                 → ∀𝕎-get0-NUM w name
                 → Σ Term (λ u → Σ ℕ (λ k →
                     appUpd name F f ⇓ u from w to w'
                     × isValue u
                     × get0 name ⇓ NUM k from w' to w'
                     × getT 0 name w' ≡ just (NUM k)
                     × v ≡ NUM (suc k)))
probeM⇓-decomp name F f v w w' comp isv g0 =
  u , j , comp1' , isv1 , comp2' , g3 , eqvj
  where
    z : Σ 𝕎· (λ w1 → Σ Term (λ u →
          appUpd name F f ⇓ u from w to w1
          × isValue u
          × SUC (get0 name) ⇓ v from w1 to w'))
    z = SEQ⇓-decomp (appUpd name F f) (SUC (get0 name)) v w w' comp isv

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

    comp2 : SUC (get0 name) ⇓ v from w1 to w'
    comp2 = snd (snd (snd (snd z)))

    comp2b : Σ ℕ (λ j → get0 name ⇓ NUM j from w1 to w' × v ≡ NUM (suc j))
    comp2b = SUC⇓val→ comp2 isv

    j : ℕ
    j = fst comp2b

    comp2c : get0 name ⇓ NUM j from w1 to w'
    comp2c = fst (snd comp2b)

    eqvj : v ≡ NUM (suc j)
    eqvj = snd (snd comp2b)

    g2 : Σ ℕ (λ k → getT 0 name w1 ≡ just (NUM k))
    g2 = lower (g0 w1 e1)

    k : ℕ
    k = fst g2

    g1 : steps 1 (get0 name , w1) ≡ (NUM k , w1)
    g1 rewrite snd g2 = refl

    comp3 : get0 name ⇓ NUM k from w1 to w1
    comp3 = 1 , g1

    eqw : w1 ≡ w'
    eqw = snd (⇓-from-to→≡𝕎 tt tt comp3 comp2c)

    eqj : j ≡ k
    eqj = NUMinj (fst (⇓-from-to→≡𝕎 tt tt comp2c comp3))

    comp1' : appUpd name F f ⇓ u from w to w'
    comp1' = ⇓-from-to≡wᵣ eqw comp1

    comp2' : get0 name ⇓ NUM j from w' to w'
    comp2' = ⇓-from-to≡wₗ eqw comp2c

    g3 : getT 0 name w' ≡ just (NUM j)
    g3 = begin
           getT 0 name w'
         ≡⟨ cong (getT 0 name) (sym eqw) ⟩
           getT 0 name w1
         ≡⟨ snd g2 ⟩
           just (NUM k)
         ≡⟨ cong (λ x → just (NUM x)) (sym eqj) ⟩
           just (NUM j)
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



#νtestM⇓→ : (cn : comp→∀ℕ) {w1 w2 : 𝕎·} {F f : Term} {n : ℕ}
             → # F
             → # f
             → ¬Names F
             → ¬Names f
             → νtestM F f ⇓ NUM n from w1 to w2
             → Σ Name (λ name → Σ Term (λ v → Σ ℕ (λ k →
                 APPLY F (upd name f) ⇓ v from (chooseT name (startNewChoiceT Res⊤ w1 (testM 0 F f)) (NUM 0)) to w2
                 × isValue v
                 × getT 0 name w2 ≡ just (NUM k)
                 × n ≡ suc k
                 × compatible· name (startNewChoiceT Res⊤ w1 (testM 0 F f)) Res⊤)))
#νtestM⇓→ cn {w1} {w2} {F} {f} {n} cF cf nnF nnf comp =
  newChoiceT w1 (testM 0 F f) ,
  fst comp3 ,
  fst (snd comp3) ,
  fst (snd (snd comp3)) ,
  fst (snd (snd (snd comp3))) ,
  fst (snd (snd (snd (snd (snd comp3))))) ,
  NUMinj (snd (snd (snd (snd (snd (snd comp3)))))) ,
  compat1
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

    comp3 : Σ Term (λ u → Σ ℕ (λ k →
               appUpd name F f ⇓ u from w1'' to w2
               × isValue u
               × get0 name ⇓ NUM k from w2 to w2
               × getT 0 name w2 ≡ just (NUM k)
               × NUM n ≡ NUM (suc k)))
    comp3 = probeM⇓-decomp name F f (NUM n) w1'' w2 comp2 tt (cn name w1' 0 compat1)



data updCtxt (name : Name) (f : Term) : Term → Set where
  updCtxt-VAR     : (x : Var) → updCtxt name f (VAR x)
--  updCtxt-NAT     : updCtxt name f NAT
  updCtxt-QNAT    : updCtxt name f QNAT
--  updCtxt-TNAT    : updCtxt name f TNAT
  updCtxt-LT      : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (LT a b)
  updCtxt-QLT     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (QLT a b)
  updCtxt-NUM     : (x : ℕ) → updCtxt name f (NUM x)
  updCtxt-IFLT    : (a b c d : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f d → updCtxt name f (IFLT a b c d)
  updCtxt-IFEQ    : (a b c d : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f d → updCtxt name f (IFEQ a b c d)
  updCtxt-SUC     : (a : Term) → updCtxt name f a → updCtxt name f (SUC a)
  updCtxt-NATREC  : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (NATREC a b c)
  updCtxt-PI      : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (PI a b)
  updCtxt-LAMBDA  : (a : Term) → updCtxt name f a → updCtxt name f (LAMBDA a)
  updCtxt-APPLY   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (APPLY a b)
  updCtxt-FIX     : (a : Term) → updCtxt name f a → updCtxt name f (FIX a)
  updCtxt-LET     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (LET a b)
  updCtxt-WT      : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (WT a b c)
  updCtxt-SUP     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SUP a b)
--  updCtxt-DSUP    : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (DSUP a b)
  updCtxt-WREC    : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (WREC a b)
  updCtxt-MT      : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (MT a b c)
--  updCtxt-MSUP    : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (MSUP a b)
--  updCtxt-DMSUP   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (DMSUP a b)
  updCtxt-SUM     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SUM a b)
  updCtxt-PAIR    : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (PAIR a b)
  updCtxt-SPREAD  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SPREAD a b)
  updCtxt-SET     : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (SET a b)
  updCtxt-ISECT   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (ISECT a b)
  updCtxt-TUNION  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (TUNION a b)
  updCtxt-UNION   : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (UNION a b)
--  updCtxt-QTUNION : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (QTUNION a b)
  updCtxt-INL     : (a : Term) → updCtxt name f a → updCtxt name f (INL a)
  updCtxt-INR     : (a : Term) → updCtxt name f a → updCtxt name f (INR a)
  updCtxt-DECIDE  : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (DECIDE a b c)
  updCtxt-EQ      : (a b c : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f (EQ a b c)
--  updCtxt-EQB     : (a b c d : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f c → updCtxt name f d → updCtxt name f (EQB a b c d)
  updCtxt-AX      : updCtxt name f AX
  updCtxt-FREE    : updCtxt name f FREE
  updCtxt-MSEQ    : (x : 𝕊) → updCtxt name f (MSEQ x)
  updCtxt-MAPP    : (s : 𝕊) (a : Term) → updCtxt name f a → updCtxt name f (MAPP s a)
  --updCtxt-CS      : updCtxt name1 name2 f (CS name1) (CS name2)
  --updCtxt-CS      : updCtxt name1 name2 f (CS name1) (CS name2)
  --updCtxt-NAME    : updCtxt name1 name2 f (NAME name1) (NAME name2)
  --updCtxt-FRESH   : (a b : Term) → updCtxt name1 name2 f a b → updCtxt name1 name2 f (FRESH a) (FRESH b)
  updCtxt-CHOOSE  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (CHOOSE a b)
--  updCtxt-IFC0    : (a₁ a₂ b₁ b₂ c₁ c₂ : Term) → updCtxt name1 name2 f a₁ a₂ → updCtxt name1 name2 f b₁ b₂ → updCtxt name1 name2 f c₁ c₂ → updCtxt name1 name2 f (IFC0 a₁ b₁ c₁) (IFC0 a₂ b₂ c₂)
--  updCtxt-TSQUASH : (a : Term) → updCtxt name f a → updCtxt name f (TSQUASH a)
--  updCtxt-TTRUNC  : (a : Term) → updCtxt name f a → updCtxt name f (TTRUNC a)
  updCtxt-NOWRITE : updCtxt name f NOWRITE
  updCtxt-NOREAD  : updCtxt name f NOREAD
  updCtxt-SUBSING : (a : Term) → updCtxt name f a → updCtxt name f (SUBSING a)
  updCtxt-PURE    : updCtxt name f PURE
  updCtxt-NOSEQ   : updCtxt name f NOSEQ
  updCtxt-NOENC   : updCtxt name f NOENC
  updCtxt-TERM    : (a : Term) → updCtxt name f a → updCtxt name f (TERM a)
  updCtxt-ENC     : (a : Term) → updCtxt name f a → updCtxt name f (ENC a)
  updCtxt-PARTIAL : (a : Term) → updCtxt name f a → updCtxt name f (PARTIAL a)
  updCtxt-FFDEFS  : (a b : Term) → updCtxt name f a → updCtxt name f b → updCtxt name f (FFDEFS a b)
  updCtxt-UNIV    : (x : ℕ) → updCtxt name f (UNIV x)
  updCtxt-LIFT    : (a : Term) → updCtxt name f a → updCtxt name f (LIFT a)
  updCtxt-LOWER   : (a : Term) → updCtxt name f a → updCtxt name f (LOWER a)
  updCtxt-SHRINK  : (a : Term) → updCtxt name f a → updCtxt name f (SHRINK a)
  updCtxt-upd     : updCtxt name f (upd name f)



abstract

  updCtxt→differ : {name : Name} {f t : Term}
                    → updCtxt name f t
                    → differ name name f t t
  updCtxt→differ {name} {f} {.(VAR x)} (updCtxt-VAR x) = differ-VAR _
--  updCtxt→differ {name} {f} {.NAT} updCtxt-NAT = differ-NAT
  updCtxt→differ {name} {f} {.QNAT} updCtxt-QNAT = differ-QNAT
--  updCtxt→differ {name} {f} {.TNAT} updCtxt-TNAT = differ-TNAT
  updCtxt→differ {name} {f} {.(LT a b)} (updCtxt-LT a b u u₁) = differ-LT _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(QLT a b)} (updCtxt-QLT a b u u₁) = differ-QLT _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(NUM x)} (updCtxt-NUM x) = differ-NUM _
  updCtxt→differ {name} {f} {.(IFLT a b c d)} (updCtxt-IFLT a b c d u u₁ u₂ u₃) = differ-IFLT _ _ _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂) (updCtxt→differ u₃)
  updCtxt→differ {name} {f} {.(IFEQ a b c d)} (updCtxt-IFEQ a b c d u u₁ u₂ u₃) = differ-IFEQ _ _ _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂) (updCtxt→differ u₃)
  updCtxt→differ {name} {f} {.(SUC a)} (updCtxt-SUC a u) = differ-SUC _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(NATREC a b c)} (updCtxt-NATREC a b c u u₁ u₂) = differ-NATREC _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂)
  updCtxt→differ {name} {f} {.(PI a b)} (updCtxt-PI a b u u₁) = differ-PI _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(LAMBDA a)} (updCtxt-LAMBDA a u) = differ-LAMBDA _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(APPLY a b)} (updCtxt-APPLY a b u u₁) = differ-APPLY _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(FIX a)} (updCtxt-FIX a u) = differ-FIX _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(LET a b)} (updCtxt-LET a b u u₁) = differ-LET _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(WT a b c)} (updCtxt-WT a b c u u₁ u₂) = differ-WT _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂)
  updCtxt→differ {name} {f} {.(SUP a b)} (updCtxt-SUP a b u u₁) = differ-SUP _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  --updCtxt→differ {name} {f} {.(DSUP a b)} (updCtxt-DSUP a b u u₁) = differ-DSUP _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(WREC a b)} (updCtxt-WREC a b u u₁) = differ-WREC _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(MT a b c)} (updCtxt-MT a b c u u₁ u₂) = differ-MT _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂)
  --updCtxt→differ {name} {f} {.(MSUP a b)} (updCtxt-MSUP a b u u₁) = differ-MSUP _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  --updCtxt→differ {name} {f} {.(DMSUP a b)} (updCtxt-DMSUP a b u u₁) = differ-DMSUP _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(SUM a b)} (updCtxt-SUM a b u u₁) = differ-SUM _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(PAIR a b)} (updCtxt-PAIR a b u u₁) = differ-PAIR _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(SPREAD a b)} (updCtxt-SPREAD a b u u₁) = differ-SPREAD _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(SET a b)} (updCtxt-SET a b u u₁) = differ-SET _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(ISECT a b)} (updCtxt-ISECT a b u u₁) = differ-ISECT _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(TUNION a b)} (updCtxt-TUNION a b u u₁) = differ-TUNION _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(UNION a b)} (updCtxt-UNION a b u u₁) = differ-UNION _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
--  updCtxt→differ {name} {f} {.(QTUNION a b)} (updCtxt-QTUNION a b u u₁) = differ-QTUNION _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(INL a)} (updCtxt-INL a u) = differ-INL _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(INR a)} (updCtxt-INR a u) = differ-INR _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(DECIDE a b c)} (updCtxt-DECIDE a b c u u₁ u₂) = differ-DECIDE _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂)
  updCtxt→differ {name} {f} {.(EQ a b c)} (updCtxt-EQ a b c u u₁ u₂) = differ-EQ _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂)
--  updCtxt→differ {name} {f} {.(EQB a b c d)} (updCtxt-EQB a b c d u u₁ u₂ u₃) = differ-EQB _ _ _ _ _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁) (updCtxt→differ u₂) (updCtxt→differ u₃)
  updCtxt→differ {name} {f} {.AX} updCtxt-AX = differ-AX
  updCtxt→differ {name} {f} {.FREE} updCtxt-FREE = differ-FREE
  updCtxt→differ {name} {f} {.(MSEQ x)} (updCtxt-MSEQ x) = differ-MSEQ x
  updCtxt→differ {name} {f} {.(MAPP s a)} (updCtxt-MAPP s a u) = differ-MAPP _ _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(CHOOSE a b)} (updCtxt-CHOOSE a b u u₁) = differ-CHOOSE _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
--  updCtxt→differ {name} {f} {.(TSQUASH a)} (updCtxt-TSQUASH a u) = differ-TSQUASH _ _ (updCtxt→differ u)
--  updCtxt→differ {name} {f} {.(TTRUNC a)} (updCtxt-TTRUNC a u) = differ-TTRUNC _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.NOWRITE} updCtxt-NOWRITE = differ-NOWRITE
  updCtxt→differ {name} {f} {.NOREAD}  updCtxt-NOREAD  = differ-NOREAD
  updCtxt→differ {name} {f} {.(SUBSING a)} (updCtxt-SUBSING a u) = differ-SUBSING _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(PURE)} (updCtxt-PURE) = differ-PURE
  updCtxt→differ {name} {f} {.(NOSEQ)} (updCtxt-NOSEQ) = differ-NOSEQ
  updCtxt→differ {name} {f} {.(NOENC)} (updCtxt-NOENC) = differ-NOENC
  updCtxt→differ {name} {f} {.(TERM a)} (updCtxt-TERM a u) = differ-TERM _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(ENC a)} (updCtxt-ENC a u) = differ-ENC _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(PARTIAL a)} (updCtxt-PARTIAL a u) = differ-PARTIAL _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(FFDEFS a b)} (updCtxt-FFDEFS a b u u₁) = differ-FFDEFS _ _ _ _ (updCtxt→differ u) (updCtxt→differ u₁)
  updCtxt→differ {name} {f} {.(UNIV x)} (updCtxt-UNIV x) = differ-UNIV x
  updCtxt→differ {name} {f} {.(LIFT a)} (updCtxt-LIFT a u) = differ-LIFT _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(LOWER a)} (updCtxt-LOWER a u) = differ-LOWER _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(SHRINK a)} (updCtxt-SHRINK a u) = differ-SHRINK _ _ (updCtxt→differ u)
  updCtxt→differ {name} {f} {.(upd name f)} updCtxt-upd = differ-upd



abstract

  differ→updCtxt : {name : Name} {f t : Term}
                    → differ name name f t t
                    → updCtxt name f t
  differ→updCtxt {name} {f} {.(VAR x)} (differ-VAR x) = updCtxt-VAR _
--  differ→updCtxt {name} {f} {.NAT} differ-NAT = updCtxt-NAT
  differ→updCtxt {name} {f} {.QNAT} differ-QNAT = updCtxt-QNAT
--  differ→updCtxt {name} {f} {.TNAT} differ-TNAT = updCtxt-TNAT
  differ→updCtxt {name} {f} {.(LT a₁ b₁)} (differ-LT a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-LT _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(QLT a₁ b₁)} (differ-QLT a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-QLT _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(NUM x)} (differ-NUM x) = updCtxt-NUM _
  differ→updCtxt {name} {f} {.(IFLT a₁ b₁ c₁ d₁)} (differ-IFLT a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ d d₂ d₃ d₄) = updCtxt-IFLT _ _ _ _ (differ→updCtxt d) (differ→updCtxt d₂) (differ→updCtxt d₃) (differ→updCtxt d₄)
  differ→updCtxt {name} {f} {.(IFEQ a₁ b₁ c₁ d₁)} (differ-IFEQ a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ d d₂ d₃ d₄) = updCtxt-IFEQ _ _ _ _ (differ→updCtxt d) (differ→updCtxt d₂) (differ→updCtxt d₃) (differ→updCtxt d₄)
  differ→updCtxt {name} {f} {.(SUC a)} (differ-SUC a .a d) = updCtxt-SUC _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(NATREC a b c)} (differ-NATREC a .a b .b c .c d d₁ d₂) = updCtxt-NATREC _ _ _ (differ→updCtxt d) (differ→updCtxt d₁) (differ→updCtxt d₂)
  differ→updCtxt {name} {f} {.(PI a₁ b₁)} (differ-PI a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-PI _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(LAMBDA a)} (differ-LAMBDA a .a d) = updCtxt-LAMBDA _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(APPLY a₁ b₁)} (differ-APPLY a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-APPLY _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(FIX a)} (differ-FIX a .a d) = updCtxt-FIX _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(LET a₁ b₁)} (differ-LET a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-LET _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(WT a₁ b₁ c₁)} (differ-WT a₁ .a₁ b₁ .b₁ c₁ .c₁ d d₁ d₂) = updCtxt-WT _ _ _ (differ→updCtxt d) (differ→updCtxt d₁) (differ→updCtxt d₂)
  differ→updCtxt {name} {f} {.(SUP a₁ b₁)} (differ-SUP a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-SUP _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  --differ→updCtxt {name} {f} {.(DSUP a₁ b₁)} (differ-DSUP a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-DSUP _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(WREC a₁ b₁)} (differ-WREC a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-WREC _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(MT a₁ b₁ c₁)} (differ-MT a₁ .a₁ b₁ .b₁ c₁ .c₁ d d₁ d₂) = updCtxt-MT _ _ _ (differ→updCtxt d) (differ→updCtxt d₁) (differ→updCtxt d₂)
  --differ→updCtxt {name} {f} {.(MSUP a₁ b₁)} (differ-MSUP a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-MSUP _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  --differ→updCtxt {name} {f} {.(DMSUP a₁ b₁)} (differ-DMSUP a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-DMSUP _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(SUM a₁ b₁)} (differ-SUM a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-SUM _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(PAIR a₁ b₁)} (differ-PAIR a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-PAIR _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(SPREAD a₁ b₁)} (differ-SPREAD a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-SPREAD _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(SET a₁ b₁)} (differ-SET a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-SET _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(ISECT a₁ b₁)} (differ-ISECT a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-ISECT _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(TUNION a₁ b₁)} (differ-TUNION a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-TUNION _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(UNION a₁ b₁)} (differ-UNION a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-UNION _ _ (differ→updCtxt d) (differ→updCtxt d₁)
--  differ→updCtxt {name} {f} {.(QTUNION a₁ b₁)} (differ-QTUNION a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-QTUNION _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(INL a)} (differ-INL a .a d) = updCtxt-INL _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(INR a)} (differ-INR a .a d) = updCtxt-INR _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(DECIDE a₁ b₁ c₁)} (differ-DECIDE a₁ .a₁ b₁ .b₁ c₁ .c₁ d d₁ d₂) = updCtxt-DECIDE _ _ _ (differ→updCtxt d) (differ→updCtxt d₁) (differ→updCtxt d₂)
  differ→updCtxt {name} {f} {.(EQ a₁ b₁ c₁)} (differ-EQ a₁ .a₁ b₁ .b₁ c₁ .c₁ d d₁ d₂) = updCtxt-EQ _ _ _ (differ→updCtxt d) (differ→updCtxt d₁) (differ→updCtxt d₂)
--  differ→updCtxt {name} {f} {.(EQB a₁ b₁ c₁ d₁)} (differ-EQB a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) = updCtxt-EQB _ _ _ _ (differ→updCtxt diff) (differ→updCtxt diff₁) (differ→updCtxt diff₂) (differ→updCtxt diff₃)
  differ→updCtxt {name} {f} {.AX} differ-AX = updCtxt-AX
  differ→updCtxt {name} {f} {.FREE} differ-FREE = updCtxt-FREE
  differ→updCtxt {name} {f} {.(MSEQ x)} (differ-MSEQ x) = updCtxt-MSEQ x
  differ→updCtxt {name} {f} {.(MAPP s a₁)} (differ-MAPP s a₁ .a₁ d) = updCtxt-MAPP _ _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(CHOOSE a₁ b₁)} (differ-CHOOSE a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-CHOOSE _ _ (differ→updCtxt d) (differ→updCtxt d₁)
--  differ→updCtxt {name} {f} {.(TSQUASH a)} (differ-TSQUASH a .a d) = updCtxt-TSQUASH _ (differ→updCtxt d)
--  differ→updCtxt {name} {f} {.(TTRUNC a)} (differ-TTRUNC a .a d) = updCtxt-TTRUNC _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.NOWRITE} differ-NOWRITE = updCtxt-NOWRITE
  differ→updCtxt {name} {f} {.NOREAD}  differ-NOREAD  = updCtxt-NOREAD
  differ→updCtxt {name} {f} {.(SUBSING a)} (differ-SUBSING a .a d) = updCtxt-SUBSING _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(PURE)} (differ-PURE) = updCtxt-PURE
  differ→updCtxt {name} {f} {.(NOSEQ)} (differ-NOSEQ) = updCtxt-NOSEQ
  differ→updCtxt {name} {f} {.(NOENC)} (differ-NOENC) = updCtxt-NOENC
  differ→updCtxt {name} {f} {.(TERM a)} (differ-TERM a .a d) = updCtxt-TERM _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(ENC a)} (differ-ENC a d) = updCtxt-ENC _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(PARTIAL a)} (differ-PARTIAL a .a d) = updCtxt-PARTIAL _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(FFDEFS a₁ b₁)} (differ-FFDEFS a₁ .a₁ b₁ .b₁ d d₁) = updCtxt-FFDEFS _ _ (differ→updCtxt d) (differ→updCtxt d₁)
  differ→updCtxt {name} {f} {.(UNIV x)} (differ-UNIV x) = updCtxt-UNIV _
  differ→updCtxt {name} {f} {.(LIFT a)} (differ-LIFT a .a d) = updCtxt-LIFT _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(LOWER a)} (differ-LOWER a .a d) = updCtxt-LOWER _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(SHRINK a)} (differ-SHRINK a .a d) = updCtxt-SHRINK _ (differ→updCtxt d)
  differ→updCtxt {name} {f} {.(upd name f)} differ-upd = updCtxt-upd



→updCtxt-shiftDown : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                     → updCtxt name f a
                     → updCtxt name f (shiftDown v a)
→updCtxt-shiftDown v {name} {f} cf {a} u = differ→updCtxt (→differ-shiftDown v cf (updCtxt→differ u))



→updCtxt-shiftUp : (v : Var) {name : Name} {f : Term} (cf : # f) {a : Term}
                     → updCtxt name f a
                     → updCtxt name f (shiftUp v a)
→updCtxt-shiftUp v {name} {f} cf {a} u = differ→updCtxt (→differ-shiftUp v cf (updCtxt→differ u))



→updCtxt-subv : (v : Var) {name : Name} {f : Term} (cf : # f) {a b : Term}
                 → updCtxt name f a
                 → updCtxt name f b
                 → updCtxt name f (subv v b a)
→updCtxt-subv v {name} {f} cf {a} {b} ua ub = differ→updCtxt (differ-subv cf v (updCtxt→differ ua) (updCtxt→differ ub))



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


updCtxt-PAIR→ : {name : Name} {f a b : Term}
                   → updCtxt name f (PAIR a b)
                   → updCtxt name f a × updCtxt name f b
updCtxt-PAIR→ {name} {f} {a} {b} (updCtxt-PAIR .a .b u v) = u , v


updCtxt-SUP→ : {name : Name} {f a b : Term}
                   → updCtxt name f (SUP a b)
                   → updCtxt name f a × updCtxt name f b
updCtxt-SUP→ {name} {f} {a} {b} (updCtxt-SUP .a .b u v) = u , v


{--
updCtxt-MSUP→ : {name : Name} {f a b : Term}
                   → updCtxt name f (MSUP a b)
                   → updCtxt name f a × updCtxt name f b
updCtxt-MSUP→ {name} {f} {a} {b} (updCtxt-MSUP .a .b u v) = u , v
--}


updCtxt-INL→ : {name : Name} {f a : Term}
                → updCtxt name f (INL a)
                → updCtxt name f a
updCtxt-INL→ {name} {f} {a} (updCtxt-INL .a u) = u


updCtxt-INR→ : {name : Name} {f a : Term}
                → updCtxt name f (INR a)
                → updCtxt name f a
updCtxt-INR→ {name} {f} {a} (updCtxt-INR .a u) = u


updCtxt-CS→ : {name n : Name} {f : Term}
               → updCtxt name f (CS n)
               → ⊥
updCtxt-CS→ {name} {n} {f} ()


updCtxt-NAME→ : {name n : Name} {f : Term}
               → updCtxt name f (NAME n)
               → ⊥
updCtxt-NAME→ {name} {n} {f} ()


getT≤ℕ : 𝕎· → ℕ → Name → Set
getT≤ℕ w1 n name = Σ ℕ (λ j → getT 0 name w1 ≡ just (NUM j) × j < n)


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



isHighestℕ-IFEQ₁ : {k : ℕ} {a a' : Term} {w w' : 𝕎·} {n : ℕ} {name : Name} (b c d : Term)
                    → (comp : steps k (a , w) ≡ (a' , w'))
                    → isHighestℕ {k} {w} {w'} {a} {a'} n name comp
                    → Σ ℕ (λ k' → Σ (steps k' (IFEQ a b c d , w) ≡ (IFEQ a' b c d , w'))
                         (isHighestℕ {k'} {w} {w'} {IFEQ a b c d} {IFEQ a' b c d} n name))
isHighestℕ-IFEQ₁ {0} {a} {a'} {w} {w'} {n} {name} b c d comp h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) =
  0 , refl , h
isHighestℕ-IFEQ₁ {suc k} {a} {a'} {w} {w'} {n} {name} b c d comp h with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ x rewrite stepVal a w x | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) = ind
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFEQ a b c d , w) ≡ (IFEQ a' b c d , w'))
            (isHighestℕ {k'} {w} {w'} {IFEQ a b c d} {IFEQ a' b c d} n name))
    ind = isHighestℕ-IFEQ₁ {k} {a} {a'} {w} {w'} {n} {name} b c d comp (snd h)
... |    inj₂ x = suc (fst ind) , comp1
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFEQ a1 b c d , w1) ≡ (IFEQ a' b c d , w'))
            (isHighestℕ {k'} {w1} {w'} {IFEQ a1 b c d} {IFEQ a' b c d} n name))
    ind = isHighestℕ-IFEQ₁ {k} {a1} {a'} {w1} {w'} {n} {name} b c d comp (snd h)

    comp1 : Σ (steps (suc (fst ind)) (IFEQ a b c d , w) ≡ (IFEQ a' b c d , w'))
              (isHighestℕ {suc (fst ind)} {w} {w'} {IFEQ a b c d} {IFEQ a' b c d} n name)
    comp1 with is-NUM a
    ... | inj₁ (na , pa) rewrite pa = ⊥-elim (x tt)
    ... | inj₂ pa rewrite z = fst (snd ind) , fst h , snd (snd ind)
isHighestℕ-IFEQ₁ {suc k} {a} {a'} {w} {w'} {n} {name} b c d comp h | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl , h



isHighestℕ-IFEQ₂ : {k : ℕ} {b b' : Term} {w w' : 𝕎·} {n : ℕ} {name : Name} (m : ℕ) (c d : Term)
                    → (comp : steps k (b , w) ≡ (b' , w'))
                    → isHighestℕ {k} {w} {w'} {b} {b'} n name comp
                    → Σ ℕ (λ k' → Σ (steps k' (IFEQ (NUM m) b c d , w) ≡ (IFEQ (NUM m) b' c d , w'))
                         (isHighestℕ {k'} {w} {w'} {IFEQ (NUM m) b c d} {IFEQ (NUM m) b' c d} n name))
isHighestℕ-IFEQ₂ {0} {b} {b'} {w} {w'} {n} {name} m c d comp h
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) =
  0 , refl , h
isHighestℕ-IFEQ₂ {suc k} {b} {b'} {w} {w'} {n} {name} m c d comp h with step⊎ b w
... | inj₁ (b1 , w1 , z) rewrite z with isValue⊎ b
... |    inj₁ x rewrite stepVal b w x | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) = ind
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFEQ (NUM m) b c d , w) ≡ (IFEQ (NUM m) b' c d , w'))
            (λ comp' → isHighestℕ {k'} {w} {w'} {IFEQ (NUM m) b c d} {IFEQ (NUM m) b' c d} n name comp'))
    ind = isHighestℕ-IFEQ₂ {k} {b} {b'} {w} {w'} {n} {name} m c d comp (snd h)
... |    inj₂ x = suc (fst ind) , comp1
  where
    ind : Σ ℕ (λ k' → Σ (steps k' (IFEQ (NUM m) b1 c d , w1) ≡ (IFEQ (NUM m) b' c d , w'))
            (λ comp' → isHighestℕ {k'} {w1} {w'} {IFEQ (NUM m) b1 c d} {IFEQ (NUM m) b' c d} n name comp'))
    ind = isHighestℕ-IFEQ₂ {k} {b1} {b'} {w1} {w'} {n} {name} m c d comp (snd h)

    comp1 : Σ (steps (suc (fst ind)) (IFEQ (NUM m) b c d , w) ≡ (IFEQ (NUM m) b' c d , w'))
              (isHighestℕ {suc (fst ind)} {w} {w'} {IFEQ (NUM m) b c d} {IFEQ (NUM m) b' c d} n name)
    comp1 with is-NUM b
    ... | inj₁ (nb , pb) rewrite pb = ⊥-elim (x tt)
    ... | inj₂ pb rewrite z = fst (snd ind) , fst h , snd (snd ind)
isHighestℕ-IFEQ₂ {suc k} {b} {b'} {w} {w'} {n} {name} m c d comp h | inj₂ z rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = 0 , refl , h


presHighestℕ : (name : Name) (f : Term) (k : ℕ) → Set(lsuc L)
presHighestℕ name f k =
  {w1 w2 : 𝕎·} {a b : Term} {n : ℕ}
  (comp : steps k (a , w1) ≡ (b , w2))
  → isValue b
  → updCtxt name f a
  → compatible· name w1 Res⊤
  → ∀𝕎-get0-NUM w1 name
  → getT≤ℕ w2 n name --getT 0 name w2 ≡ just (NUM n)
  → isHighestℕ {k} {w1} {w2} {a} {b} n name comp


stepsPresHighestℕ : (name : Name) (f : Term) (b : Term) (w : 𝕎·) → Set(lsuc L)
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



stepsPresHighestℕ-IFEQ₁→ : {name : Name} {f : Term} {a b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (IFEQ a b c d) w
                            → stepsPresHighestℕ name f a w
stepsPresHighestℕ-IFEQ₁→ {name} {f} {a} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k a w
    hv = IFEQ→hasValue k a b c d v w w' comp isv



stepsPresHighestℕ-IFEQ₂→ : {name : Name} {f : Term} {n : ℕ} {b c d : Term} {w : 𝕎·}
                            → stepsPresHighestℕ name f (IFEQ (NUM n) b c d) w
                            → stepsPresHighestℕ name f b w
stepsPresHighestℕ-IFEQ₂→ {name} {f} {n} {b} {c} {d} {w} (k , v , w' , comp , isv , ind) =
  k , fst hv , fst (snd hv) , fst (snd (snd hv)) , snd (snd (snd hv)) , ind
  where
    hv : hasValueℕ k b w
    hv = IFEQ-NUM→hasValue k n b c d v w w' comp isv


→step-IFEQ₂ : {w w' : 𝕎·} {n : ℕ} {b b' : Term} (c d : Term)
               → ¬ isValue b
               → step b w ≡ just (b' , w')
               → step (IFEQ (NUM n) b c d) w ≡ just (IFEQ (NUM n) b' c d , w')
→step-IFEQ₂ {w} {w'} {n} {b} {b'} c d nv s with is-NUM b
... | inj₁ (k , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite s = refl



ΣhighestUpdCtxtAux-IFEQ₂-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {b b1 b' : Term} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {c d : Term}
                               → ¬ isValue b
                               → step b w ≡ just (b1 , w1)
                               → (comp : steps k (b1 , w1) ≡ (b' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {b1} {b'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (IFEQ (NUM m) b1 c d) (IFEQ (NUM m) b' c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (IFEQ (NUM m) b c d) (IFEQ (NUM m) b' c d) w0 w w'
ΣhighestUpdCtxtAux-IFEQ₂-aux {j} {k} {w} {w0} {w1} {w'} {b} {b1} {b'} {name} {f} {n} {m} {c} {d} nv comp0 comp i (comp1 , g , u) with is-NUM b
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-IFEQ₂ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b b' c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxtAux k name f n b b' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFEQ (NUM m) b c d) (IFEQ (NUM m) b' c d) w0 w w')
ΣhighestUpdCtxtAux-IFEQ₂ {0} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFEQ _ _ _ _ (updCtxt-NUM m) u uc ud
ΣhighestUpdCtxtAux-IFEQ₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , u) with step⊎ b w
... | inj₁ (b1 , w1 , z) rewrite z with isValue⊎ b
... |    inj₁ y rewrite stepVal b w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-IFEQ₂ {k} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-IFEQ₂-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFEQ (NUM m) b1 c d) (IFEQ (NUM m) b' c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-IFEQ₂ {k} {name} {f} {n} {m} {b1} {b'} {c} {d} {w0} {w1} {w'} uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-IFEQ₂ {suc k} {name} {f} {n} {m} {b} {b'} {c} {d} {w0} {w} {w'} uc ud (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFEQ _ _ _ _ (updCtxt-NUM m) u uc ud



ΣhighestUpdCtxt-IFEQ₂ : {name : Name} {f : Term} {n : ℕ} {m : ℕ} {b c d : Term} {w0 w : 𝕎·}
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxt name f n b w0 w
                        → ΣhighestUpdCtxt name f n (IFEQ (NUM m) b c d) w0 w
ΣhighestUpdCtxt-IFEQ₂ {name} {f} {n} {m} {b} {c} {d} {w0} {w} uc ud (k , b' , w' , wcomp , i , u) =
  fst q , IFEQ (NUM m) b' c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFEQ (NUM m) b c d) (IFEQ (NUM m) b' c d) w0 w w')
    q = ΣhighestUpdCtxtAux-IFEQ₂ {k} uc ud (wcomp , i , u)



ΣhighestUpdCtxtAux-IFEQ₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b c d : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (IFEQ a1 b c d) (IFEQ a' b c d) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (IFEQ a b c d) (IFEQ a' b c d) w0 w w'
ΣhighestUpdCtxtAux-IFEQ₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} {c} {d} nv comp0 comp i (comp1 , g , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-IFEQ₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b c d : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFEQ a b c d) (IFEQ a' b c d) w0 w w')
ΣhighestUpdCtxtAux-IFEQ₁ {0} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFEQ _ _ _ _ u ub uc ud
ΣhighestUpdCtxtAux-IFEQ₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-IFEQ₁ {k} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-IFEQ₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFEQ a1 b c d) (IFEQ a' b c d) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-IFEQ₁ {k} {name} {f} {n} {a1} {a'} {b} {c} {d} {w0} {w1} {w'} ub uc ud (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-IFEQ₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {d} {w0} {w} {w'} ub uc ud (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-IFEQ _ _ _ _ u ub uc ud



ΣhighestUpdCtxt-IFEQ₁ : {name : Name} {f : Term} {n : ℕ} {a b c d : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → updCtxt name f d
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (IFEQ a b c d) w0 w
ΣhighestUpdCtxt-IFEQ₁ {name} {f} {n} {a} {b} {c} {d} {w0} {w} ub uc ud (k , a' , w' , wcomp , i , u) =
  fst q , IFEQ a' b c d , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (IFEQ a b c d) (IFEQ a' b c d) w0 w w')
    q = ΣhighestUpdCtxtAux-IFEQ₁ {k} ub uc ud (wcomp , i , u)



ΣhighestUpdCtxtAux-APPLY₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (APPLY a1 b) (APPLY a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (APPLY a b) (APPLY a' b) w0 w w'
ΣhighestUpdCtxtAux-APPLY₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv comp0 comp i (comp1 , g , u) with is-LAM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p with is-CS a
... |    inj₁ (y , q) rewrite q = ⊥-elim (nv tt)
... |    inj₂ q with is-MSEQ a
... |       inj₁ (sq , r) rewrite r = ⊥-elim (nv tt)
... |       inj₂ r rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-APPLY₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (APPLY a b) (APPLY a' b) w0 w w')
ΣhighestUpdCtxtAux-APPLY₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-APPLY _ _ u ub
ΣhighestUpdCtxtAux-APPLY₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-APPLY₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-APPLY₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (APPLY a1 b) (APPLY a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-APPLY₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-APPLY₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-APPLY _ _ u ub



ΣhighestUpdCtxt-APPLY₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (APPLY a b) w0 w
ΣhighestUpdCtxt-APPLY₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , u) =
  fst q , APPLY a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (APPLY a b) (APPLY a' b) w0 w w')
    q = ΣhighestUpdCtxtAux-APPLY₁ {k} ub (wcomp , i , u)



ΣhighestUpdCtxtAux-MAPP₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {s : 𝕊}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (MAPP s a1) (MAPP s a') w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (MAPP s a) (MAPP s a') w0 w w'
ΣhighestUpdCtxtAux-MAPP₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {s} nv comp0 comp i (comp1 , g , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u


ΣhighestUpdCtxtAux-MAPP₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' : Term} {s : 𝕊} {w0 w w' : 𝕎·}
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (MAPP s a) (MAPP s a') w0 w w')
ΣhighestUpdCtxtAux-MAPP₁ {0} {name} {f} {n} {a} {a'} {s} {w0} {w} {w'} (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-MAPP _ _ u
ΣhighestUpdCtxtAux-MAPP₁ {suc k} {name} {f} {n} {a} {a'} {s} {w0} {w} {w'} (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-MAPP₁ {k} (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-MAPP₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (MAPP s a1) (MAPP s a') w0 w1 w')
    ind = ΣhighestUpdCtxtAux-MAPP₁ {k} {name} {f} {n} {a1} {a'} {s} {w0} {w1} {w'} (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-MAPP₁ {suc k} {name} {f} {n} {a} {a'} {s} {w0} {w} {w'} (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-MAPP _ _ u



ΣhighestUpdCtxt-MAPP₁ : {name : Name} {f : Term} {n : ℕ} {a : Term} {s : 𝕊} {w0 w : 𝕎·}
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (MAPP s a) w0 w
ΣhighestUpdCtxt-MAPP₁ {name} {f} {n} {a} {s} {w0} {w} (k , a' , w' , wcomp , i , u) =
  fst q , MAPP s a' , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (MAPP s a) (MAPP s a') w0 w w')
    q = ΣhighestUpdCtxtAux-MAPP₁ {k} (wcomp , i , u)



ΣhighestUpdCtxtAux-LET₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (LET a1 b) (LET a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (LET a b) (LET a' b) w0 w w'
ΣhighestUpdCtxtAux-LET₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv comp0 comp i (comp1 , g , u) with isValue⊎ a
... | inj₁ x = ⊥-elim (nv x)
... | inj₂ x rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-LET₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (LET a b) (LET a' b) w0 w w')
ΣhighestUpdCtxtAux-LET₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-LET _ _ u ub
ΣhighestUpdCtxtAux-LET₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-LET₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-LET₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (LET a1 b) (LET a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-LET₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-LET₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-LET _ _ u ub



ΣhighestUpdCtxt-LET₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (LET a b) w0 w
ΣhighestUpdCtxt-LET₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , u) =
  fst q , LET a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (LET a b) (LET a' b) w0 w w')
    q = ΣhighestUpdCtxtAux-LET₁ {k} ub (wcomp , i , u)



ΣhighestUpdCtxtAux-FIX₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (FIX a1) (FIX a') w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (FIX a) (FIX a') w0 w w'
ΣhighestUpdCtxtAux-FIX₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} nv comp0 comp i (comp1 , g , u) with is-LAM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-FIX₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' : Term} {w0 w w' : 𝕎·}
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (FIX a) (FIX a') w0 w w')
ΣhighestUpdCtxtAux-FIX₁ {0} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-FIX _ u
ΣhighestUpdCtxtAux-FIX₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-FIX₁ {k} (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-FIX₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (FIX a1) (FIX a') w0 w1 w')
    ind = ΣhighestUpdCtxtAux-FIX₁ {k} {name} {f} {n} {a1} {a'} {w0} {w1} {w'} (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-FIX₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-FIX _ u



ΣhighestUpdCtxt-FIX₁ : {name : Name} {f : Term} {n : ℕ} {a : Term} {w0 w : 𝕎·}
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (FIX a) w0 w
ΣhighestUpdCtxt-FIX₁ {name} {f} {n} {a} {w0} {w} (k , a' , w' , wcomp , i , u) =
  fst q , FIX a' , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (FIX a) (FIX a') w0 w w')
    q = ΣhighestUpdCtxtAux-FIX₁ {k} (wcomp , i , u)



ΣhighestUpdCtxtAux-SUC₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (SUC a1) (SUC a') w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (SUC a) (SUC a') w0 w w'
ΣhighestUpdCtxtAux-SUC₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} nv comp0 comp i (comp1 , g , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-SUC₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' : Term} {w0 w w' : 𝕎·}
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (SUC a) (SUC a') w0 w w')
ΣhighestUpdCtxtAux-SUC₁ {0} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-SUC _ u
ΣhighestUpdCtxtAux-SUC₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-SUC₁ {k} (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-SUC₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (SUC a1) (SUC a') w0 w1 w')
    ind = ΣhighestUpdCtxtAux-SUC₁ {k} {name} {f} {n} {a1} {a'} {w0} {w1} {w'} (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-SUC₁ {suc k} {name} {f} {n} {a} {a'} {w0} {w} {w'} (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-SUC _ u



ΣhighestUpdCtxt-SUC₁ : {name : Name} {f : Term} {n : ℕ} {a : Term} {w0 w : 𝕎·}
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (SUC a) w0 w
ΣhighestUpdCtxt-SUC₁ {name} {f} {n} {a} {w0} {w} (k , a' , w' , wcomp , i , u) =
  fst q , SUC a' , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (SUC a) (SUC a') w0 w w')
    q = ΣhighestUpdCtxtAux-SUC₁ {k} (wcomp , i , u)



ΣhighestUpdCtxtAux-NATREC₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a b c a1 a' : Term} {name : Name} {f : Term} {n : ℕ}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (NATREC a1 b c) (NATREC a' b c) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (NATREC a b c) (NATREC a' b c) w0 w w'
ΣhighestUpdCtxtAux-NATREC₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {b} {c} {a1} {a'} {name} {f} {n} nv comp0 comp i (comp1 , g , u) with is-NUM a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-NATREC₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a b c a' : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (NATREC a b c) (NATREC a' b c) w0 w w')
ΣhighestUpdCtxtAux-NATREC₁ {0} {name} {f} {n} {a} {b} {c} {a'} {w0} {w} {w'} ub uc (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-NATREC _ _ _ u ub uc
ΣhighestUpdCtxtAux-NATREC₁ {suc k} {name} {f} {n} {a} {b} {c} {a'} {w0} {w} {w'} ub uc (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-NATREC₁ {k} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-NATREC₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (NATREC a1 b c) (NATREC a' b c) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-NATREC₁ {k} {name} {f} {n} {a1} {b} {c} {a'} {w0} {w1} {w'} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-NATREC₁ {suc k} {name} {f} {n} {a} {b} {c} {a'} {w0} {w} {w'} ub uc (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-NATREC _ _ _ u ub uc



ΣhighestUpdCtxt-NATREC₁ : {name : Name} {f : Term} {n : ℕ} {a b c : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (NATREC a b c) w0 w
ΣhighestUpdCtxt-NATREC₁ {name} {f} {n} {a} {b} {c} {w0} {w} ub uc (k , a' , w' , wcomp , i , u) =
  fst q , NATREC a' b c , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (NATREC a b c) (NATREC a' b c) w0 w w')
    q = ΣhighestUpdCtxtAux-NATREC₁ {k} ub uc (wcomp , i , u)


{--
ΣhighestUpdCtxtAux-DSUP₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (DSUP a1 b) (DSUP a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (DSUP a b) (DSUP a' b) w0 w w'
ΣhighestUpdCtxtAux-DSUP₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv comp0 comp i (comp1 , g , u) with is-SUP a
... | inj₁ (x , y , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-DSUP₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DSUP a b) (DSUP a' b) w0 w w')
ΣhighestUpdCtxtAux-DSUP₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-DSUP _ _ u ub
ΣhighestUpdCtxtAux-DSUP₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-DSUP₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-DSUP₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DSUP a1 b) (DSUP a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-DSUP₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-DSUP₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-DSUP _ _ u ub



ΣhighestUpdCtxt-DSUP₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (DSUP a b) w0 w
ΣhighestUpdCtxt-DSUP₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , u) =
  fst q , DSUP a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DSUP a b) (DSUP a' b) w0 w w')
    q = ΣhighestUpdCtxtAux-DSUP₁ {k} ub (wcomp , i , u)
--}


ΣhighestUpdCtxtAux-WREC₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (WREC a1 b) (WREC a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (WREC a b) (WREC a' b) w0 w w'
ΣhighestUpdCtxtAux-WREC₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv comp0 comp i (comp1 , g , u) with is-SUP a
... | inj₁ (x , y , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-WREC₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (WREC a b) (WREC a' b) w0 w w')
ΣhighestUpdCtxtAux-WREC₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-WREC _ _ u ub
ΣhighestUpdCtxtAux-WREC₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-WREC₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-WREC₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (WREC a1 b) (WREC a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-WREC₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-WREC₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-WREC _ _ u ub



ΣhighestUpdCtxt-WREC₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (WREC a b) w0 w
ΣhighestUpdCtxt-WREC₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , u) =
  fst q , WREC a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (WREC a b) (WREC a' b) w0 w w')
    q = ΣhighestUpdCtxtAux-WREC₁ {k} ub (wcomp , i , u)



{--
ΣhighestUpdCtxtAux-DMSUP₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (DMSUP a1 b) (DMSUP a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (DMSUP a b) (DMSUP a' b) w0 w w'
ΣhighestUpdCtxtAux-DMSUP₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv comp0 comp i (comp1 , g , u) with is-MSUP a
... | inj₁ (x , y , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-DMSUP₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DMSUP a b) (DMSUP a' b) w0 w w')
ΣhighestUpdCtxtAux-DMSUP₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-DMSUP _ _ u ub
ΣhighestUpdCtxtAux-DMSUP₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-DMSUP₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-DMSUP₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DMSUP a1 b) (DMSUP a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-DMSUP₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-DMSUP₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-DMSUP _ _ u ub



ΣhighestUpdCtxt-DMSUP₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (DMSUP a b) w0 w
ΣhighestUpdCtxt-DMSUP₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , u) =
  fst q , DMSUP a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DMSUP a b) (DMSUP a' b) w0 w w')
    q = ΣhighestUpdCtxtAux-DMSUP₁ {k} ub (wcomp , i , u)
--}


ΣhighestUpdCtxtAux-SPREAD₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (SPREAD a1 b) (SPREAD a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (SPREAD a b) (SPREAD a' b) w0 w w'
ΣhighestUpdCtxtAux-SPREAD₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv comp0 comp i (comp1 , g , u) with is-PAIR a
... | inj₁ (x , y , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-SPREAD₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (SPREAD a b) (SPREAD a' b) w0 w w')
ΣhighestUpdCtxtAux-SPREAD₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-SPREAD _ _ u ub
ΣhighestUpdCtxtAux-SPREAD₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-SPREAD₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-SPREAD₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (SPREAD a1 b) (SPREAD a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-SPREAD₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-SPREAD₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-SPREAD _ _ u ub



ΣhighestUpdCtxt-SPREAD₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (SPREAD a b) w0 w
ΣhighestUpdCtxt-SPREAD₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , u) =
  fst q , SPREAD a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (SPREAD a b) (SPREAD a' b) w0 w w')
    q = ΣhighestUpdCtxtAux-SPREAD₁ {k} ub (wcomp , i , u)




ΣhighestUpdCtxtAux-DECIDE₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b c : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (DECIDE a1 b c) (DECIDE a' b c) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (DECIDE a b c) (DECIDE a' b c) w0 w w'
ΣhighestUpdCtxtAux-DECIDE₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} {c} nv comp0 comp i (comp1 , g , u) with is-INL a
... | inj₁ (x , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ p with is-INR a
... |    inj₁ (y , q) rewrite q = ⊥-elim (nv tt)
... |    inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-DECIDE₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b c : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DECIDE a b c) (DECIDE a' b c) w0 w w')
ΣhighestUpdCtxtAux-DECIDE₁ {0} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-DECIDE _ _ _ u ub uc
ΣhighestUpdCtxtAux-DECIDE₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-DECIDE₁ {k} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-DECIDE₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DECIDE a1 b c) (DECIDE a' b c) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-DECIDE₁ {k} {name} {f} {n} {a1} {a'} {b} {c} {w0} {w1} {w'} ub uc (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-DECIDE₁ {suc k} {name} {f} {n} {a} {a'} {b} {c} {w0} {w} {w'} ub uc (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-DECIDE _ _ _ u ub uc



ΣhighestUpdCtxt-DECIDE₁ : {name : Name} {f : Term} {n : ℕ} {a b c : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → updCtxt name f c
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (DECIDE a b c) w0 w
ΣhighestUpdCtxt-DECIDE₁ {name} {f} {n} {a} {b} {c} {w0} {w} ub uc (k , a' , w' , wcomp , i , u) =
  fst q , DECIDE a' b c , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (DECIDE a b c) (DECIDE a' b c) w0 w w')
    q = ΣhighestUpdCtxtAux-DECIDE₁ {k} ub uc (wcomp , i , u)



ΣhighestUpdCtxtAux-CHOOSE₁-aux : {j : ℕ} {k : ℕ} {w w0 w1 w' : 𝕎·} {a a1 a' : Term} {name : Name} {f : Term} {n : ℕ} {b : Term}
                               → ¬ isValue a
                               → step a w ≡ just (a1 , w1)
                               → (comp : steps k (a1 , w1) ≡ (a' , w'))
                               → (getT≤ℕ w' n name → (getT≤ℕ w0 n name × getT≤ℕ w n name × isHighestℕ {k} {w1} {w'} {a1} {a'} n name comp))
                               → ΣhighestUpdCtxtAux j name f n (CHOOSE a1 b) (CHOOSE a' b) w0 w1 w'
                               → ΣhighestUpdCtxtAux (suc j) name f n (CHOOSE a b) (CHOOSE a' b) w0 w w'
ΣhighestUpdCtxtAux-CHOOSE₁-aux {j} {k} {w} {w0} {w1} {w'} {a} {a1} {a'} {name} {f} {n} {b} nv comp0 comp i (comp1 , g , u) with is-NAME a
... | inj₁ (name' , p) rewrite p = ⊥-elim (nv tt)
... | inj₂ q rewrite comp0 = comp1 , (λ s → fst (g s) , fst (snd (i s)) , snd (g s)) , u



ΣhighestUpdCtxtAux-CHOOSE₁ : {k : ℕ} {name : Name} {f : Term} {n : ℕ} {a a' b : Term} {w0 w w' : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxtAux k name f n a a' w0 w w'
                        → Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (CHOOSE a b) (CHOOSE a' b) w0 w w')
ΣhighestUpdCtxtAux-CHOOSE₁ {0} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u)
  rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-CHOOSE _ _ u ub
ΣhighestUpdCtxtAux-CHOOSE₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) with step⊎ a w
... | inj₁ (a1 , w1 , z) rewrite z with isValue⊎ a
... |    inj₁ y rewrite stepVal a w y | sym (pair-inj₁ (just-inj z)) | sym (pair-inj₂ (just-inj z)) =
  ΣhighestUpdCtxtAux-CHOOSE₁ {k} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
... |    inj₂ y =
  suc (fst ind) , ΣhighestUpdCtxtAux-CHOOSE₁-aux {fst ind} {k} y z comp i (snd ind)
  where
    ind : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (CHOOSE a1 b) (CHOOSE a' b) w0 w1 w')
    ind = ΣhighestUpdCtxtAux-CHOOSE₁ {k} {name} {f} {n} {a1} {a'} {b} {w0} {w1} {w'} ub (comp , (λ s → fst (i s) , snd (snd (i s))) , u)
ΣhighestUpdCtxtAux-CHOOSE₁ {suc k} {name} {f} {n} {a} {a'} {b} {w0} {w} {w'} ub (comp , i , u) | inj₂ z
  rewrite z | sym (pair-inj₁ comp) | sym (pair-inj₂ comp)
  = 0 , refl , i , updCtxt-CHOOSE _ _ u ub



ΣhighestUpdCtxt-CHOOSE₁ : {name : Name} {f : Term} {n : ℕ} {a b : Term} {w0 w : 𝕎·}
                        → updCtxt name f b
                        → ΣhighestUpdCtxt name f n a w0 w
                        → ΣhighestUpdCtxt name f n (CHOOSE a b) w0 w
ΣhighestUpdCtxt-CHOOSE₁ {name} {f} {n} {a} {b} {w0} {w} ub (k , a' , w' , wcomp , i , u) =
  fst q , CHOOSE a' b , w' , snd q
  where
    q : Σ ℕ (λ j → ΣhighestUpdCtxtAux j name f n (CHOOSE a b) (CHOOSE a' b) w0 w w')
    q = ΣhighestUpdCtxtAux-CHOOSE₁ {k} ub (wcomp , i , u)




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


abstract

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

