\begin{code}
{-# OPTIONS --rewriting #-}

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality hiding ([_]) -- using (sym ; subst ; _∎ ; _≡⟨_⟩_)
open ≡-Reasoning
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ; _<_ ; _≤_ ; _≥_ ; _≤?_ ; _<?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Data.Bool using (Bool ; _∧_ ; _∨_)
open import Data.Bool.Properties using ()
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties

open import util
open import name
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import choiceExt
open import newChoice
open import encode


module terms7 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
              (N : NewChoice W C M G)
              (EC : Encode)
       where

open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)

open import computation(W)(C)(M)(G)(E)(N)(EC)
open import terms2(W)(C)(M)(G)(E)(N)(EC)
open import terms3(W)(C)(M)(G)(E)(N)(EC)
open import terms4(W)(C)(M)(G)(E)(N)(EC)
open import terms5(W)(C)(M)(G)(E)(N)(EC)
open import terms6(W)(C)(M)(G)(E)(N)(EC)

open import continuity-conds(W)(C)(M)(G)(E)(N)(EC)


⇓PresDiffNF : (f : Term) (name : Name) (n : ℕ) → Set(lsuc(L))
⇓PresDiffNF f name n =
  (w1 w2 w1' : 𝕎·) (a v : Term)
  → isValue v
  → compatible· name w1 Res⊤
  → compatible· name w1' Res⊤
  → ∀𝕎-get0-NUM w1 name
  → ∀𝕎-get0-NUM w1' name
  → differ name name f a a
  → steps n (a , w1) ≡ (v , w2)
  → Σ 𝕎· (λ w2' → a ⇓ v from w1' to w2' × differ name name f v v)


differNF-LAMBDAₗ→ : {name : Name} {f g : Term}
                  → differ name name f (LAMBDA g) (LAMBDA g)
                  → differ name name f g g
                    ⊎ g ≡ updBody name f
differNF-LAMBDAₗ→ {name} {f} {g} (differ-LAMBDA .g .g d) = inj₁ d
differNF-LAMBDAₗ→ {name} {f} {.(updBody name f)} differ-upd = inj₂ refl


differNF-PAIRₗ→ : {name : Name} {f a b : Term}
                  → differ name name f (PAIR a b) (PAIR a b)
                  → differ name name f a a × differ name name f b b
differNF-PAIRₗ→ {name} {f} {a} {b} (differ-PAIR .a .a .b .b diff diff₁) = diff , diff₁


differNF-SUPₗ→ : {name : Name} {f a b : Term}
                  → differ name name f (SUP a b) (SUP a b)
                  → differ name name f a a × differ name name f b b
differNF-SUPₗ→ {name} {f} {a} {b} (differ-SUP .a .a .b .b diff diff₁) = diff , diff₁


{--
differNF-MSUPₗ→ : {name : Name} {f a b : Term}
                  → differ name name f (MSUP a b) (MSUP a b)
                  → differ name name f a a × differ name name f b b
differNF-MSUPₗ→ {name} {f} {a} {b} (differ-MSUP .a .a .b .b diff diff₁) = diff , diff₁
--}


differNF-INLₗ→ : {name : Name} {f a : Term}
                → differ name name f (INL a) (INL a)
                → differ name name f a a
differNF-INLₗ→ {name} {f} {a} (differ-INL .a .a diff) = diff


differNF-INRₗ→ : {name : Name} {f a : Term}
                → differ name name f (INR a) (INR a)
                → differ name name f a a
differNF-INRₗ→ {name} {f} {a} (differ-INR .a .a diff) = diff


<⊎≤ : (a b : ℕ) → a < b ⊎ b ≤ a
<⊎≤ a b with a <? b
... | yes y = inj₁ y
... | no y = inj₂ (≮⇒≥ y)



abstract
  updNF⇓names : (gc0 : get-choose-ℕ)
            (k : ℕ) (f : Term) (name : Name) (w1 w1' w2 : 𝕎·) (a : Term) (v : Term)
            → # f
            → ¬Names f
            → ∀𝕎-get0-NUM w1 name
            → ∀𝕎-get0-NUM w1' name
            → compatible· name w1 Res⊤
            → compatible· name w1' Res⊤
            → isValue v
            → ((k' : ℕ) → k' < k → ⇓PresDiffNF f name k')
            → differ name name f a a
            → steps k (LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w2)
            → Σ 𝕎· (λ w2' → APPLY (upd name f) a ⇓ v from w1' to w2' × ¬Names v)
  updNF⇓names gc0 k f name w1 w1' w2 a v cf nnf gtn gtn' compat1 compat2 isv pd diff comp = concl comp8 (<⊎≤ n' m)
    where
      seqv : Term
      seqv = SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))

      h1 : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w → Σ Term (λ u →
              Σ (steps k1 (a , w1) ≡ (u , w)) (λ comp1 →
              isValue u
              × steps k2 (sub u seqv , w) ≡ (v , w2)
              × Σ (steps (suc k1) (LET a seqv , w1) ≡ (sub u seqv , w)) (λ comp2 →
              steps→𝕎s {k1} {w1} {w} {a} {u} comp1 ++ [ w ] ≡ steps→𝕎s {suc k1} {w1} {w} {LET a seqv} {sub u seqv} comp2
              × k1 + k2 < k))))))
      h1 = LET→hasValue-decomp k a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) v w1 w2 comp isv

      k1 : ℕ
      k1 = fst h1

      k2 : ℕ
      k2 = fst (snd h1)

      w3 : 𝕎·
      w3 = fst (snd (snd h1))

      u : Term
      u = fst (snd (snd (snd h1)))

      comp1 : steps k1 (a , w1) ≡ (u , w3)
      comp1 = fst (snd (snd (snd (snd h1))))

      isvu : isValue u
      isvu = fst (snd (snd (snd (snd (snd h1)))))

      comp2 : steps k2 (sub u (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w3) ≡ (v , w2)
      comp2 = fst (snd (snd (snd (snd (snd (snd h1))))))

      ltk12 : k1 + k2 < k
      ltk12 = snd (snd (snd (snd (snd (snd (snd (snd (snd h1))))))))

      comp3 : steps k2 (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (v , w2)
      comp3 rewrite sym (sub-SEQ-updGt u name f cf) = comp2

      e13 : w1 ⊑· w3
      e13 = steps→⊑ k1 a u comp1

      h2 : Σ ℕ (λ k3 → Σ ℕ (λ k4 → Σ 𝕎· (λ w4 → Σ Term (λ u' →
             Σ (steps k3 (updGt name u , w3) ≡ (u' , w4)) (λ comp1 →
             isValue u'
             × steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
             × Σ (steps (suc k3) (LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4)) (λ comp2 →
             steps→𝕎s {k3} {w3} {w4} {updGt name u} {u'} comp1 ++ [ w4 ] ≡ steps→𝕎s {suc k3} {w3} {w4} {LET (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} {sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} comp2
             × k3 + k4 < k2))))))
      h2 = LET→hasValue-decomp k2 (updGt name u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) v w3 w2 comp3 isv

      k3 : ℕ
      k3 = fst h2

      k4 : ℕ
      k4 = fst (snd h2)

      w4 : 𝕎·
      w4 = fst (snd (snd h2))

      u' : Term
      u' = fst (snd (snd (snd h2)))

      comp4 : steps k3 (updGt name u , w3) ≡ (u' , w4)
      comp4 = fst (snd (snd (snd (snd h2))))

      isvu' : isValue u'
      isvu' = fst (snd (snd (snd (snd (snd h2)))))

      comp5 : steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
      comp5 = fst (snd (snd (snd (snd (snd (snd h2))))))

      ltk34 : k3 + k4 < k2
      ltk34 = snd (snd (snd (snd (snd (snd (snd (snd (snd h2))))))))

      h3 : Σ ℕ (λ k5 → Σ ℕ (λ k6 → Σ ℕ (λ k7 → Σ 𝕎· (λ w5 → Σ 𝕎· (λ w6 → Σ ℕ (λ n → Σ ℕ (λ m →
             steps k5 (get0 name , w3) ≡ (NUM n , w5)
             × steps k6 (u , w5) ≡ (NUM m , w6)
             × ((n < m × steps k7 (setT name u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
             × k5 + k6 + k7 < k3)))))))
      h3 = IFLT→hasValue-decomp k3 (get0 name) u (setT name u) AX u' w3 w4 comp4 isvu'

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

      comp1b : steps k1 (a , w1) ≡ (NUM m , w3)
      comp1b rewrite sym eqm = comp1

      h4 : Σ 𝕎· (λ w3' → a ⇓ NUM m from w1' to w3' × differ name name f (NUM m) (NUM m))
      h4 = pd k1 (≤-<-trans (m≤n⇒m≤n+o k2 ≤-refl) ltk12) w1 w3 w1' a (NUM m) tt compat1 compat2 gtn gtn' diff comp1b

      h4→ : Σ 𝕎· (λ w3' → a ⇓ NUM m from w1' to w3' × differ name name f (NUM m) (NUM m))
            → Σ 𝕎· (λ w3' → a ⇓ NUM m from w1' to w3')
      h4→ (w3' , c , d) = w3' , c

      w3' : 𝕎·
      w3' = fst (h4→ h4)

      comp1' : a ⇓ NUM m from w1' to w3'
      comp1' = snd (h4→ h4)

      e13' : w1' ⊑· w3'
      e13' = steps→⊑ (fst comp1') a (NUM m) (snd comp1')

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

      comp5b : steps k4 (APPLY f (NUM m) , w4) ≡ (v , w2)
      comp5b = trans (≡Term→≡steps k4 w4 (APPLY-NUM-shift≡ f cf m u u' eqm)) comp5

      compa' : APPLY (upd name f) a ⇓ LET a (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) from w1' to w1'
      compa' = ⇓≡ᵣ (sub a (updBody name f)) (sym (sub-upd name f a cf)) (APPLY-LAMBDA⇓ w1' (updBody name f) a)

      compb' : APPLY (upd name f) a ⇓ LET (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) from w1' to w3'
      compb' = ⇓-trans₂ compa' (LET⇓ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) comp1')

      compc' : APPLY (upd name f) a ⇓ SEQ (updGt name (NUM m)) (APPLY f (NUM m)) from w1' to w3'
      compc' = ⇓-trans₂ compb' (⇓≡ᵣ (sub (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))))
                                    (sym (sub-NUM-SEQ-updGt m name f cf))
                                    (LET-val⇓ w3' (NUM m) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) tt))

      gtn0 : Σ ℕ (λ j → getT 0 name w3 ≡ just (NUM j))
      gtn0 = lower (gtn w3 e13)

      eqc1 : c1 ≡ NUM n
      eqc1 = fst (Σ≡just-NUM×steps→≡NUM k5' (getT 0 name w3) c1 n w3 w5 gtn0 g2 comp6b)

      eqw35 : w3 ≡ w5
      eqw35 = snd (Σ≡just-NUM×steps→≡NUM k5' (getT 0 name w3) c1 n w3 w5 gtn0 g2 comp6b)

      eqchT : chooseT name w6 u ≡ chooseT name w3 (NUM m)
      eqchT rewrite sym eqm | sym eqw56 | sym eqw35 = refl

      g3a : Σ ℕ (λ n' → getT 0 name w3' ≡ just (NUM n'))
      g3a = lower (gtn' w3' e13')

      n' : ℕ
      n' = fst g3a

      g3 : getT 0 name w3' ≡ just (NUM n')
      g3 = snd g3a

      compd' : APPLY (upd name f) a ⇓ SEQ (IFLT (NUM n') (NUM m) (setT name (NUM m)) AX) (APPLY f (NUM m)) from w1' to w3'
      compd' = ⇓-trans₂ compc' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM-1st⇓ (NUM m) (setT name (NUM m)) AX (APPLY-CS-NUM⇓ (NUM n') w3' 0 name g3)))

      concl : ((n < m × steps k7 (setT name u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
              → (n' < m ⊎ m ≤ n')
              → Σ 𝕎· (λ w2' → APPLY (upd name f) a ⇓ v from w1' to w2' × ¬Names v)
      concl (inj₁ (ltnm , comp8b)) (inj₁ ltnm') = chooseT name w3' (NUM m) , comph' , nnv
        where
          compe' : APPLY (upd name f) a ⇓ SEQ (setT name (NUM m)) (APPLY f (NUM m)) from w1' to w3'
          compe' = ⇓-trans₂ compd' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM<⇓ ltnm' (setT name (NUM m)) AX w3'))

          comp8c : u' ≡ AX × w4 ≡ chooseT name w6 u
          comp8c = setT⇓→ k7 name u u' w6 w4 isvu' comp8b

          compf' : APPLY (upd name f) a ⇓ SEQ AX (APPLY f (NUM m)) from w1' to chooseT name w3' (NUM m)
          compf' = ⇓-trans₂ compe' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (setT⇓ name (NUM m) w3'))

          comp5c : steps k4 (APPLY f (NUM m) , chooseT name w3 (NUM m)) ≡ (v , w2)
          comp5c = trans (≡𝕎→≡steps k4 (APPLY f (NUM m)) (trans (sym eqchT) (sym (snd comp8c)))) comp5b

          compg' : APPLY (upd name f) a ⇓ APPLY f (NUM m) from w1' to chooseT name w3' (NUM m)
          compg' = ⇓-trans₂ compf' (SEQ-val⇓ (chooseT name w3' (NUM m)) AX (APPLY f (NUM m)) tt)

          h6 : steps k4 (APPLY f (NUM m) , chooseT name w3' (NUM m)) ≡ (v , chooseT name w3' (NUM m))
               × chooseT name w3 (NUM m) ≡ w2
               × ¬Names v
               × (¬Enc (APPLY f (NUM m)) → ¬Enc v × fvars v ⊆ fvars (APPLY f (NUM m)))
          h6 = ¬Names→steps k4 (chooseT name w3 (NUM m)) w2 (chooseT name w3' (NUM m)) (APPLY f (NUM m)) v (→∧≡true {¬names f} {¬names (NUM m)} nnf refl) comp5c

          comph' : APPLY (upd name f) a ⇓ v from w1' to chooseT name w3' (NUM m)
          comph' = ⇓-trans₂ compg' (k4 , fst h6)

          nnv : ¬Names v
          nnv = steps→¬Names k4 (chooseT name w3 (NUM m)) w2 (APPLY f (NUM m)) v comp5c (→∧≡true {¬names f} {¬names (NUM m)} nnf refl)

      concl (inj₁ (ltnm , comp8b)) (inj₂ ltnm') = w3' , compg' , nnv
        where
          compe' : APPLY (upd name f) a ⇓ SEQ AX (APPLY f (NUM m)) from w1' to w3'
          compe' = ⇓-trans₂ compd' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM¬<⇓ (≤⇒≯ ltnm') (setT name (NUM m)) AX w3'))

          compf' : APPLY (upd name f) a ⇓ APPLY f (NUM m) from w1' to w3'
          compf' = ⇓-trans₂ compe' (SEQ-val⇓ w3' AX (APPLY f (NUM m)) tt)

          comp8c : u' ≡ AX × w4 ≡ chooseT name w6 u
          comp8c = setT⇓→ k7 name u u' w6 w4 isvu' comp8b

          comp5c : steps k4 (APPLY f (NUM m) , chooseT name w3 (NUM m)) ≡ (v , w2)
          comp5c = trans (≡𝕎→≡steps k4 (APPLY f (NUM m)) (trans (sym eqchT) (sym (snd comp8c)))) comp5b

          h6 : steps k4 (APPLY f (NUM m) , w3') ≡ (v , w3')
               × (chooseT name w3 (NUM m)) ≡ w2
               × ¬Names v
               × (¬Enc (APPLY f (NUM m)) → ¬Enc v × fvars v ⊆ fvars (APPLY f (NUM m)))
          h6 = ¬Names→steps k4 (chooseT name w3 (NUM m)) w2 w3' (APPLY f (NUM m)) v (→∧≡true {¬names f} {¬names (NUM m)} nnf refl) comp5c

          compg' : APPLY (upd name f) a ⇓ v from w1' to w3'
          compg' = ⇓-trans₂ compf' (k4 , fst h6)

          nnv : ¬Names v
          nnv = steps→¬Names k4 (chooseT name w3 (NUM m)) w2 (APPLY f (NUM m)) v comp5c (→∧≡true {¬names f} {¬names (NUM m)} nnf refl)

      concl (inj₂ (ltnm , comp8b)) (inj₁ ltnm') = chooseT name w3' (NUM m) , comph' , nnv
        where
          compe' : APPLY (upd name f) a ⇓ SEQ (setT name (NUM m)) (APPLY f (NUM m)) from w1' to w3'
          compe' = ⇓-trans₂ compd' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM<⇓ ltnm' (setT name (NUM m)) AX w3'))

          compf' : APPLY (upd name f) a ⇓ SEQ AX (APPLY f (NUM m)) from w1' to chooseT name w3' (NUM m)
          compf' = ⇓-trans₂ compe' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (setT⇓ name (NUM m) w3'))

          compg' : APPLY (upd name f) a ⇓ APPLY f (NUM m) from w1' to chooseT name w3' (NUM m)
          compg' = ⇓-trans₂ compf' (SEQ-val⇓ (chooseT name w3' (NUM m)) AX (APPLY f (NUM m)) tt)

          eqw64 : w6 ≡ w4
          eqw64 = stepsVal→ᵣ AX u' w6 w4 k7 tt comp8b

          comp5c : steps k4 (APPLY f (NUM m) , w3) ≡ (v , w2)
          comp5c = trans (≡𝕎→≡steps k4 (APPLY f (NUM m)) (trans (trans eqw35 eqw56) eqw64)) comp5b

          h6 : steps k4 (APPLY f (NUM m) , chooseT name w3' (NUM m)) ≡ (v , chooseT name w3' (NUM m))
               × w3 ≡ w2
               × ¬Names v
               × (¬Enc (APPLY f (NUM m)) → ¬Enc v × fvars v ⊆ fvars (APPLY f (NUM m)))
          h6 = ¬Names→steps k4 w3 w2 (chooseT name w3' (NUM m)) (APPLY f (NUM m)) v (→∧≡true {¬names f} {¬names (NUM m)} nnf refl) comp5c

          comph' : APPLY (upd name f) a ⇓ v from w1' to chooseT name w3' (NUM m)
          comph' = ⇓-trans₂ compg' (k4 , fst h6)

          nnv : ¬Names v
          nnv = steps→¬Names k4 w3 w2 (APPLY f (NUM m)) v comp5c (→∧≡true {¬names f} {¬names (NUM m)} nnf refl)

      concl (inj₂ (ltnm , comp8b)) (inj₂ ltnm') = w3' , compg' , nnv
        where
          compe' : APPLY (upd name f) a ⇓ SEQ AX (APPLY f (NUM m)) from w1' to w3'
          compe' = ⇓-trans₂ compd' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM¬<⇓ (≤⇒≯ ltnm') (setT name (NUM m)) AX w3'))

          compf' : APPLY (upd name f) a ⇓ APPLY f (NUM m) from w1' to w3'
          compf' = ⇓-trans₂ compe' (SEQ-val⇓ w3' AX (APPLY f (NUM m)) tt)

          eqw64 : w6 ≡ w4
          eqw64 = stepsVal→ᵣ AX u' w6 w4 k7 tt comp8b

          comp5c : steps k4 (APPLY f (NUM m) , w3) ≡ (v , w2)
          comp5c = trans (≡𝕎→≡steps k4 (APPLY f (NUM m)) (trans (trans eqw35 eqw56) eqw64)) comp5b

          h6 : steps k4 (APPLY f (NUM m) , w3') ≡ (v , w3')
               × w3 ≡ w2
               × ¬Names v
               × (¬Enc (APPLY f (NUM m)) → ¬Enc v × fvars v ⊆ fvars (APPLY f (NUM m)))
          h6 = ¬Names→steps k4 w3 w2 w3' (APPLY f (NUM m)) v (→∧≡true {¬names f} {¬names (NUM m)} nnf refl) comp5c

          compg' : APPLY (upd name f) a ⇓ v from w1' to w3'
          compg' = ⇓-trans₂ compf' (k4 , fst h6)

          nnv : ¬Names v
          nnv = steps→¬Names k4 w3 w2 (APPLY f (NUM m)) v comp5c (→∧≡true {¬names f} {¬names (NUM m)} nnf refl)



abstract

  differNF⇓-aux2 : (gc0 : get-choose-ℕ)
                   (f : Term) (cf : # f) (nn : ¬Names f) (name : Name) (w1 w2 w1' w0 : 𝕎·) (a b v : Term) (k : ℕ)
                   → compatible· name w1 Res⊤
                   → compatible· name w1' Res⊤
                   → ∀𝕎-get0-NUM w1 name
                   → ∀𝕎-get0-NUM w1' name
                   → differ name name f a a
                   → step a w1 ≡ just (b , w2)
                   → steps k (b , w2) ≡ (v , w0)
                   → isValue v
                   → ((k' : ℕ) → k' < k → ⇓PresDiffNF f name k')
                   → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       b ⇓ a'' from w2 to w3
                       × a ⇓ a'' from w1' to w3'
                       × differ name name f a'' a'')))
--  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .NAT b v k compat1 compat2 agtn atgn' differ-NAT s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NAT
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .QNAT b v k compat1 compat2 agtn atgn' differ-QNAT s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QNAT
--  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .TNAT b v k compat1 compat2 agtn atgn' differ-TNAT s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TNAT
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(LT a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-LT a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LT _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LT _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(QLT a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-QLT a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QLT _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QLT _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(NUM x) b v k compat1 compat2 agtn atgn' (differ-NUM x) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NUM _
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(IFLT a₁ b₁ c₁ d₁) b v k compat1 compat2 agtn atgn' (differ-IFLT a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p) rewrite p with is-NUM b₁
  ... |    inj₁ (m , q) rewrite q with n <? m
  ... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = c₁ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM<⇓ r c₁ d₁ w1' , diff₂
  ... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = d₁ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM¬<⇓ r c₁ d₁ w1' , diff₃
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(IFLT a₁ b₁ c₁ d₁) b v k compat1 compat2 agtn atgn' (differ-IFLT a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) s hv isvv pd | inj₁ (n , p) | inj₂ q with step⊎ b₁ w1
  ... |       inj₁ (b₁' , w1'' , z ) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFLT (NUM n) (fst ind) c₁ d₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    IFLT-NUM-2nd⇓ n c₁ d₁ (fst (snd (snd (snd ind)))) , --IFLT-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd ind)))) ,
    IFLT-NUM-2nd⇓ n c₁ d₁ (fst (snd (snd (snd (snd ind))))) , --IFLT-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-IFLT _ _ _ _ _ _ _ _ (differ-NUM n) (snd (snd (snd (snd (snd ind))))) diff₂ diff₃ --ret (IFLT a b' c d) w'
    where
      hv0 : hasValueℕ k b₁' w1''
      hv0 = IFLT-NUM→hasValue k n b₁' c₁ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              b₁' ⇓ b'' from w1'' to w3 × b₁ ⇓ b'' from w1' to w3' × differ name name f b'' b'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) b₁ b₁' (fst hv0) k compat1 compat2 agtn atgn' diff₁ z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFLT-NUM→ n b₁' c₃ d₁ w1'' {k} hv) pd
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(IFLT a₁ b₁ c₁ d₁) b v k compat1 compat2 agtn atgn' (differ-IFLT a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) s hv isvv pd | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFLT (fst ind) b₁ c₁ d₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    IFLT-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd ind)))) ,
    IFLT-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-IFLT _ _ _ _ _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁ diff₂ diff₃
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = IFLT→hasValue k a₁' b₁ c₁ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFLT→ a₁' b₁ c₃ d₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(IFEQ a₁ b₁ c₁ d₁) b v k compat1 compat2 agtn atgn' (differ-IFEQ a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p) rewrite p with is-NUM b₁
  ... |    inj₁ (m , q) rewrite q with n ≟ m
  ... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = c₁ , w1 , w1' , ⇓from-to-refl _ _ , IFEQ-NUM=⇓ r c₁ d₁ w1' , diff₂
  ... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = d₁ , w1 , w1' , ⇓from-to-refl _ _ , IFEQ-NUM¬=⇓ r c₁ d₁ w1' , diff₃
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(IFEQ a₁ b₁ c₁ d₁) b v k compat1 compat2 agtn atgn' (differ-IFEQ a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) s hv isvv pd | inj₁ (n , p) | inj₂ q with step⊎ b₁ w1
  ... |       inj₁ (b₁' , w1'' , z ) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFEQ (NUM n) (fst ind) c₁ d₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    IFEQ-NUM-2nd⇓ n c₁ d₁ (fst (snd (snd (snd ind)))) , --IFEQ-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd ind)))) ,
    IFEQ-NUM-2nd⇓ n c₁ d₁ (fst (snd (snd (snd (snd ind))))) , --IFEQ-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-IFEQ _ _ _ _ _ _ _ _ (differ-NUM n) (snd (snd (snd (snd (snd ind))))) diff₂ diff₃ --ret (IFEQ a b' c d) w'
    where
      hv0 : hasValueℕ k b₁' w1''
      hv0 = IFEQ-NUM→hasValue k n b₁' c₁ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              b₁' ⇓ b'' from w1'' to w3 × b₁ ⇓ b'' from w1' to w3' × differ name name f b'' b'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) b₁ b₁' (fst hv0) k compat1 compat2 agtn atgn' diff₁ z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFEQ-NUM→ n b₁' c₃ d₁ w1'' {k} hv) pd
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(IFEQ a₁ b₁ c₁ d₁) b v k compat1 compat2 agtn atgn' (differ-IFEQ a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) s hv isvv pd | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    IFEQ (fst ind) b₁ c₁ d₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    IFEQ-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd ind)))) ,
    IFEQ-NUM-1st⇓ b₁ c₁ d₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-IFEQ _ _ _ _ _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁ diff₂ diff₃
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = IFEQ→hasValue k a₁' b₁ c₁ d₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFEQ→ a₁' b₁ c₃ d₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(SUC a₁) b v k compat1 compat2 agtn atgn' (differ-SUC a₁ .a₁ diff) s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM (suc n) , w1 , w1' , (0 , refl) , (1 , refl) , differ-NUM (suc n)
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    SUC (fst ind) ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    SUC⇓ (fst (snd (snd (snd ind)))) ,
    SUC⇓ (fst (snd (snd (snd (snd ind))))) ,
    differ-SUC _ _ (snd (snd (snd (snd (snd ind)))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = SUC→hasValue k a₁' v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(NATREC a₁ a₂ a₃) b v k compat1 compat2 agtn atgn' (differ-NATREC a₁ .a₁ a₂ .a₂ a₃ .a₃ diff diff₁ diff₂) s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p)
    rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s))
    = NATRECr n a₂ a₃ , w1 , w1' , (0 , refl) , (1 , refl) , differ-NATRECr {name} {name} {f} {n} {a₂} {a₂} {a₃} {a₃} cf diff₁ diff₂
  ... | inj₂ p with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    NATREC (fst ind) a₂ a₃ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    NATREC⇓ a₂ a₃ (fst (snd (snd (snd ind)))) ,
    NATREC⇓ a₂ a₃ (fst (snd (snd (snd (snd ind))))) ,
    differ-NATREC _ _ _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁ diff₂
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = NATREC→hasValue k a₁' a₂ a₃ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(PI a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-PI a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PI _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PI _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(LAMBDA a) b v k compat1 compat2 agtn atgn' (differ-LAMBDA a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LAMBDA _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LAMBDA _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(APPLY a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-APPLY a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd with is-LAM a₁
  ... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d
    where
      d : differ name name f t t ⊎ t ≡ updBody name f
      d = differNF-LAMBDAₗ→ diff

      concl : (differ name name f t t ⊎ t ≡ updBody name f)
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub b₁ t ⇓ a'' from w1 to w3 × APPLY (LAMBDA t) b₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      concl (inj₁ d) =
        sub b₁ t ,
        w1 , w1' ,
        ⇓from-to-refl _ _ , APPLY-LAMBDA⇓ w1' t b₁ ,
        differ-sub cf d diff₁
      concl (inj₂ e) rewrite e | sub-upd name f b₁ cf =
        v , w0 , fst hv2 , (k , hv1) , fst (snd hv2) , differ-refl name name f v (snd (snd hv2))
        where
          hv0 : steps k (sub b₁ (updBody name f) , w1) ≡ (v , w0)
          hv0 rewrite e = hv

          hv1 : steps k (LET b₁ (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w0)
          hv1 rewrite sym (sub-upd name f b₁ cf) = hv0

          hv2 : Σ 𝕎· (λ w2' → APPLY (upd name f) b₁ ⇓ v from w1' to w2' × ¬Names v)
          hv2 = updNF⇓names gc0 k f name w1 w1' w0 b₁ v cf nnf agtn atgn' compat1 compat2 isvv pd diff₁ hv1
  ... | inj₂ x with is-CS a₁
  ... |    inj₁ (name , p) rewrite p = ⊥-elim (differ-CSₗ→ diff)
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(APPLY a₁ b₁) a' v k compat1 compat2 agtn atgn' (differ-APPLY a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd | inj₂ x | inj₂ y with is-MSEQ a₁
  ... | inj₁ (sq , r) rewrite r | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    MAPP sq b₁ , w1 , w1' , (0 , refl) , (1 , refl) , differ-MAPP sq b₁ b₁ diff₁
  ... | inj₂ r with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    APPLY (fst ind) b₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    APPLY⇓ b₁ (fst (snd (snd (snd ind)))) ,
    APPLY⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-APPLY _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = APPLY→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-APPLY→ a₁' b₁ w1'' {k} hv) pd
  ... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(FIX a₁) b v k compat1 compat2 agtn atgn' (differ-FIX a₁ .a₁ diff) s hv isvv pd with is-LAM a₁
  ... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : differ name name f t t ⊎ t ≡ updBody name f
      d = differNF-LAMBDAₗ→ diff

      concl : (differ name name f t t ⊎ t ≡ updBody name f)
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub (FIX (LAMBDA t)) t ⇓ a'' from w1 to w3 × FIX (LAMBDA t) ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      concl (inj₁ d) =
        sub (FIX (LAMBDA t)) t ,
        w1 , w1' ,
        ⇓from-to-refl _ _ ,
        FIX-LAMBDA⇓ w1' t ,
        differ-sub cf d (differ-FIX _ _ (differ-LAMBDA _ _ d))
      concl (inj₂ e) rewrite e | sub-upd name f (FIX (upd name f)) cf =
        v , w0 , fst hv2 , (k , hv1) , (⇓-trans₂ (FIX-LAMBDA⇓ w1' (updBody name f)) cs) ,
        differ-refl name name f v (snd (snd hv2))
        where
          hv0 : steps k (sub (FIX (upd name f)) (updBody name f) , w1) ≡ (v , w0)
          hv0 rewrite e = hv

          hv1 : steps k (LET (FIX (upd name f)) (SEQ (updGt name (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w0)
          hv1 rewrite sym (sub-upd name f (FIX (upd name f)) cf) = hv0

          df : differ name name f (FIX (upd name f)) (FIX (upd name f))
          df = differ-FIX _ _ differ-upd

          hv2 : Σ 𝕎· (λ w2' → APPLY (upd name f) (FIX (upd name f)) ⇓ v from w1' to w2' × ¬Names v)
          hv2 = updNF⇓names gc0 k f name w1 w1' w0 (FIX (upd name f)) v cf nnf agtn atgn' compat1 compat2 isvv pd df hv1

          cs : sub (FIX (upd name f)) (updBody name f) ⇓ v from w1' to (fst hv2)
          cs = APPLY-LAMBDA⇓→ (fst (fst (snd hv2))) isvv (snd (fst (snd hv2)))
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    FIX (fst ind) ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    FIX⇓ (fst (snd (snd (snd ind)))) ,
    FIX⇓ (fst (snd (snd (snd (snd ind))))) ,
    differ-FIX _ _ (snd (snd (snd (snd (snd ind)))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = FIX→hasValue k a₁' v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-FIX→ a₁' w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(LET a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-LET a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd with isValue⊎ a₁
  ... | inj₁ x rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    sub a₁ b₁ , w1 , w1' ,
    ⇓from-to-refl _ _ , LET-val⇓ w1' a₁ b₁ isv , differ-sub cf diff₁ diff
    where
      isv : isValue a₁
      isv = differ-isValue→ diff x
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    LET (fst ind) b₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    LET⇓ b₁ (fst (snd (snd (snd ind)))) ,
    LET⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-LET _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = LET→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-LET→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(WT a₁ b₁ c₁) b v k compat1 compat2 agtn atgn' (differ-WT a₁ .a₁ b₁ .b₁ c₁ .c₁ diff diff₁ diff₂) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = WT _ _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-WT _ _ _ _ _ _ diff diff₁ diff₂
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(SUP a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-SUP a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUP _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUP _ _ _ _ diff diff₁
  {--differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(DSUP a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-DSUP a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd with is-SUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : differ name name f u₁ u₁ × differ name name f u₂ u₂
      d = differNF-SUPₗ→ diff

      concl : differ name name f u₁ u₁ × differ name name f u₂ u₂
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u₂ (sub u₁ b₁) ⇓ a'' from w1 to w3 × DSUP (SUP u₁ u₂) b₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      concl (d1 , d2) =
        sub u₂ (sub u₁ b₁) , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DSUP-SUP⇓ w1' u₁ u₂ b₁ ,
        differ-sub cf (differ-sub cf diff₁ d1) d2
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    DSUP (fst ind) b₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    DSUP⇓ b₁ (fst (snd (snd (snd ind)))) ,
    DSUP⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-DSUP _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = DSUP→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(WREC a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-WREC a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd with is-SUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : differ name name f u₁ u₁ × differ name name f u₂ u₂
      d = differNF-SUPₗ→ diff

      concl : differ name name f u₁ u₁ × differ name name f u₂ u₂
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                  sub (WRECr b₁ u₂) (sub (shiftUp 0 u₂) (sub (shiftUp 0 (shiftUp 0 u₁)) b₁)) ⇓ a'' from w1 to w3
                × WREC (SUP u₁ u₂) b₁ ⇓ a'' from w1' to w3'
                × differ name name f a'' a'')))
      concl (d1 , d2) =
        sub (WRECr b₁ u₂) (sub (shiftUp 0 u₂) (sub (shiftUp 0 (shiftUp 0 u₁)) b₁)) ,
        w1 , w1' ,
        ⇓from-to-refl _ _ ,
        WREC-SUP⇓ w1' u₁ u₂ b₁ ,
        differ-sub cf
          (differ-sub cf (differ-sub cf diff₁ (→differ-shiftUp 0 cf (→differ-shiftUp 0 cf d1)))
            (→differ-shiftUp 0 cf d2))
          (differ-WRECr cf diff₁ d2) --differ-sub cf (differ-sub cf (differ-sub cf diff₁ d1) d2) (differ-WRECr cf diff₁ d2)
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    WREC (fst ind) b₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    WREC⇓ b₁ (fst (snd (snd (snd ind)))) ,
    WREC⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-WREC _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = WREC→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(MT a₁ b₁ c₁) b v k compat1 compat2 agtn atgn' (differ-MT a₁ .a₁ b₁ .b₁ c₁ .c₁ diff diff₁ diff₂) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = MT _ _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-MT _ _ _ _ _ _ diff diff₁ diff₂
  --differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(MSUP a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-MSUP a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = MSUP _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-MSUP _ _ _ _ diff diff₁
  {--differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(DMSUP a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-DMSUP a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd with is-MSUP a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : differ name name f u₁ u₁ × differ name name f u₂ u₂
      d = differNF-MSUPₗ→ diff

      concl : differ name name f u₁ u₁ × differ name name f u₂ u₂
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u₂ (sub u₁ b₁) ⇓ a'' from w1 to w3 × DMSUP (MSUP u₁ u₂) b₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      concl (d1 , d2) =
        sub u₂ (sub u₁ b₁) , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DMSUP-MSUP⇓ w1' u₁ u₂ b₁ ,
        differ-sub cf (differ-sub cf diff₁ d1) d2
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    DMSUP (fst ind) b₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    DMSUP⇓ b₁ (fst (snd (snd (snd ind)))) ,
    DMSUP⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-DMSUP _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = DMSUP→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))--}
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(SUM a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-SUM a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUM _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUM _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(PAIR a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-PAIR a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PAIR _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PAIR _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(SPREAD a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-SPREAD a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd with is-PAIR a₁
  ... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : differ name name f u₁ u₁ × differ name name f u₂ u₂
      d = differNF-PAIRₗ→ diff

      concl : differ name name f u₁ u₁ × differ name name f u₂ u₂
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                  sub u₂ (sub (shiftUp 0 u₁) b₁) ⇓ a'' from w1 to w3
                × SPREAD (PAIR u₁ u₂) b₁ ⇓ a'' from w1' to w3'
                × differ name name f a'' a'')))
      concl (d1 , d2) =
        sub u₂ (sub (shiftUp 0 u₁) b₁) , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        SPREAD-PAIR⇓ w1' u₁ u₂ b₁ ,
        differ-sub cf (differ-sub cf diff₁ (→differ-shiftUp 0 cf d1)) d2 --differ-sub cf (differ-sub cf diff₁ d1) d2
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    SPREAD (fst ind) b₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    SPREAD⇓ b₁ (fst (snd (snd (snd ind)))) ,
    SPREAD⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-SPREAD _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = SPREAD→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(SET a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-SET a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SET _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SET _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(ISECT a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-ISECT a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ISECT _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-ISECT _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(TUNION a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-TUNION a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TUNION _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TUNION _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(UNION a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-UNION a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNION _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNION _ _ _ _ diff diff₁
--  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(QTUNION a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-QTUNION a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QTUNION _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QTUNION _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(INL a) b v k compat1 compat2 agtn atgn' (differ-INL a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INL _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INL _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(INR a) b v k compat1 compat2 agtn atgn' (differ-INR a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INR _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INR _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(DECIDE a₁ b₁ c₁) b v k compat1 compat2 agtn atgn' (differ-DECIDE a₁ .a₁ b₁ .b₁ c₁ .c₁ diff diff₁ diff₂) s hv isvv pd with is-INL a₁
  ... | inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : differ name name f u u
      d = differNF-INLₗ→ diff

      concl : differ name name f u u
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u b₁ ⇓ a'' from w1 to w3 × DECIDE (INL u) b₁ c₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      concl d1 =
        sub u b₁ , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DECIDE-INL⇓ w1' u _ _ ,
        differ-sub cf diff₁ d1
  ... | inj₂ x with is-INR a₁
  ... |    inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    concl d
    where
      d : differ name name f u u
      d = differNF-INRₗ→ diff

      concl : differ name name f u u
              → Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                       sub u c₁ ⇓ a'' from w1 to w3 × DECIDE (INR u) b₁ c₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      concl d1 =
        sub u c₁ , w1 , w1' ,
        ⇓from-to-refl _ _ ,
        DECIDE-INR⇓ w1' u _ _ ,
        differ-sub cf diff₂ d1
  ... |    inj₂ y with step⊎ a₁ w1
  ... |       inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    DECIDE (fst ind) b₁ c₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    DECIDE⇓ b₁ c₁ (fst (snd (snd (snd ind)))) ,
    DECIDE⇓ b₁ c₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-DECIDE _ _ _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁ diff₂
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = DECIDE→hasValue k a₁' b₁ c₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-DECIDE→ a₁' b₁ c₃ w1'' {k} hv) pd
  ... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(EQ a₁ b₁ c₁) b v k compat1 compat2 agtn atgn' (differ-EQ a₁ .a₁ b₁ .b₁ c₁ .c₁ diff diff₁ diff₂) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQ _ _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-EQ _ _ _ _ _ _ diff diff₁ diff₂
--  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(EQB a₁ b₁ c₁ d₁) b v k compat1 compat2 agtn atgn' (differ-EQB a₁ .a₁ b₁ .b₁ c₁ .c₁ d₁ .d₁ diff diff₁ diff₂ diff₃) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQB _ _ _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-EQB _ _ _ _ _ _ _ _ diff diff₁ diff₂ diff₃
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .AX b v k compat1 compat2 agtn atgn' differ-AX s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = AX , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-AX
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .FREE b v k compat1 compat2 agtn atgn' differ-FREE s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FREE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FREE
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(MSEQ x) b v k compat1 compat2 agtn atgn' (differ-MSEQ x) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = MSEQ x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-MSEQ x
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(MAPP x a₁) b v k compat1 compat2 agtn atgn' (differ-MAPP x a₁ .a₁ diff) s hv isvv pd with is-NUM a₁
  ... | inj₁ (n , p)
    rewrite p
            | sym (pair-inj₁ (just-inj s))
            | sym (pair-inj₂ (just-inj s))
            | stepsVal (NUM (x n)) w1 k tt
            | sym (pair-inj₁ hv)
            | sym (pair-inj₂ hv) = NUM (x n) , w1 , w1' , (0 , refl) , (1 , refl) , differ-NUM (x n)
  ... | inj₂ y with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    MAPP x (fst ind) ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    MAPP⇓ x (fst (snd (snd (snd ind)))) ,
    MAPP⇓ x (fst (snd (snd (snd (snd ind))))) ,
    differ-MAPP _ _ _ (snd (snd (snd (snd (snd ind)))))
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = MAPP→hasValue k x a₁' v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-APPLY→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(CHOOSE a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-CHOOSE a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd with is-NAME a₁
  ... | inj₁ (name , p) rewrite p = ⊥-elim (differ-NAMEₗ→ diff)
  ... | inj₂ x with step⊎ a₁ w1
  ... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
    CHOOSE (fst ind) b₁ ,
    fst (snd ind) ,
    fst (snd (snd ind)) ,
    CHOOSE⇓ b₁ (fst (snd (snd (snd ind)))) ,
    CHOOSE⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
    differ-CHOOSE _ _ _ _ (snd (snd (snd (snd (snd ind))))) diff₁
    where
      hv0 : hasValueℕ k a₁' w1''
      hv0 = CHOOSE→hasValue k a₁' b₁ v w1'' w0 hv isvv

      ind : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
              a₁' ⇓ a'' from w1'' to w3 × a₁ ⇓ a'' from w1' to w3' × differ name name f a'' a'')))
      ind = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' (fst (snd hv0)) a₁ a₁' (fst hv0) k compat1 compat2 agtn atgn' diff z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-CHOOSE→ a₁' b₁ w1'' {k} hv) pd
  ... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
--  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(TSQUASH a) b v k compat1 compat2 agtn atgn' (differ-TSQUASH a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TSQUASH _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TSQUASH _ _ diff
--  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(TTRUNC a) b v k compat1 compat2 agtn atgn' (differ-TTRUNC a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TTRUNC _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TTRUNC _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .NOWRITE b v k compat1 compat2 agtn atgn' differ-NOWRITE s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NOWRITE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NOWRITE
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .NOREAD  b v k compat1 compat2 agtn atgn' differ-NOREAD  s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NOREAD  , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NOREAD
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(SUBSING a) b v k compat1 compat2 agtn atgn' (differ-SUBSING a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUBSING _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUBSING _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .PURE b v k compat1 compat2 agtn atgn' differ-PURE s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PURE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PURE
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .NOSEQ b v k compat1 compat2 agtn atgn' differ-NOSEQ s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NOSEQ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NOSEQ
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .NOENC b v k compat1 compat2 agtn atgn' differ-NOENC s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NOENC , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NOENC
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(TERM a) b v k compat1 compat2 agtn atgn' (differ-TERM a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TERM _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TERM _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(ENC a) b v k compat1 compat2 agtn atgn' (differ-ENC a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ENCr a , w1 , w1' , ⇓from-to-refl _ _ , (1 , refl) , →differ-ENCr diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(PARTIAL a) b v k compat1 compat2 agtn atgn' (differ-PARTIAL a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PARTIAL _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PARTIAL _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(FFDEFS a₁ b₁) b v k compat1 compat2 agtn atgn' (differ-FFDEFS a₁ .a₁ b₁ .b₁ diff diff₁) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FFDEFS _ _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FFDEFS _ _ _ _ diff diff₁
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(UNIV x) b v k compat1 compat2 agtn atgn' (differ-UNIV x) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNIV _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNIV _
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(LIFT a) b v k compat1 compat2 agtn atgn' (differ-LIFT a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LIFT _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LIFT _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(LOWER a) b v k compat1 compat2 agtn atgn' (differ-LOWER a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LOWER _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LOWER _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(SHRINK a) b v k compat1 compat2 agtn atgn' (differ-SHRINK a .a diff) s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SHRINK _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SHRINK _ _ diff
  differNF⇓-aux2 gc0 f cf nnf name w1 w2 w1' w0 .(upd name f) b v k compat1 compat2 agtn atgn' differ-upd s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = upd name f , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-upd



abstract
  differNF⇓-aux : (gc0 : get-choose-ℕ) (f : Term) (cf : # f) (nn : ¬Names f) (name : Name) (n : ℕ)
                  (ind : (n' : ℕ) → n' < n → ⇓PresDiffNF f name n')
                  → ⇓PresDiffNF f name n
  differNF⇓-aux gc0 f cf nnf name 0 ind w1 w2 w1' a v isv compat1 compat2 gt0 gt0' diff comp rewrite pair-inj₁ comp | pair-inj₂ comp =
    w1' , (0 , refl) , diff
  differNF⇓-aux gc0 f cf nnf name (suc n) ind w1 w2 w1' a v isv compat1 compat2 gt0 gt0' diff comp with step⊎ a w1
  ... | inj₁ (a' , w1'' , z) rewrite z =
    fst e ,
    ⇓-trans₂ (fst (snd (snd (snd (snd c))))) (fst (snd e)) ,
    snd (snd e)
    where
      c : Σ Term (λ a'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                    a' ⇓ a'' from w1'' to w3
                    × a ⇓ a'' from w1' to w3'
                    × differ name name f a'' a'')))
      c = differNF⇓-aux2 gc0 f cf nnf name w1 w1'' w1' w2 a a' v n compat1 compat2 gt0 gt0' diff z comp isv λ k i → ind k (<-trans i (n<1+n n))

      d : steps n (fst c , fst (snd c)) ≡ (v , w2)
      d = steps⇓-decomp
            n (fst (fst (snd (snd (snd c))))) a'
            (fst c) v w1'' w2 (fst (snd c)) comp
            (snd (fst (snd (snd (snd c))))) isv

      e₁ : w1 ⊑· fst (snd c)
      e₁ = ⇓→⊑ a (fst c) (step-⇓-from-to-trans z (fst (snd (snd (snd c)))))

      e₂ : w1' ⊑· fst (snd (snd c))
      e₂ = ⇓→⊑ a (fst c) (fst (snd (snd (snd (snd c)))))

      e : Σ 𝕎· (λ w2' → fst c ⇓ v from fst (snd (snd c)) to w2' × differ name name f v v)
      e = ind n ≤-refl (fst (snd c)) w2 (fst (snd (snd c))) (fst c) v isv
              (⊑-compatible· e₁ compat1) (⊑-compatible· e₂ compat2)
              (∀𝕎-mon e₁ gt0)
              (∀𝕎-mon e₂ gt0')
              (snd (snd (snd (snd (snd c)))))
              d
  ... | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = w1' , (0 , refl) , diff



differNF⇓ : (gc0 : get-choose-ℕ) (f : Term) (cf : # f) (nn : ¬Names f) (name : Name) (n : ℕ)
          → ⇓PresDiffNF f name n
differNF⇓ gc0 f cf nnf name = <ℕind _ (differNF⇓-aux gc0 f cf nnf name)



differNF⇓APPLY-upd : (gc0 : get-choose-ℕ) (F f : Term) (cf : # f) (name : Name) (n : ℕ)
                     (w1 w2 w1' : 𝕎·)
                     → ¬Names F
                     → ¬Names f
                     → compatible· name w1 Res⊤
                     → compatible· name w1' Res⊤
                     → ∀𝕎-get0-NUM w1 name
                     → ∀𝕎-get0-NUM w1' name
                     → APPLY F (upd name f) ⇓ NUM n from w1 to w2
                     → Σ 𝕎· (λ w2' → APPLY F (upd name f) ⇓ NUM n from w1' to w2')
differNF⇓APPLY-upd gc0 F f cf name n w1 w2 w1' nnF nnf compat1 compat2 wgt0 wgt0' (k , comp) =
  fst concl , fst (snd concl)
  where
    concl : Σ 𝕎· (λ w2' → APPLY F (upd name f) ⇓ NUM n from w1' to w2' × differ name name f (NUM n) (NUM n))
    concl = differNF⇓ gc0 f cf nnf name k w1 w2 w1'
                      (APPLY F (upd name f)) (NUM n) tt
                      compat1 compat2 wgt0 wgt0'
                      (differ-APPLY _ _ _ _ (differ-refl name name f F nnF) differ-upd) comp

\end{code}
