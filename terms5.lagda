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


module terms5 {L : Level} (W : PossibleWorlds {L})
              (C : Choice) (M : Compatible W C) (G : GetChoice {L} W C M) (E : ChoiceExt {L} W C)
              (N : NewChoice W C M G)
       where
open import worldDef(W)
open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(M)
open import getChoiceDef(W)(C)(M)(G)
open import choiceExtDef(W)(C)(M)(G)(E)
open import newChoiceDef(W)(C)(M)(G)(N)
open import computation(W)(C)(M)(G)(E)(N)
open import terms2(W)(C)(M)(G)(E)(N)
open import terms3(W)(C)(M)(G)(E)(N)
open import terms4(W)(C)(M)(G)(E)(N)

open import continuity-conds(W)(C)(M)(G)(E)(N)






{--
-- This should be a property
→≡getT-chooseT : {name1 name2 : Name} {w1 w2 : 𝕎·} (n : ℕ)
                  → getT 0 name1 w1 ≡ getT 0 name2 w2
                  → getT 0 name1 (chooseT name1 w1 (NUM n)) ≡ getT 0 name2 (chooseT name2 w2 (NUM n))
→≡getT-chooseT {name1} {name2} {w1} {w2} n eqt = {!!}
--}


≡→getT≡ : (w1 w2 : 𝕎·) (n : ℕ) (name : Name) (x : Maybe Term)
           → w1 ≡ w2
           → getT n name w1 ≡ x
           → getT n name w2 ≡ x
≡→getT≡ w1 w2 n name x e h rewrite e = h



steps→¬Names : (k : ℕ) (w1 w2 : 𝕎·) (t u : Term)
              → steps k (t , w1) ≡ (u , w2)
              → ¬Names t
              → ¬Names u
steps→¬Names k w1 w2 t u s nn = snd (snd (¬Names→steps k w1 w2 w2 t u nn s))




⇓PresDiff : (f : Term) (name1 name2 : Name) (n : ℕ) → Set(lsuc(L))
⇓PresDiff f name1 name2 n =
  (w1 w2 w1' : 𝕎·) (a b v : Term)
  → isValue v
  → compatible· name1 w1 Res⊤
  → compatible· name2 w1' Res⊤
  → ∀𝕎-get0-NUM w1 name1
--  → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
--  → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
  → differ name1 name2 f a b
  → getT 0 name1 w1 ≡ getT 0 name2 w1'
  → steps n (a , w1) ≡ (v , w2)
  → Σ 𝕎· (λ w2' → Σ Term (λ v' →
      b ⇓ v' from w1' to w2' × differ name1 name2 f v v' × getT 0 name1 w2 ≡ getT 0 name2 w2'))



upd⇓names : (gc0 : get-choose-ℕ)
            (k : ℕ) (f : Term) (name1 name2 : Name) (w1 w1' w2 : 𝕎·) (a b : Term) (v : Term)
            → # f
            → ¬Names f
            → ∀𝕎-get0-NUM w1 name1
            → compatible· name1 w1 Res⊤
            → compatible· name2 w1' Res⊤
--            → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
--            → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
            → isValue v
            → ((k' : ℕ) → k' < k → ⇓PresDiff f name1 name2 k')
            → getT 0 name1 w1 ≡ getT 0 name2 w1'
            → differ name1 name2 f a b
            → steps k (LET a (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w2)
            → Σ 𝕎· (λ w2' → APPLY (upd name2 f) b ⇓ v from w1' to w2' × getT 0 name1 w2 ≡ getT 0 name2 w2' × ¬Names v)
upd⇓names gc0 k f name1 name2 w1 w1' w2 a b v cf nnf gtn compat1 compat2 isv pd g0 diff comp = concl comp8
  where
    seqv : Term
    seqv = SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))

    h1 : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w → Σ Term (λ u →
            Σ (steps k1 (a , w1) ≡ (u , w)) (λ comp1 →
            isValue u
            × steps k2 (sub u seqv , w) ≡ (v , w2)
            × Σ (steps (suc k1) (LET a seqv , w1) ≡ (sub u seqv , w)) (λ comp2 →
            steps→𝕎s {k1} {w1} {w} {a} {u} comp1 ++ [ w ] ≡ steps→𝕎s {suc k1} {w1} {w} {LET a seqv} {sub u seqv} comp2
            × k1 + k2 < k))))))
    h1 = LET→hasValue-decomp k a (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) v w1 w2 comp isv

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

    comp2 : steps k2 (sub u (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w3) ≡ (v , w2)
    comp2 = fst (snd (snd (snd (snd (snd (snd h1))))))

    --eqws1 : steps→𝕎s {k1} {w1} {w3} {a} {u} comp1 ++ [ w3 ] ≡ steps→𝕎s {suc k1} {w1} {w3} {LET a seqv} {sub u seqv} comp2
    --eqws1 = fst (snd (snd (snd (snd (snd (snd (snd (snd h1))))))))

    ltk12 : k1 + k2 < k
    ltk12 = snd (snd (snd (snd (snd (snd (snd (snd (snd h1))))))))

    comp3 : steps k2 (LET (updGt name1 u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (v , w2)
    comp3 rewrite sym (sub-SEQ-updGt u name1 f cf) = comp2

    e13 : w1 ⊑· w3
    e13 = steps→⊑ k1 a u comp1

    h2 : Σ ℕ (λ k3 → Σ ℕ (λ k4 → Σ 𝕎· (λ w4 → Σ Term (λ u' →
           Σ (steps k3 (updGt name1 u , w3) ≡ (u' , w4)) (λ comp1 →
           isValue u'
           × steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
           × Σ (steps (suc k3) (LET (updGt name1 u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4)) (λ comp2 →
           steps→𝕎s {k3} {w3} {w4} {updGt name1 u} {u'} comp1 ++ [ w4 ] ≡ steps→𝕎s {suc k3} {w3} {w4} {LET (updGt name1 u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} {sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u))))} comp2
           × k3 + k4 < k2))))))
    h2 = LET→hasValue-decomp k2 (updGt name1 u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) v w3 w2 comp3 isv

    k3 : ℕ
    k3 = fst h2

    k4 : ℕ
    k4 = fst (snd h2)

    w4 : 𝕎·
    w4 = fst (snd (snd h2))

    u' : Term
    u' = fst (snd (snd (snd h2)))

    comp4 : steps k3 (updGt name1 u , w3) ≡ (u' , w4)
    comp4 = fst (snd (snd (snd (snd h2))))

    isvu' : isValue u'
    isvu' = fst (snd (snd (snd (snd (snd h2)))))

    comp5 : steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
    comp5 = fst (snd (snd (snd (snd (snd (snd h2))))))

    ltk34 : k3 + k4 < k2
    ltk34 = snd (snd (snd (snd (snd (snd (snd (snd (snd h2))))))))

    h3 : Σ ℕ (λ k5 → Σ ℕ (λ k6 → Σ ℕ (λ k7 → Σ 𝕎· (λ w5 → Σ 𝕎· (λ w6 → Σ ℕ (λ n → Σ ℕ (λ m →
           steps k5 (get0 name1 , w3) ≡ (NUM n , w5)
           × steps k6 (u , w5) ≡ (NUM m , w6)
           × ((n < m × steps k7 (setT name1 u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
           × k5 + k6 + k7 < k3)))))))
    h3 = IFLT→hasValue-decomp k3 (get0 name1) u (setT name1 u) AX u' w3 w4 comp4 isvu'

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

    comp6 : steps k5 (get0 name1 , w3) ≡ (NUM n , w5)
    comp6 = fst (snd (snd (snd (snd (snd (snd (snd h3)))))))

    comp7 : steps k6 (u , w5) ≡ (NUM m , w6)
    comp7 = fst (snd (snd (snd (snd (snd (snd (snd (snd h3))))))))

    comp8 : ((n < m × steps k7 (setT name1 u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
    comp8 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))

    ltk567 : k5 + k6 + k7 < k3
    ltk567 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))

    eqm : u ≡ NUM m
    eqm = stepsVal→ₗ u (NUM m) w5 w6 k6 isvu comp7

    eqw56 : w5 ≡ w6
    eqw56 = stepsVal→ᵣ u (NUM m) w5 w6 k6 isvu comp7

    comp1b : steps k1 (a , w1) ≡ (NUM m , w3)
    comp1b rewrite sym eqm = comp1

    h4 : Σ 𝕎· (λ w3' → Σ Term (λ v' →
                b ⇓ v' from w1' to w3' × differ name1 name2 f (NUM m) v' × getT 0 name1 w3 ≡ getT 0 name2 w3'))
    h4 = pd k1 (<-transʳ (≤-stepsʳ k2 ≤-refl) ltk12) w1 w3 w1' a b (NUM m) tt compat1 compat2 gtn diff g0 comp1b

    h4→ : Σ 𝕎· (λ w3' → Σ Term (λ v' →
                b ⇓ v' from w1' to w3' × differ name1 name2 f (NUM m) v' × getT 0 name1 w3 ≡ getT 0 name2 w3'))
                → Σ 𝕎· (λ w3' → b ⇓ NUM m from w1' to w3' × getT 0 name1 w3 ≡ getT 0 name2 w3')
    h4→ (w3' , v' , c , d , g) rewrite differ-NUM→ d = w3' , c , g

    w3' : 𝕎·
    w3' = fst (h4→ h4)

    comp1' : b ⇓ NUM m from w1' to w3'
    comp1' = fst (snd (h4→ h4))

    e13' : w1' ⊑· w3'
    e13' = steps→⊑ (fst comp1') b (NUM m) (snd comp1')

    g1 : getT 0 name1 w3 ≡ getT 0 name2 w3'
    g1 = snd (snd (h4→ h4))

    h5 : Σ Term (λ u → Σ ℕ (λ k5' → k5' < k5 × getT 0 name1 w3 ≡ just u × steps k5' (u , w3) ≡ (NUM n , w5)))
    h5 = steps-get0 k5 name1 w3 w5 (NUM n) tt comp6

    c1 : Term
    c1 = fst h5

    k5' : ℕ
    k5' = fst (snd h5)

    ltk5' : k5' < k5
    ltk5' = fst (snd (snd h5))

    g2 : getT 0 name1 w3 ≡ just c1
    g2 = fst (snd (snd (snd h5)))

    comp6b : steps k5' (c1 , w3) ≡ (NUM n , w5)
    comp6b = snd (snd (snd (snd h5)))

    comp5b : steps k4 (APPLY f (NUM m) , w4) ≡ (v , w2)
    comp5b = trans (≡Term→≡steps k4 w4 (APPLY-NUM-shift≡ f cf m u u' eqm)) comp5

    compa' : APPLY (upd name2 f) b ⇓ LET b (SEQ (updGt name2 (VAR 0)) (APPLY f (VAR 0))) from w1' to w1'
    compa' = ⇓≡ᵣ (sub b (updBody name2 f)) (sym (sub-upd name2 f b cf)) (APPLY-LAMBDA⇓ w1' (updBody name2 f) b)

    compb' : APPLY (upd name2 f) b ⇓ LET (NUM m) (SEQ (updGt name2 (VAR 0)) (APPLY f (VAR 0))) from w1' to w3'
    compb' = ⇓-trans₂ compa' (LET⇓ (SEQ (updGt name2 (VAR 0)) (APPLY f (VAR 0))) comp1')

    compc' : APPLY (upd name2 f) b ⇓ SEQ (updGt name2 (NUM m)) (APPLY f (NUM m)) from w1' to w3'
    compc' = ⇓-trans₂ compb' (⇓≡ᵣ (sub (NUM m) (SEQ (updGt name2 (VAR 0)) (APPLY f (VAR 0))))
                                  (sym (sub-NUM-SEQ-updGt m name2 f cf))
                                  (LET-val⇓ w3' (NUM m) (SEQ (updGt name2 (VAR 0)) (APPLY f (VAR 0))) tt))

    gtn0 : Σ ℕ (λ j → getT 0 name1 w3 ≡ just (NUM j))
    gtn0 = lower (gtn w3 e13)

    eqc1 : c1 ≡ NUM n
    eqc1 = fst (Σ≡just-NUM×steps→≡NUM k5' (getT 0 name1 w3) c1 n w3 w5 gtn0 g2 comp6b)

    eqw35 : w3 ≡ w5
    eqw35 = snd (Σ≡just-NUM×steps→≡NUM k5' (getT 0 name1 w3) c1 n w3 w5 gtn0 g2 comp6b)

    eqchT : chooseT name1 w6 u ≡ chooseT name1 w3 (NUM m)
    eqchT rewrite sym eqm | sym eqw56 | sym eqw35 = refl

    g3 : getT 0 name2 w3' ≡ just (NUM n)
    g3 = trans (sym g1) (trans g2 (≡just eqc1))

    compd' : APPLY (upd name2 f) b ⇓ SEQ (IFLT (NUM n) (NUM m) (setT name2 (NUM m)) AX) (APPLY f (NUM m)) from w1' to w3'
    compd' = ⇓-trans₂ compc' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM-1st⇓ (NUM m) (setT name2 (NUM m)) AX (APPLY-CS-NUM⇓ (NUM n) w3' 0 name2 g3)))

    concl : ((n < m × steps k7 (setT name1 u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
            → Σ 𝕎· (λ w2' → APPLY (upd name2 f) b ⇓ v from w1' to w2' × getT 0 name1 w2 ≡ getT 0 name2 w2' × ¬Names v)
    concl (inj₁ (ltnm , comp8b)) = chooseT name2 w3' (NUM m) , comph' , g5 , nnv
      where
        compe' : APPLY (upd name2 f) b ⇓ SEQ (setT name2 (NUM m)) (APPLY f (NUM m)) from w1' to w3'
        compe' = ⇓-trans₂ compd' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM<⇓ ltnm (setT name2 (NUM m)) AX w3'))

        comp8c : u' ≡ AX × w4 ≡ chooseT name1 w6 u
        comp8c = setT⇓→ k7 name1 u u' w6 w4 isvu' comp8b

        compf' : APPLY (upd name2 f) b ⇓ SEQ AX (APPLY f (NUM m)) from w1' to chooseT name2 w3' (NUM m)
        compf' = ⇓-trans₂ compe' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (setT⇓ name2 (NUM m) w3'))

        comp5c : steps k4 (APPLY f (NUM m) , chooseT name1 w3 (NUM m)) ≡ (v , w2)
        comp5c = trans (≡𝕎→≡steps k4 (APPLY f (NUM m)) (trans (sym eqchT) (sym (snd comp8c)))) comp5b

        compg' : APPLY (upd name2 f) b ⇓ APPLY f (NUM m) from w1' to chooseT name2 w3' (NUM m)
        compg' = ⇓-trans₂ compf' (SEQ-val⇓ (chooseT name2 w3' (NUM m)) AX (APPLY f (NUM m)) tt)

        g4 : getT 0 name1 (chooseT name1 w3 (NUM m)) ≡ getT 0 name2 (chooseT name2 w3' (NUM m))
        g4 rewrite gc0 name1 w3 m (⊑-compatible· e13 compat1) | gc0 name2 w3' m (⊑-compatible· e13' compat2) = refl

        h6 : steps k4 (APPLY f (NUM m) , chooseT name2 w3' (NUM m)) ≡ (v , chooseT name2 w3' (NUM m)) × chooseT name1 w3 (NUM m) ≡ w2 × ¬Names v
        h6 = ¬Names→steps k4 (chooseT name1 w3 (NUM m)) w2 (chooseT name2 w3' (NUM m)) (APPLY f (NUM m)) v (→∧≡true {¬names f} {¬names (NUM m)} nnf refl) comp5c

        comph' : APPLY (upd name2 f) b ⇓ v from w1' to chooseT name2 w3' (NUM m)
        comph' = ⇓-trans₂ compg' (k4 , fst h6)

        g5 : getT 0 name1 w2 ≡ getT 0 name2 (chooseT name2 w3' (NUM m))
        g5 = ≡→getT≡ (chooseT name1 w3 (NUM m)) w2 0 name1 (getT 0 name2 (chooseT name2 w3' (NUM m))) (proj₁ (snd h6)) g4

        nnv : ¬Names v
        nnv = steps→¬Names k4 (chooseT name1 w3 (NUM m)) w2 (APPLY f (NUM m)) v comp5c (→∧≡true {¬names f} {¬names (NUM m)} nnf refl)

    concl (inj₂ (ltnm , comp8b)) = w3' , compg' , g5 , nnv
      where
        compe' : APPLY (upd name2 f) b ⇓ SEQ AX (APPLY f (NUM m)) from w1' to w3'
        compe' = ⇓-trans₂ compd' (LET⇓ (shiftUp 0 (APPLY f (NUM m))) (IFLT-NUM¬<⇓ (≤⇒≯ ltnm) (setT name2 (NUM m)) AX w3'))

        compf' : APPLY (upd name2 f) b ⇓ APPLY f (NUM m) from w1' to w3'
        compf' = ⇓-trans₂ compe' (SEQ-val⇓ w3' AX (APPLY f (NUM m)) tt)

        eqw64 : w6 ≡ w4
        eqw64 = stepsVal→ᵣ AX u' w6 w4 k7 tt comp8b

        comp5c : steps k4 (APPLY f (NUM m) , w3) ≡ (v , w2)
        comp5c = trans (≡𝕎→≡steps k4 (APPLY f (NUM m)) (trans (trans eqw35 eqw56) eqw64)) comp5b

        h6 : steps k4 (APPLY f (NUM m) , w3') ≡ (v , w3') × w3 ≡ w2 × ¬Names v
        h6 = ¬Names→steps k4 w3 w2 w3' (APPLY f (NUM m)) v (→∧≡true {¬names f} {¬names (NUM m)} nnf refl) comp5c

        compg' : APPLY (upd name2 f) b ⇓ v from w1' to w3'
        compg' = ⇓-trans₂ compf' (k4 , fst h6)

        g5 : getT 0 name1 w2 ≡ getT 0 name2 w3'
        g5 = ≡→getT≡ w3 w2 0 name1 (getT 0 name2 w3') (fst (snd h6)) g1

        nnv : ¬Names v
        nnv = steps→¬Names k4 w3 w2 (APPLY f (NUM m)) v comp5c (→∧≡true {¬names f} {¬names (NUM m)} nnf refl)




differ-refl : (name1 name2 : Name) (f t : Term)
              → ¬names t ≡ true
              → differ name1 name2 f t t
differ-refl name1 name2 f (VAR x) nn = differ-VAR x
differ-refl name1 name2 f NAT nn = differ-NAT
differ-refl name1 name2 f QNAT nn = differ-QNAT
differ-refl name1 name2 f TNAT nn = differ-TNAT
differ-refl name1 name2 f (LT t t₁) nn = differ-LT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (QLT t t₁) nn = differ-QLT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (NUM x) nn = differ-NUM x
differ-refl name1 name2 f (IFLT t t₁ t₂ t₃) nn = differ-IFLT _ _ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₃ (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn))
differ-refl name1 name2 f (SUC t) nn = differ-SUC _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (PI t t₁) nn = differ-PI _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (LAMBDA t) nn = differ-LAMBDA _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (APPLY t t₁) nn = differ-APPLY _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (FIX t) nn = differ-FIX _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (LET t t₁) nn = differ-LET _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (WT t t₁) nn = differ-WT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (SUP t t₁) nn = differ-SUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (DSUP t t₁) nn = differ-DSUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (MT t t₁) nn = differ-MT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (MSUP t t₁) nn = differ-MSUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (DMSUP t t₁) nn = differ-DMSUP _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (SUM t t₁) nn = differ-SUM _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (PAIR t t₁) nn = differ-PAIR _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (SPREAD t t₁) nn = differ-SPREAD _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (SET t t₁) nn = differ-SET _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (ISECT t t₁) nn = differ-ISECT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (TUNION t t₁) nn = differ-TUNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (UNION t t₁) nn = differ-UNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (QTUNION t t₁) nn = differ-QTUNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (INL t) nn = differ-INL _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (INR t) nn = differ-INR _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (DECIDE t t₁ t₂) nn = differ-DECIDE _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
differ-refl name1 name2 f (EQ t t₁ t₂) nn = differ-EQ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
differ-refl name1 name2 f (EQB t t₁ t₂ t₃) nn = differ-EQB _ _ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₃ (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn))
differ-refl name1 name2 f AX nn = differ-AX
differ-refl name1 name2 f FREE nn = differ-FREE
differ-refl name1 name2 f (CHOOSE t t₁) nn = differ-CHOOSE _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (TSQUASH t) nn = differ-TSQUASH _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (TTRUNC t) nn = differ-TTRUNC _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (TCONST t) nn = differ-TCONST _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (SUBSING t) nn = differ-SUBSING _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (PURE) nn = differ-PURE
differ-refl name1 name2 f (DUM t) nn = differ-DUM _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (FFDEFS t t₁) nn = differ-FFDEFS _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (UNIV x) nn = differ-UNIV x
differ-refl name1 name2 f (LIFT t) nn = differ-LIFT _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (LOWER t) nn = differ-LOWER _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (SHRINK t) nn = differ-SHRINK _ _ (differ-refl name1 name2 f t nn)



APPLY-LAMBDA⇓→ : (k : ℕ) {w1 w2 : 𝕎·} {f a v : Term}
                 → isValue v
                 → steps k (APPLY (LAMBDA f) a , w1) ≡ (v , w2)
                 → sub a f ⇓ v from w1 to w2
APPLY-LAMBDA⇓→ 0 {w1} {w2} {f} {a} {v} isv comp rewrite sym (pair-inj₁ comp) | sym (pair-inj₂ comp) = ⊥-elim isv
APPLY-LAMBDA⇓→ (suc k) {w1} {w2} {f} {a} {v} isv comp = k , comp


--differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → differ name1 name2 f (CS name) t → t ≡ CS name
--differ-CSₗ→ {name1} {name2} {name} {f} {.(CS name)} (differ-CS name) = refl


differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (CS name) t
differ-CSₗ→ {name1} {name2} {name} {f} {t} ()


differ-NAMEₗ→ : {name1 name2 name : Name} {f t : Term} → ¬ differ name1 name2 f (NAME name) t
differ-NAMEₗ→ {name1} {name2} {name} {f} {t} ()



map-getT-just→ : (n : ℕ) (name : Name) (w : 𝕎·) (t : Term) (w' : 𝕎·)
                  → Data.Maybe.map (λ t → t , w) (getT n name w) ≡ just (t , w')
                  → w' ≡ w
map-getT-just→ n name w t w' s with getT n name w
... | just u rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
... | nothing = ⊥-elim (¬just≡nothing (sym s))

\end{code}
