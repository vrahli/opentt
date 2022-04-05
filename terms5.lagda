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




--getT0-chooseT : Set(L)
--getT0-chooseT = (name : Name) (w : 𝕎·) (n : ℕ) → getT 0 name (chooseT name w (NUM n)) ≡ just (NUM n)


getT-chooseT : Set(L)
getT-chooseT = (w : 𝕎·) (name : Name) (k : ℕ)
               → compatible· name w Res⊤
               → getT 0 name (chooseT name w (NUM k)) ≡ just (NUM k)



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


∀𝕎-get0-NUM : 𝕎· → Name → Set(lsuc(L))
∀𝕎-get0-NUM w name = ∀𝕎 w (λ w' e → Lift {0ℓ} (lsuc(L)) (Σ ℕ (λ j → getT 0 name w' ≡ just (NUM j))))



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



upd⇓names : (k : ℕ) (f : Term) (name1 name2 : Name) (w1 w1' w2 : 𝕎·) (a b : Term) (v : Term)
            → # f
            → ¬Names f
            → ∀𝕎-get0-NUM w1 name1
            → compatible· name1 w1 Res⊤
            → compatible· name2 w1' Res⊤
            → getT-chooseT
--            → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
--            → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
            → isValue v
            → ((k' : ℕ) → k' < k → ⇓PresDiff f name1 name2 k')
            → getT 0 name1 w1 ≡ getT 0 name2 w1'
            → differ name1 name2 f a b
            → steps k (LET a (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w2)
            → Σ 𝕎· (λ w2' → APPLY (upd name2 f) b ⇓ v from w1' to w2' × getT 0 name1 w2 ≡ getT 0 name2 w2' × ¬Names v)
upd⇓names k f name1 name2 w1 w1' w2 a b v cf nnf gtn compat1 compat2 gc0 isv pd g0 diff comp = concl comp8
  where
    h1 : Σ ℕ (λ k1 → Σ ℕ (λ k2 → Σ 𝕎· (λ w → Σ Term (λ u →
            steps k1 (a , w1) ≡ (u , w)
            × isValue u
            × steps k2 (sub u (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w) ≡ (v , w2)
            × k1 < k
            × k2 < k))))
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

    ltk1 : k1 < k
    ltk1 = fst (snd (snd (snd (snd (snd (snd (snd h1)))))))

    ltk2 : k2 < k
    ltk2 = snd (snd (snd (snd (snd (snd (snd (snd h1)))))))

    comp3 : steps k2 (LET (updGt name1 u) (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w3) ≡ (v , w2)
    comp3 rewrite sym (sub-SEQ-updGt u name1 f cf) = comp2

    e13 : w1 ⊑· w3
    e13 = steps→⊑ k1 a u comp1

    h2 : Σ ℕ (λ k3 → Σ ℕ (λ k4 → Σ 𝕎· (λ w4 → Σ Term (λ u' →
           steps k3 (updGt name1 u , w3) ≡ (u' , w4)
           × isValue u'
           × steps k4 (sub u' (APPLY f (shiftDown 1 (shiftUp 0 (shiftUp 0 u)))) , w4) ≡ (v , w2)
           × k3 < k2
           × k4 < k2))))
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

    ltk3 : k3 < k2
    ltk3 = fst (snd (snd (snd (snd (snd (snd (snd h2)))))))

    ltk4 : k4 < k2
    ltk4 = snd (snd (snd (snd (snd (snd (snd (snd h2)))))))

    h3 : Σ ℕ (λ k5 → Σ ℕ (λ k6 → Σ ℕ (λ k7 → Σ 𝕎· (λ w5 → Σ 𝕎· (λ w6 → Σ ℕ (λ n → Σ ℕ (λ m →
           steps k5 (get0 name1 , w3) ≡ (NUM n , w5)
           × steps k6 (u , w5) ≡ (NUM m , w6)
           × ((n < m × steps k7 (setT name1 u , w6) ≡ (u' , w4)) ⊎ (m ≤ n × steps k7 (AX , w6) ≡ (u' , w4)))
           × k5 < k3
           × k6 < k3
           × k7 < k3)))))))
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

    ltk5 : k5 < k3
    ltk5 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3))))))))))

    ltk6 : k6 < k3
    ltk6 = fst (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))))

    ltk7 : k7 < k3
    ltk7 = snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd (snd h3)))))))))))

    eqm : u ≡ NUM m
    eqm = stepsVal→ₗ u (NUM m) w5 w6 k6 isvu comp7

    eqw56 : w5 ≡ w6
    eqw56 = stepsVal→ᵣ u (NUM m) w5 w6 k6 isvu comp7

    comp1b : steps k1 (a , w1) ≡ (NUM m , w3)
    comp1b rewrite sym eqm = comp1

    h4 : Σ 𝕎· (λ w3' → Σ Term (λ v' →
                b ⇓ v' from w1' to w3' × differ name1 name2 f (NUM m) v' × getT 0 name1 w3 ≡ getT 0 name2 w3'))
    h4 = pd k1 ltk1 w1 w3 w1' a b (NUM m) tt compat1 compat2 gtn diff g0 comp1b

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
        g4 rewrite gc0 w3 name1 m (⊑-compatible· e13 compat1) | gc0 w3' name2 m (⊑-compatible· e13' compat2) = refl

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
differ-refl name1 name2 f (LT t t₁) nn = differ-LT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (QLT t t₁) nn = differ-QLT _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (NUM x) nn = differ-NUM x
differ-refl name1 name2 f (IFLT t t₁ t₂ t₃) nn = differ-IFLT _ _ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn)) (differ-refl name1 name2 f t₃ (∧≡true→4-4 {¬names t} {¬names t₁} {¬names t₂} {¬names t₃} nn))
differ-refl name1 name2 f (PI t t₁) nn = differ-PI _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (LAMBDA t) nn = differ-LAMBDA _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (APPLY t t₁) nn = differ-APPLY _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (FIX t) nn = differ-FIX _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (LET t t₁) nn = differ-LET _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (SUM t t₁) nn = differ-SUM _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (PAIR t t₁) nn = differ-PAIR _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (SPREAD t t₁) nn = differ-SPREAD _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (SET t t₁) nn = differ-SET _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (TUNION t t₁) nn = differ-TUNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (UNION t t₁) nn = differ-UNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (QTUNION t t₁) nn = differ-QTUNION _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (INL t) nn = differ-INL _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (INR t) nn = differ-INR _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (DECIDE t t₁ t₂) nn = differ-DECIDE _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
differ-refl name1 name2 f (EQ t t₁ t₂) nn = differ-EQ _ _ _ _ _ _ (differ-refl name1 name2 f t (∧≡true→1-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₁ (∧≡true→2-3 {¬names t} {¬names t₁} {¬names t₂} nn)) (differ-refl name1 name2 f t₂ (∧≡true→3-3 {¬names t} {¬names t₁} {¬names t₂} nn))
differ-refl name1 name2 f AX nn = differ-AX
differ-refl name1 name2 f FREE nn = differ-FREE
differ-refl name1 name2 f (CHOOSE t t₁) nn = differ-CHOOSE _ _ _ _ (differ-refl name1 name2 f t (∧≡true→ₗ (¬names t) (¬names t₁) nn)) (differ-refl name1 name2 f t₁ (∧≡true→ᵣ (¬names t) (¬names t₁) nn))
differ-refl name1 name2 f (TSQUASH t) nn = differ-TSQUASH _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (TTRUNC t) nn = differ-TTRUNC _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (TCONST t) nn = differ-TCONST _ _ (differ-refl name1 name2 f t nn)
differ-refl name1 name2 f (SUBSING t) nn = differ-SUBSING _ _ (differ-refl name1 name2 f t nn)
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


--differ-CSₗ→ : {name1 name2 name : Name} {f t : Term} → differ name1 name2 f (CS name) t → name ≡ name1 × t ≡ CS name2
--differ-CSₗ→ {name1} {name2} {.name1} {f} {.(CS name2)} differ-CS = refl , refl



map-getT-just→ : (n : ℕ) (name : Name) (w : 𝕎·) (t : Term) (w' : 𝕎·)
                  → Data.Maybe.map (λ t → t , w) (getT n name w) ≡ just (t , w')
                  → w' ≡ w
map-getT-just→ n name w t w' s with getT n name w
... | just u rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = refl
... | nothing = ⊥-elim (¬just≡nothing (sym s))


differ⇓-aux2 : (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name) (w1 w2 w1' w0 : 𝕎·) (a b a' v : Term) (k : ℕ)
               → compatible· name1 w1 Res⊤
               → compatible· name2 w1' Res⊤
               → getT-chooseT
               → ∀𝕎-get0-NUM w1 name1
--               → ∀𝕎 w1 (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
--               → ∀𝕎 w1' (λ w' _ → (m : ℕ) → ∈ℕ w' (APPLY f (NUM m)))
               → differ name1 name2 f a b
               → getT 0 name1 w1 ≡ getT 0 name2 w1'
               → step a w1 ≡ just (a' , w2)
               → steps k (a' , w2) ≡ (v , w0)
               → isValue v
               → ((k' : ℕ) → k' < k → ⇓PresDiff f name1 name2 k')
               → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   a' ⇓ a'' from w2 to w3
                   × b ⇓ b'' from w1' to w3'
                   × differ name1 name2 f a'' b''
                   × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .NAT .NAT a' v k compat1 compat2 gc0 agtn differ-NAT g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NAT , NAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NAT , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .QNAT .QNAT a' v k compat1 compat2 gc0 agtn differ-QNAT g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QNAT , QNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QNAT , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(LT a₁ b₁) .(LT a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-LT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LT a₁ b₁ , LT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LT _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(QLT a₁ b₁) .(QLT a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-QLT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QLT a₁ b₁ , QLT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QLT _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(NUM x) .(NUM x) a' v k compat1 compat2 gc0 agtn (differ-NUM x) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM x , NUM x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-NUM x , g0
-- IFLT
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' v k compat1 compat2 gc0 agtn (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd with is-NUM a₁
... | inj₁ (n , p) rewrite p | differ-NUM→ diff with is-NUM b₁
... |    inj₁ (m , q) rewrite q | differ-NUM→ diff₁ with n <? m
... |       yes r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = c₃ , c₄ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM<⇓ r c₄ d₂ w1' , diff₂ , g0
... |       no r rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = d₁ , d₂ , w1 , w1' , ⇓from-to-refl _ _ , IFLT-NUM¬<⇓ r c₄ d₂ w1' , diff₃ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' v k compat1 compat2 gc0 agtn (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd | inj₁ (n , p) | inj₂ q with step⊎ b₁ w1
... | inj₁ (b₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  IFLT (NUM n) (fst ind) c₃ d₁ ,
  IFLT (NUM n) (fst (snd ind)) c₄ d₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  IFLT-NUM-2nd⇓ n c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
  IFLT-NUM-2nd⇓ n c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-IFLT _ _ _ _ _ _ _ _ (differ-NUM n) (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₂ diff₃ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k b₁' w1''
    hv0 = IFLT-NUM→hasValue k n b₁' c₃ d₁ v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            b₁' ⇓ a'' from w1'' to w3 × b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) b₁ b₂ b₁' (fst hv0) k compat1 compat2 gc0 agtn diff₁ g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFLT-NUM→ n b₁' c₃ d₁ w1'' {k} hv) pd
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(IFLT a₁ b₁ c₃ d₁) .(IFLT a₂ b₂ c₄ d₂) a' v k compat1 compat2 gc0 agtn (differ-IFLT a₁ a₂ b₁ b₂ c₃ c₄ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd | inj₂ p with step⊎ a₁ w1
... | inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  IFLT (fst ind) b₁ c₃ d₁ ,
  IFLT (fst (snd ind)) b₂ c₄ d₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  IFLT-NUM-1st⇓ b₁ c₃ d₁ (fst (snd (snd (snd (snd ind))))) ,
  IFLT-NUM-1st⇓ b₂ c₄ d₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-IFLT _ _ _ _ _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ diff₂ diff₃ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k a₁' w1''
    hv0 = IFLT→hasValue k a₁' b₁ c₃ d₁ v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 gc0 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-IFLT→ a₁' b₁ c₃ d₁ w1'' {k} hv) pd
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- PI
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(PI a₁ b₁) .(PI a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-PI a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PI a₁ b₁ , PI a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PI _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(LAMBDA a) .(LAMBDA b) a' v k compat1 compat2 gc0 agtn (differ-LAMBDA a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LAMBDA a , LAMBDA b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LAMBDA _ _ diff , g0
-- APPLY
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(APPLY a₁ b₁) .(APPLY a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-LAM a₁
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d
  where
    d : Σ Term (λ g' → a₂ ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × a₂ ≡ upd name2 f)
    d = differ-LAMBDAₗ→ diff

    concl : Σ Term (λ g' → a₂ ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × a₂ ≡ upd name2 f)
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub b₁ t ⇓ a'' from w1 to w3 × APPLY a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (inj₁ (g' , e₁ , e₂)) rewrite e₁ =
      sub b₁ t ,
      sub b₂ g' ,
      w1 , w1' ,
      ⇓from-to-refl _ _ , APPLY-LAMBDA⇓ w1' g' b₂ ,
      differ-sub cf e₂ diff₁ ,
      g0
    concl (inj₂ (e₁ , e₂)) rewrite e₁ | e₂ | sub-upd name1 f b₁ cf =
      v , v , w0 , fst hv2 , (k , hv1) , fst (snd hv2) , differ-refl name1 name2 f v (snd (snd (snd hv2))) , fst (snd (snd hv2))
      where
        hv0 : steps k (sub b₁ (updBody name1 f) , w1) ≡ (v , w0)
        hv0 rewrite e₁ = hv

        hv1 : steps k (LET b₁ (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w0)
        hv1 rewrite sym (sub-upd name1 f b₁ cf) = hv0

        hv2 : Σ 𝕎· (λ w2' → APPLY (upd name2 f) b₂ ⇓ v from w1' to w2' × getT 0 name1 w0 ≡ getT 0 name2 w2' × ¬Names v)
        hv2 = upd⇓names k f name1 name2 w1 w1' w0 b₁ b₂ v cf nnf agtn compat1 compat2 gc0 isvv pd g0 diff₁ hv1
... | inj₂ x with is-CS a₁
... |    inj₁ (name , p) rewrite p = {-- | fst (differ-CSₗ→ diff) | snd (differ-CSₗ→ diff) with is-NUM b₁
... |       inj₁ (n₁ , q) rewrite q | differ-NUM→ diff₁ | map-getT-just→ n₁ name1 w1 a' w2 s = a' , a' , w1 , w1' , (0 , refl) , {!(1 , step-APPLY-CS a' w1' n₁) , ?!} --⊥-elim (differ-CSₗ→ diff)
... |       inj₂ q = {!!} --} ⊥-elim (differ-CSₗ→ diff)
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(APPLY a₁ b₁) .(APPLY a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-APPLY a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd | inj₂ x | inj₂ name with step⊎ a₁ w1
... | inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  APPLY (fst ind) b₁ ,
  APPLY (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  APPLY⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  APPLY⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-APPLY _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k a₁' w1''
    hv0 = APPLY→hasValue k a₁' b₁ v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 gc0 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-APPLY→ a₁' b₁ w1'' {k} hv) pd
... | inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- FIX
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(FIX a) .(FIX b) a' v k compat1 compat2 gc0 agtn (differ-FIX a b diff) g0 s hv isvv pd with is-LAM a
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d --ret (sub (FIX (LAMBDA t)) t) w
  where
    d : Σ Term (λ g' → b ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × b ≡ upd name2 f)
    d = differ-LAMBDAₗ→ diff

    concl : Σ Term (λ g' → b ≡ LAMBDA g' × differ name1 name2 f t g') ⊎ (t ≡ updBody name1 f × b ≡ upd name2 f)
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub (FIX (LAMBDA t)) t ⇓ a'' from w1 to w3 × FIX b ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (inj₁ (g' , e₁ , e₂)) rewrite e₁ =
      sub (FIX (LAMBDA t)) t ,
      sub (FIX (LAMBDA g')) g' ,
      w1 , w1' ,
      ⇓from-to-refl _ _ ,
      FIX-LAMBDA⇓ w1' g' ,
      differ-sub cf e₂ (differ-FIX _ _ (differ-LAMBDA _ _ e₂)) ,
      g0
    concl (inj₂ (e₁ , e₂)) rewrite e₁ | e₂ | sub-upd name1 f (FIX (upd name1 f)) cf =
      v , v , w0 , fst hv2 , (k , hv1) , (⇓-trans₂ (FIX-LAMBDA⇓ w1' (updBody name2 f)) cs) , differ-refl name1 name2 f v (snd (snd (snd hv2))) , fst (snd (snd hv2))
--  (fst (snd hv2))
      where
        hv0 : steps k (sub (FIX (upd name1 f)) (updBody name1 f) , w1) ≡ (v , w0)
        hv0 rewrite e₁ = hv

        hv1 : steps k (LET (FIX (upd name1 f)) (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w0)
        hv1 rewrite sym (sub-upd name1 f (FIX (upd name1 f)) cf) = hv0

        df : differ name1 name2 f (FIX (upd name1 f)) (FIX (upd name2 f))
        df = differ-FIX _ _ differ-upd

        hv2 : Σ 𝕎· (λ w2' → APPLY (upd name2 f) (FIX (upd name2 f)) ⇓ v from w1' to w2' × getT 0 name1 w0 ≡ getT 0 name2 w2' × ¬Names v)
        hv2 = upd⇓names k f name1 name2 w1 w1' w0 (FIX (upd name1 f)) (FIX (upd name2 f)) v cf nnf agtn compat1 compat2 gc0 isvv pd g0 df hv1

        cs : sub (FIX (upd name2 f)) (updBody name2 f) ⇓ v from w1' to (fst hv2)
        cs = APPLY-LAMBDA⇓→ (fst (fst (snd hv2))) isvv (snd (fst (snd hv2)))
... | inj₂ x with step⊎ a w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  FIX (fst ind) ,
  FIX (fst (snd ind)) ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  FIX⇓ (fst (snd (snd (snd (snd ind))))) ,
  FIX⇓ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-FIX _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k a₁' w1''
    hv0 = FIX→hasValue k a₁' v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × b ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a b a₁' (fst hv0) k compat1 compat2 gc0 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-FIX→ a₁' w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- LET
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(LET a₁ b₁) .(LET a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-LET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with isValue⊎ a₁
... | inj₁ x rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  sub a₁ b₁ , sub a₂ b₂ , w1 , w1' ,
  ⇓from-to-refl _ _ , LET-val⇓ w1' a₂ b₂ isv , differ-sub cf diff₁ diff , g0
  where
    isv : isValue a₂
    isv = differ-isValue→ diff x
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  LET (fst ind) b₁ ,
  LET (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  LET⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  LET⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-LET _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k a₁' w1''
    hv0 = LET→hasValue k a₁' b₁ v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 gc0 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-LET→ a₁' b₁ w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SUM
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(SUM a₁ b₁) .(SUM a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-SUM a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUM a₁ b₁ , SUM a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUM _ _ _ _ diff diff₁ , g0
-- PAIR
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(PAIR a₁ b₁) .(PAIR a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-PAIR a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-PAIR _ _ _ _ diff diff₁ , g0
-- SPREAD
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-SPREAD a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-PAIR a₁
... | inj₁ (u₁ , u₂ , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  concl d
  where
    d : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ PAIR u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
    d = differ-PAIRₗ→ diff

    concl : Σ Term (λ u' → Σ Term (λ v' → a₂ ≡ PAIR u' v' × differ name1 name2 f u₁ u' × differ name1 name2 f u₂ v'))
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub u₂ (sub u₁ b₁) ⇓ a'' from w1 to w3 × SPREAD a₂ b₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (u' , v' , e , d1 , d2) rewrite e =
      sub u₂ (sub u₁ b₁) , sub v' (sub u' b₂) , w1 , w1' ,
      ⇓from-to-refl _ _ ,
      SPREAD-PAIR⇓ w1' u' v' b₂ ,
      differ-sub cf (differ-sub cf diff₁ d1) d2 ,
      g0
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  SPREAD (fst ind) b₁ ,
  SPREAD (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  SPREAD⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  SPREAD⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-SPREAD _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k a₁' w1''
    hv0 = SPREAD→hasValue k a₁' b₁ v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 gc0 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-SPREAD→ a₁' b₁ w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- SET
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(SET a₁ b₁) .(SET a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-SET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SET a₁ b₁ , SET a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SET _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(TUNION a₁ b₁) .(TUNION a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-TUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TUNION _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(UNION a₁ b₁) .(UNION a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-UNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNION a₁ b₁ , UNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNION _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(QTUNION a₁ b₁) .(QTUNION a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-QTUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-QTUNION _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(INL a) .(INL b) a' v k compat1 compat2 gc0 agtn (differ-INL a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INL a , INL b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INL _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(INR a) .(INR b) a' v k compat1 compat2 gc0 agtn (differ-INR a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INR a , INR b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-INR _ _ diff , g0
-- DECIDE
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(DECIDE a₁ b₁ c₃) .(DECIDE a₂ b₂ c₄) a' v k compat1 compat2 gc0 agtn (differ-DECIDE a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv isvv pd with is-INL a₁
... | inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  concl d
  where
    d : Σ Term (λ u' → a₂ ≡ INL u' × differ name1 name2 f u u')
    d = differ-INLₗ→ diff

    concl : Σ Term (λ u' → a₂ ≡ INL u' × differ name1 name2 f u u')
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub u b₁ ⇓ a'' from w1 to w3 × DECIDE a₂ b₂ c₄ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (u' , e , d1) rewrite e =
      sub u b₁ , sub u' b₂ , w1 , w1' ,
      ⇓from-to-refl _ _ ,
      DECIDE-INL⇓ w1' u' _ _ ,
      differ-sub cf diff₁ d1 ,
      g0
... | inj₂ x with is-INR a₁
... |    inj₁ (u , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  concl d
  where
    d : Σ Term (λ u' → a₂ ≡ INR u' × differ name1 name2 f u u')
    d = differ-INRₗ→ diff

    concl : Σ Term (λ u' → a₂ ≡ INR u' × differ name1 name2 f u u')
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub u c₃ ⇓ a'' from w1 to w3 × DECIDE a₂ b₂ c₄ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (u' , e , d1) rewrite e =
      sub u c₃ , sub u' c₄ , w1 , w1' ,
      ⇓from-to-refl _ _ ,
      DECIDE-INR⇓ w1' u' _ _ ,
      differ-sub cf diff₂ d1 ,
      g0
... |    inj₂ y with step⊎ a₁ w1
... |       inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  DECIDE (fst ind) b₁ c₃ ,
  DECIDE (fst (snd ind)) b₂ c₄ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  DECIDE⇓ b₁ c₃ (fst (snd (snd (snd (snd ind))))) ,
  DECIDE⇓ b₂ c₄ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-DECIDE _ _ _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ diff₂ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k a₁' w1''
    hv0 = DECIDE→hasValue k a₁' b₁ c₃ v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 gc0 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-DECIDE→ a₁' b₁ c₃ w1'' {k} hv) pd
... |       inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- EQ
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(EQ a₁ b₁ c₃) .(EQ a₂ b₂ c₄) a' v k compat1 compat2 gc0 agtn (differ-EQ a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQ a₁ b₁ c₃ , EQ a₂ b₂ c₄ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-EQ _ _ _ _ _ _ diff diff₁ diff₂ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .AX .AX a' v k compat1 compat2 gc0 agtn differ-AX g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = AX , AX , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-AX , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .FREE .FREE a' v k compat1 compat2 gc0 agtn differ-FREE g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FREE , FREE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FREE , g0
--differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(CS name1) .(CS name2) a' v k compat1 compat2 gc0 agtn differ-CS g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = CS name1 , CS name2 , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-CS , g0
-- CHOOSE
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd with is-NAME a₁
... | inj₁ (name , p) rewrite p = ⊥-elim (differ-NAMEₗ→ diff)
... | inj₂ x with step⊎ a₁ w1
... |    inj₁ (a₁' , w1'' , z) rewrite z | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  CHOOSE (fst ind) b₁ ,
  CHOOSE (fst (snd ind)) b₂ ,
  fst (snd (snd ind)) ,
  fst (snd (snd (snd ind))) ,
  CHOOSE⇓ b₁ (fst (snd (snd (snd (snd ind))))) ,
  CHOOSE⇓ b₂ (fst (snd (snd (snd (snd (snd ind)))))) ,
  differ-CHOOSE _ _ _ _ (fst (snd (snd (snd (snd (snd (snd ind))))))) diff₁ ,
  snd (snd (snd (snd (snd (snd (snd ind))))))
  where
    hv0 : hasValueℕ k a₁' w1''
    hv0 = CHOOSE→hasValue k a₁' b₁ v w1'' w0 hv isvv

    ind : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
            a₁' ⇓ a'' from w1'' to w3 × a₂ ⇓ b'' from w1' to w3' × differ name1 name2 f a'' b'' × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    ind = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' (fst (snd hv0)) a₁ a₂ a₁' (fst hv0) k compat1 compat2 gc0 agtn diff g0 z (fst (snd (snd hv0))) (snd (snd (snd hv0))) pd -- (hasValue-CHOOSE→ a₁' b₁ w1'' {k} hv) pd
... |    inj₂ z rewrite z = ⊥-elim (¬just≡nothing (sym s))
-- IFC0
--differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(IFC0 a₁ b₁ c₃) .(IFC0 a₂ b₂ c₄) a' v k compat1 compat2 gc0 agtn (differ-IFC0 a₁ a₂ b₁ b₂ c₃ c₄ diff diff₁ diff₂) g0 s hv isvv pd = {!!}
-- TSQUASH
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(TSQUASH a) .(TSQUASH b) a' v k compat1 compat2 gc0 agtn (differ-TSQUASH a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TSQUASH a , TSQUASH b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TSQUASH _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(TTRUNC a) .(TTRUNC b) a' v k compat1 compat2 gc0 agtn (differ-TTRUNC a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TTRUNC a , TTRUNC b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TTRUNC _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(TCONST a) .(TCONST b) a' v k compat1 compat2 gc0 agtn (differ-TCONST a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TCONST a , TCONST b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-TCONST _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(SUBSING a) .(SUBSING b) a' v k compat1 compat2 gc0 agtn (differ-SUBSING a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUBSING a , SUBSING b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SUBSING _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(DUM a) .(DUM b) a' v k compat1 compat2 gc0 agtn (differ-DUM a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = DUM a , DUM b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-DUM _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) a' v k compat1 compat2 gc0 agtn (differ-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-FFDEFS _ _ _ _ diff diff₁ , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(UNIV x) .(UNIV x) a' v k compat1 compat2 gc0 agtn (differ-UNIV x) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNIV x , UNIV x , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-UNIV x , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(LIFT a) .(LIFT b) a' v k compat1 compat2 gc0 agtn (differ-LIFT a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LIFT a , LIFT b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LIFT _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(LOWER a) .(LOWER b) a' v k compat1 compat2 gc0 agtn (differ-LOWER a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LOWER a , LOWER b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-LOWER _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(SHRINK a) .(SHRINK b) a' v k compat1 compat2 gc0 agtn (differ-SHRINK a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SHRINK a , SHRINK b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ-SHRINK _ _ diff , g0
differ⇓-aux2 f cf nnf name1 name2 w1 w2 w1' w0 .(upd name1 f) .(upd name2 f) a' v k compat1 compat2 gc0 agtn differ-upd g0 s hv isvv pd
  rewrite stepVal (upd name1 f) w1 tt | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) =
  upd name1 f , upd name2 f , w1 , w1' , (0 , refl) , (0 , refl) , differ-upd , g0


steps-val-suc : (k : ℕ) (a v : Term) (w1 w2 : 𝕎·)
                → isValue v
                → steps k (a , w1) ≡ (v , w2)
                → steps (suc k) (a , w1) ≡ (v , w2)
steps-val-suc 0 a v w1 w2 isv s
  rewrite sym (pair-inj₁ s)
        | sym (pair-inj₂ s) = stepsVal a w1 1 isv
steps-val-suc (suc k) a v w1 w2 isv s with step⊎ a w1
... | inj₁ (a' , w1' , z) rewrite z = steps-val-suc k a' v w1' w2 isv s
... | inj₂ z rewrite z = s


steps⇓-decomp : (k k' : ℕ) (a b v : Term) (w1 w2 w3 : 𝕎·)
                → steps k (a , w1) ≡ (v , w2)
                → steps k' (a , w1) ≡ (b , w3)
                → isValue v
                → steps k (b , w3) ≡ (v , w2)
steps⇓-decomp 0 k' a b v w1 w2 w3 s comp isv
  rewrite sym (pair-inj₁ s)
        | sym (pair-inj₂ s)
        | stepsVal a w1 k' isv
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = refl
steps⇓-decomp (suc k) 0 a b v w1 w2 w3 s comp isv
  rewrite sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp) = s
steps⇓-decomp (suc k) (suc k') a b v w1 w2 w3 s comp isv with step⊎ a w1
... | inj₁ (a' , w1' , z)
  rewrite z = steps-val-suc k b v w3 w2 isv c
  where
    c : steps k (b , w3) ≡ (v , w2)
    c = steps⇓-decomp k k' a' b v w1' w2 w3 s comp isv
... | inj₂ z
  rewrite z
        | sym (pair-inj₁ comp)
        | sym (pair-inj₂ comp)
        | sym (pair-inj₁ s)
        | sym (pair-inj₂ s) = stepsVal a w1 (suc k) isv



⇓→⊑ : (a b : Term) {w w' : 𝕎·} → a ⇓ b from w to w' → w ⊑· w'
⇓→⊑ a b {w} {w'} (n , comp) = steps→⊑ n a b comp


step→⇓ : {a b : Term} {w1 w2 : 𝕎·}
              → step a w1 ≡ just (b , w2)
              → a ⇓ b from w1 to w2
step→⇓ {a} {b} {w1} {w2} comp = 1 , c
  where
    c : steps 1 (a , w1) ≡ (b , w2)
    c rewrite comp = refl


differ⇓-aux : (gc0 : getT-chooseT) (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name) (n : ℕ)
              (ind : (n' : ℕ) → n' < n → ⇓PresDiff f name1 name2 n')
              → ⇓PresDiff f name1 name2 n
differ⇓-aux gc0 f cf nnf name1 name2 0 ind w1 w2 w1' a b v isv compat1 compat2 gt0 diff g0 comp rewrite pair-inj₁ comp | pair-inj₂ comp =
  w1' , b , (0 , refl) , diff , g0
differ⇓-aux gc0 f cf nnf name1 name2 (suc n) ind w1 w2 w1' a b v isv compat1 compat2 gt0 diff g0 comp with step⊎ a w1
... | inj₁ (a' , w1'' , z) rewrite z =
  fst e , fst (snd e) , (⇓-trans₂ (fst (snd (snd (snd (snd (snd c)))))) (fst (snd (snd e)))) ,
  fst (snd (snd (snd e))) , snd (snd (snd (snd e)))
  where
    c : Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   a' ⇓ a'' from w1'' to w3
                   × b ⇓ b'' from w1' to w3'
                   × differ name1 name2 f a'' b''
                   × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    c = differ⇓-aux2 f cf nnf name1 name2 w1 w1'' w1' w2 a b a' v n compat1 compat2 gc0 gt0 diff g0 z comp isv λ k i → ind k (<-trans i (n<1+n n))

    d : steps n (fst c , fst (snd (snd c))) ≡ (v , w2)
    d = steps⇓-decomp
          n (proj₁ (proj₁ (snd (snd (snd (snd c)))))) a'
          (proj₁ c) v w1'' w2 (proj₁ (snd (snd c))) comp
          (snd (fst (snd (snd (snd (snd c)))))) isv

    e₁ : w1 ⊑· fst (snd (snd c))
    e₁ = ⇓→⊑ a (fst c) (step-⇓-from-to-trans z (fst (snd (snd (snd (snd c))))))

    e₂ : w1' ⊑· fst (snd (snd (snd c)))
    e₂ = ⇓→⊑ b (fst (snd c)) (fst (snd (snd (snd (snd (snd c))))))

    e : Σ 𝕎· (λ w2' → Σ Term (λ v' →
          fst (snd c) ⇓ v' from fst (snd (snd (snd c))) to w2' × differ name1 name2 f v v' × getT 0 name1 w2 ≡ getT 0 name2 w2'))
    e = ind n ≤-refl (fst (snd (snd c))) w2 (fst (snd (snd (snd c)))) (fst c) (fst (snd c)) v isv
            (⊑-compatible· e₁ compat1) (⊑-compatible· e₂ compat2)
            (∀𝕎-mon (⇓→⊑ a (proj₁ c) {w1} {proj₁ (snd (snd c))} (⇓-trans₂ (step→⇓ z) (fst (snd (snd (snd (snd c))))))) gt0) (fst (snd (snd (snd (snd (snd (snd c))))))) (snd (snd (snd (snd (snd (snd (snd c))))))) d
... | inj₂ z rewrite z | pair-inj₁ comp | pair-inj₂ comp = w1' , b , (0 , refl) , diff , g0


differ⇓ : (gc0 : getT-chooseT) (f : Term) (cf : # f) (nn : ¬Names f) (name1 name2 : Name) (n : ℕ) → ⇓PresDiff f name1 name2 n
differ⇓ gc0 f cf nnf name1 name2 = <ℕind _ (differ⇓-aux gc0 f cf nnf name1 name2)


\end{code}
