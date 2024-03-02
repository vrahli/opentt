\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}

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
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
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
open import compatible
open import progress
open import getChoice
open import newChoice
open import freeze
open import mod
open import choiceExt
open import choiceVal


-- An instance with beth bars (inBethBar-Bar) and references
-- As oppposed to modInstanceBethRef, which relies on choices of nats, this one relies on bools

module modInstanceBethRef3 (E0 : Extensionality 0ℓ 0ℓ)
       where


open import encoding3(E0)

open import worldInstanceRef3(E0)

W : PossibleWorlds
W = PossibleWorldsRef

C : Choice
C = choiceRef

K : Compatible W C
K = compatibleREF

P : Progress W C K
P = progressREF

open import barBeth(W)(C)(K)(P)

M : Mod W
M = inBethBar-Mod

G : GetChoice W C K
G = getChoiceRef

N : NewChoice W C K G
N = newChoiceRef

F : Freeze W C K P G N
F = freezeREF

X : ChoiceExt W C
X = choiceExtRef

V : ChoiceVal W C K G X N enc
V = choiceValRef

open import worldDef(W)
open import bar(W)
open import mod(W)
--open import barOpen(W)
open import choiceDef{1ℓ}(C)
open import compatibleDef(W)(C)(K)
open import progressDef(W)(C)(K)(P)
open import getChoiceDef(W)(C)(K)(G)
open import choiceExtDef(W)(C)(K)(G)(X)
open import choiceValDef(W)(C)(K)(G)(X)(N)(enc)(V)
open import newChoiceDef(W)(C)(K)(G)(N)
open import freezeDef(W)(C)(K)(P)(G)(N)(F)

--open import barBeth(W)(C)(K)(P)
open import barI(W)(M)--(C)(K)(P)
open import computation(W)(C)(K)(G)(X)(N)(enc)

open import forcing(W)(M)(C)(K)(G)(X)(N)(enc)
open import props1(W)(M)(C)(K)(G)(X)(N)(enc)
open import props2(W)(M)(C)(K)(G)(X)(N)(enc)
  using ()
open import props3(W)(M)(C)(K)(G)(X)(N)(enc)
  using (isTypeBOOL₀!→  ; →equalInType-BOOL₀!-INR ; →equalInType-BOOL₀!-INL ; equalInType-BOOL₀!→ ; →equalInType-BOOL₀! ;
         equalTerms-pres-#⇛-left-BOOL₀! ; equalTerms-pres-#⇛-left-rev-BOOL₀!)


{--
progressing→ΣgetCs≤ : {w : 𝕎·} {c : chain w} {r : Res} (n : Name) (m : ℕ)
                    → compatible· n w r
                    → progressing {w} c
                    → Σ ℕ (λ k → Σ ℂ· (λ l → getRef n (chain.seq c k) ≡ just (mkref n l r) × m < length l))
progressing→ΣgetCs≤ {w} {c} {r} n 0 comp prog = k , (fst i2 ++ fst i3) , fst (snd i3) , len
  where
    z : Σ ℕ (λ m → 0 < m × progress· n (chain.seq c 0) (chain.seq c m))
    z = prog n 0 (⊑-compatible· (chain.init c) comp)

    k : ℕ
    k = fst z

    ltk : 0 < k
    ltk = fst (snd z)

    i1 : Σ (List ℂ·) (λ l → ∈world (mkcs n l r) w × resSatCs 0 l r)
    i1 = comp

    i2 : Σ (List ℂ·) (λ l → ∈world (mkcs n l r) (chain.seq c 0) × resSatCs 0 l r)
    i2 = ⊑-compatible· (chain.init c) comp

    i3 : Σ (List ℂ·) (λ l → ∈world (mkcs n (fst i2 ++ l) r) (chain.seq c k) × 0 < length l)
    i3 = snd (snd z) (fst i2) r (fst (snd i2))

    len : 0 < length (proj₁ i2 ++ proj₁ i3)
    len rewrite length-++ (fst i2) {fst i3} = <-≤-trans (snd (snd i3)) (m≤n+m _ _)
progressing→ΣgetCs≤ {w} {c} {r} n (suc m) comp prog = k' , l ++ fst i1 , (fst (snd i1)) , len'
  where
    ind : Σ ℕ (λ k → Σ (List ℂ·) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l r) × m < length l))
    ind = progressing→ΣgetCs≤ {w} {c} n m comp prog

    k : ℕ
    k = fst ind

    l : List ℂ·
    l = fst (snd ind)

    g : getCs n (chain.seq c k) ≡ just (mkcs n l r)
    g = fst (snd (snd ind))

    len : m < length l
    len = snd (snd (snd ind))

    p : Σ ℕ (λ m → k < m × progress· n (chain.seq c k) (chain.seq c m))
    p = prog n k (⊑-compatible· (chain⊑n k c) comp)

    k' : ℕ
    k' = fst p

    ltk' : k < k'
    ltk' = fst (snd p)

    i1 : Σ (List ℂ·) (λ l' → ∈world (mkcs n (l ++ l') r) (chain.seq c k') × 0 < length l')
    i1 = snd (snd p) l r g

    len' : suc m < length (l ++ proj₁ i1)
    len' rewrite length-++ l {fst i1} | suc-+1 m = <-≤-trans (+-monoˡ-< 1 len) (+-monoʳ-≤ (length l) (snd (snd i1)))
--}


IS𝔹-ℕ : (w : 𝕎·) (r : Res) (n : Name) (m : ℕ) (comp : compatible· n w r) → IS𝔹 w
IS𝔹-ℕ w r n m comp =
  mk𝔹 bar bars ext mon
  where
    bar : 𝕎· → Set₁
    bar w' = w ⊑· w' × Σ ℂ· (λ v → getRef n w' ≡ just (cell n r (just v)))

    bars : (c : pchain w) → BarredChain bar (pchain.c c)
    bars (mkPChain c p) = mkBarredChain {!!} {!!} {!!} {!!} {-- (chain.seq c (fst z)) b (fst z) (⊑-refl· _)
      where
        z : Σ ℕ (λ k → Σ (List ℂ·) (λ l → getCs n (chain.seq c k) ≡ just (mkcs n l r) × m < length l))
        z = progressing→ΣgetCs≤ {w} {c} n m comp p

        b : bar (chain.seq c (fst z))
        b = chain⊑n (fst z) c , snd z --fst (snd z) , fst (snd (snd z)) , snd (snd (snd z))
--}

    ext : {w' : 𝕎·} → bar w' → w ⊑· w'
    ext {w'} (e , v , g) = e

    mon : {w1 w2 : 𝕎·} → w1 ⊑· w2 → bar w1 → bar w2
    mon {w1} {w2} e (e' , v , g)
      with ⊑-pres-getRef {w1} {w2} {n} {r} {just v} e g
    ... | just v' , g' , s' , f' rewrite sym f' = ⊑-trans· e' e , v , g'
    ... | nothing , g' , s' , f' = ⊑-trans· e' e , v , ⊥-elim f'


\end{code}


Typeℂ₀₁-beth-ref : CTerm
Typeℂ₀₁-beth-ref = #BOOL₀!


Typeℂ₀₁-isType-beth-bar : (u : ℕ) (w : 𝕎·) → isType u w Typeℂ₀₁-beth-ref
Typeℂ₀₁-isType-beth-bar u w = isTypeBOOL₀!→ u w


ℂ₀∈Typeℂ₀₁-beth-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-ref Cℂ₀
ℂ₀∈Typeℂ₀₁-beth-ref u w = →equalInType-BOOL₀!-INL u w #AX #AX


ℂ₁∈Typeℂ₀₁-beth-ref : (u : ℕ) (w : 𝕎·) → ∈Type u w Typeℂ₀₁-beth-ref Cℂ₁
ℂ₁∈Typeℂ₀₁-beth-ref u w = →equalInType-BOOL₀!-INR u w #AX #AX


isvalue-choice : (c : ℂ·) → #isValue (ℂ→C· c)
isvalue-choice true = tt
isvalue-choice false = tt


{--ℂ→C→∼ℂ-beth-ref : {w : 𝕎·} {c c1 c2 : ℂ·} → ℂ→C· c1 #⇓ ℂ→C· c2 at w → ∼C w c1 c → ∼C w c2 c
ℂ→C→∼ℂ-beth-ref {w} {c} {c1} {c2} comp sim
  rewrite sym (#NUMinj (#compVal comp (isvalue-choice c1))) -- (∼vals→isValue₁ sim)
  = sim--}


{--
isValueℂ₀-beth-ref : isValue Tℂ₀
isValueℂ₀-beth-ref = tt


isValueℂ₁-beth-ref : isValue Tℂ₁
isValueℂ₁-beth-ref = tt


ℂ₀≠ℂ₁-beth-ref : ¬ Cℂ₀ ≡ Cℂ₁
ℂ₀≠ℂ₁-beth-ref ()
--}


ℕ→B : ℕ → Bool
ℕ→B 0 = true
ℕ→B (suc _) = false



#⇓-true : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓ ℂ→C· c at w
          → a #⇓ #INL x at w
          → c ≡ true
#⇓-true w a x true c₁ c₂ = refl
#⇓-true w a x false c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INL x ≡ #BFALSE
    z ()



#⇓-false : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓ ℂ→C· c at w
          → a #⇓ #INR x at w
          → c ≡ false
#⇓-false w a x false c₁ c₂ = refl
#⇓-false w a x true c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INR x ≡ #BTRUE
    z ()



#⇓!-true : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓! ℂ→C· c at w
          → a #⇓! #INL x at w
          → c ≡ true
#⇓!-true w a x true c₁ c₂ = refl
#⇓!-true w a x false c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓!-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INL x ≡ #BFALSE
    z ()



#⇓!-false : (w : 𝕎·) (a x : CTerm) (c : ℂ·)
          → a #⇓! ℂ→C· c at w
          → a #⇓! #INR x at w
          → c ≡ false
#⇓!-false w a x false c₁ c₂ = refl
#⇓!-false w a x true c₁ c₂ = ⊥-elim (z (CTerm≡ (⇓!-val-det tt tt c₂ c₁)))
  where
    z : ¬ #INR x ≡ #BTRUE
    z ()



∈Typeℂ₀₁→-beth-ref : (i : ℕ) (w : 𝕎·) (a b : CTerm) → equalInType i w Typeℂ₀₁-beth-ref a b → □· w (λ w' _ → #weakℂEq w' a b)
∈Typeℂ₀₁→-beth-ref i w a b eqi = Mod.∀𝕎-□Func M aw (equalInType-BOOL₀!→ i w a b eqi)
  where
    aw : ∀𝕎 w (λ w' e' → #strongBool! w' a b → #weakℂEq w' a b)
    aw w1 e1 (x , y , inj₁ (d₁ , d₂)) w2 e2 = lift j --j
      where
      j : (c₁ c₂ : ℂ·) → ⌜ a ⌝ ⇓! ℂ→T c₁ at w2 → ⌜ b ⌝ ⇓! ℂ→T c₂ at w2 → ∼C! w2 (ℂ→C· c₁) (ℂ→C· c₂)
      j c₁ c₂ comp₁ comp₂
        rewrite #⇓!-true w2 a x c₁ comp₁ (lower (d₁ w2 e2))
              | #⇓!-true w2 b y c₂ comp₂ (lower (d₂ w2 e2)) = ∼C!-refl {w2} {#BTRUE}
    aw w1 e1 (x , y , inj₂ (d₁ , d₂)) w2 e2 = lift j --j
      where
      j : (c₁ c₂ : ℂ·) → ⌜ a ⌝ ⇓! ℂ→T c₁ at w2 → ⌜ b ⌝ ⇓! ℂ→T c₂ at w2 → ∼C! w2 (ℂ→C· c₁) (ℂ→C· c₂)
      j c₁ c₂ comp₁ comp₂
        rewrite #⇓!-false w2 a x c₁ comp₁ (lower (d₁ w2 e2))
              | #⇓!-false w2 b y c₂ comp₂ (lower (d₂ w2 e2)) = ∼C!-refl {w2} {#BFALSE}


□·-choice-beth-ref0 : (w : 𝕎·) (c : Name) (m : ℕ) (r : Res)
                    → compatible· c w r
                    → □· w (λ w' _ → Σ ℂ· (λ t → ·ᵣ r m t × ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (getChoice· m c w'' ≡ just t))))
□·-choice-beth-ref0 w c m r (v , i , sat) = trivialIS𝔹 w , j -- this is not the correct bar
  where
    j : inIS𝔹 (trivialIS𝔹 w) (λ w' _ → Σ ℂ· (λ t → ·ᵣ r m t × ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (getChoice· m c w'' ≡ just t))))
    j {w1} e1 b w2 e2 z = {!!}
-- w3 e3 = {!!}
{-- rewrite fst (snd (snd (⊑-pres-getRef (⊑-trans· z e3) i))) =
      lift (fst (⊑-pres-getRef (⊑-trans· z e3) i) ,
            refl ,
            getRefChoiceCompatible
              c r w3 m
              (fst (⊑-pres-getRef (⊑-trans· z e3) i))
              (⊑-compatibleRef (⊑-trans· z e3) (v , i , sat))
              gc)
      where
        gc : getRefChoice m c w3 ≡ just (fst (⊑-pres-getRef (⊑-trans· z e3) i))
        gc rewrite fst (snd (snd (⊑-pres-getRef (⊑-trans· z e3) i))) = refl
--}


□·-choice-beth-ref : (w : 𝕎·) (c : Name) (m : ℕ) (r : Res)
                    → compatible· c w r
                    → □· w (λ w' _ → ∀𝕎 w' (λ w'' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
□·-choice-beth-ref w c m r comp = Mod.∀𝕎-□Func M aw (□·-choice-beth-ref0 w c m r comp)
  where
  aw : ∀𝕎 w (λ w' e' → Σ ℂ· (λ t → ·ᵣ r m t × ∀𝕎 w' (λ w'' _ → Lift 2ℓ (getChoice· m c w'' ≡ just t)))
                     → ∀𝕎 w' (λ w'' _ → Lift 2ℓ (Σ ℂ· (λ t → getChoice· m c w'' ≡ just t × ·ᵣ r m t))))
  aw w1 e1 (t , r , h) w2 e2 = lift (t , lower (h w2 e2) , r)


getChoice→weakℂ₀₁M : (w : 𝕎·) (n : ℕ) (c : Name)
                   → ∀𝕎 w (λ w' _ → Lift {0ℓ} (2ℓ) (Σ ℂ· (λ t → getChoice· n c w' ≡ just t × ·ᵣ Resℂ₀₁ n t)))
                   → weakℂ₀₁M w (getT n c)
getChoice→weakℂ₀₁M w n c h w1 e1 with lower (h w1 e1)
... | t , gc , r rewrite gc with r
... |  inj₁ x rewrite x = lift (BTRUE , refl , inj₁ (⇓!-refl BTRUE w1))
... |  inj₂ x rewrite x = lift (BFALSE , refl , inj₂ (⇓!-refl BFALSE w1))


→∈Typeℂ₀₁-beth-ref : (i : ℕ) {w : 𝕎·} (n : ℕ) {c : Name}
                   → compatible· c w Resℂ₀₁ --□· w (λ w' _ → weakℂ₀₁M w' (getT n c))
                   → ∈Type i w Typeℂ₀₁-beth-ref (#APPLY (#CS c) (#NUM n))
→∈Typeℂ₀₁-beth-ref i {w} n {c} h =
  →equalInType-BOOL₀!
    i w (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n))
    (Mod.∀𝕎-□Func M aw (□·-choice-beth-ref0 w c n Resℂ₀₁ h))
  where
    aw : ∀𝕎 w (λ w' e' → Σ ℂ· (λ t → ·ᵣ Resℂ₀₁ n t × ∀𝕎 w' (λ w'' _ → Lift 2ℓ (getChoice· n c w'' ≡ just t)))
                       → #strongBool! w' (#APPLY (#CS c) (#NUM n)) (#APPLY (#CS c) (#NUM n)))
    aw w1 e1 (t , inj₁ x , q) rewrite x = #AX , #AX , inj₁ (c₁ , c₁)
      where
        c₁ : #APPLY (#CS c) (#NUM n) #⇛! #BTRUE at w1
        c₁ w2 e2 = lift (Σ-steps-APPLY-CS 0 (NUM n) BTRUE w2 w2 n c refl gtn)
          where
            gtn : getT n c w2 ≡ just BTRUE
            gtn rewrite lower (q w2 e2) = refl
    aw w1 e1 (t , inj₂ x , q) rewrite x = #AX , #AX , inj₂ (c₁ , c₁)
      where
        c₁ : #APPLY (#CS c) (#NUM n) #⇛! #BFALSE at w1
        c₁ w2 e2 = lift (Σ-steps-APPLY-CS 0 (NUM n) BFALSE w2 w2 n c refl gtn)
          where
            gtn : getT n c w2 ≡ just BFALSE
            gtn rewrite lower (q w2 e2) = refl


followChoice-beth-ref : (c : Name) {w : 𝕎·} {f : wPred w} {r : Res{0ℓ}}
                        → □· w f
                        → onlyℂ∈𝕎 (Res.c₀ r) c w
                        → compatible· c w r
                        → freezable· c w
                        → ∃𝕎 w (λ w1 e1 → onlyℂ∈𝕎 (Res.c₀ r) c w1 × compatible· c w1 r × freezable· c w1 × f w1 e1)
followChoice-beth-ref c {w} {f} {r} (bar , i) ioc comp fb =
  w , ⊑-refl· _ , ioc , comp , fb ,
  i e (BarredChain.b bp) (chain.seq (pchain.c pc) (BarredChain.n bp)) (BarredChain.ext bp) (⊑-refl· _)
  where
    pc : pchain w
    pc = 𝕎→pchain w

    bp : BarredChain (𝔹.bar bar) (pchain.c pc)
    bp = 𝔹.bars bar pc

    w' : 𝕎·
    w' = BarredChain.w' bp

    e : w ⊑· w'
    e = 𝔹.ext bar (BarredChain.b bp)



open import choiceBar(W)(M)(C)(K)(P)(G)(X)(N)(enc)(V)(F)

bethRef-choiceBar : ChoiceBar
bethRef-choiceBar =
  mkChoiceBar
    Typeℂ₀₁-beth-ref
    Typeℂ₀₁-isType-beth-bar
    ℂ₀∈Typeℂ₀₁-beth-ref
    ℂ₁∈Typeℂ₀₁-beth-ref
    ∈Typeℂ₀₁→-beth-ref
    →∈Typeℂ₀₁-beth-ref
    equalTerms-pres-#⇛-left-BOOL₀!
    equalTerms-pres-#⇛-left-rev-BOOL₀!
    □·-choice-beth-ref
    followChoice-beth-ref

\end{code}
