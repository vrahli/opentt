\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
--{-# OPTIONS --lossy-unification #-}
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


module barContP8 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                 (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
                 (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                 (EM : ExcludedMiddle (lsuc(L)))
                 (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)

--open import terms2(W)(C)(K)(G)(X)(N)(EC)
open import terms3(W)(C)(K)(G)(X)(N)(EC) using (≡APPLY ; upd)
--open import terms4(W)(C)(K)(G)(X)(N)(EC)
--open import terms5(W)(C)(K)(G)(X)(N)(EC)
--open import terms6(W)(C)(K)(G)(X)(N)(EC)
--open import terms7(W)(C)(K)(G)(X)(N)(EC)
open import terms8(W)(C)(K)(G)(X)(N)(EC) using (#APPLY2 ; #⇛-trans ; #INL¬≡INR)
open import terms9 using (#BAIRE!) --(W)(C)(K)(G)(X)(N)(EC)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (∀𝕎-□Func2 ; eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇛-mon) -- (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-trans)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (→equalInType-NAT! ; equalInType-W→)
--open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (#upd ; #force ; equalInType-force ; ⇛-upd-body ; #APPLY-force)
--open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇓sameℕ)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (steps-sat-isHighestℕ ; ¬Names→updCtxt)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
  using (equalInType-upd-force ; APPLY-force⇛ ; ⇛-upd-body→⇛-APPLY)
--open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-TPURE→ₗ ; equalInType-TPURE→)
open import continuitySMb(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
  using (isHighestℕ≤)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
  using (#INIT ; #APPLY-loop⇓SUP→ ; #⇛!-NUM-type)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
  using (seq2list ; mseq∈baire)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
--open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
  using (#FunBarP ; #updSeq-APPLY-updr ; updSeq-steps-NUM ; seq2list≡ ; mseq∈NAT→T ; #¬Names-seq2list)
open import barContP7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)



abstract

  #tab#⇛#ETA→ : (cn : cℕ) (w : 𝕎·) (F f : CTerm) (k j : ℕ)
                  → #tab F k f #⇛ #ETA (#NUM j) at w
                  → ∀𝕎 w (λ w1 e1 → Lift (lsuc L) (Σ 𝕎· (λ w' → Σ ℕ (λ n →
                       #APPLY F (#upd (#loopName w1 F (#NUM k) f) f) #⇓ #NUM j from (#loop𝕎0 w1 F (#NUM k) f) to w'
                       × getT 0 (#loopName w1 F (#NUM k) f) w' ≡ just (NUM n)
                       × n < k))))
  #tab#⇛#ETA→ cn w F f k j comp w1 e1
    with #APPLY-loop⇓SUP→ cn w1 F (#NUM k) f (#INL (#NUM j)) #AX (lower (comp w1 e1))
  ... | (i , w' , n , m , comp' , gt0 ,  ck , inj₁ (x , y , z))
    rewrite #NUMinj (#INLinj y) | #NUMinj (#compVal {#NUM k} {#NUM m} {w'} ck tt)
    = lift (w' , n , comp' , gt0 , x)
  ... | (i , w' , n , m , comp' , gt0 ,  ck , inj₂ (x , y , z)) = ⊥-elim (#INL¬≡INR {#NUM j} {#AX} y)


abstract

  ≡#NUM : (i j : ℕ)
          → i ≡ j
          → #NUM i ≡ #NUM j
  ≡#NUM i j e rewrite e = refl


abstract

  updCtxt-APPLY-upd-seq2list : (r : Name) (s : 𝕊) (k : ℕ) (F : CTerm) (nnF : #¬Names F)
                               → updCtxt r ⌜ seq2list s k ⌝ ⌜ #APPLY F (#upd r (seq2list s k)) ⌝
  updCtxt-APPLY-upd-seq2list r s k F nnF
    rewrite seq2list≡ s k
    = updCtxt-APPLY ⌜ F ⌝ (upd r (s2l s k)) (¬Names→updCtxt {r} {s2l s k} {⌜ F ⌝} nnF) updCtxt-upd


type-#⇛-NUM : (P : ℕ → Set) (T : CTerm) → Set(lsuc(L))
type-#⇛-NUM P T =
  {i : ℕ} {w : 𝕎·} {a b : CTerm}
  → equalInType i w T a b
  → □· w (λ w' _ → Σ ℕ (λ n → a #⇛ #NUM n at w' × b #⇛ #NUM n at w' × P n))


equalInType-upd-force-T : (i : ℕ) (w : 𝕎·) (name : Name) (P : ℕ → Set) (T f : CTerm)
                          → ∀𝕎-get0-NUM w name
                          → type-#⇛-NUM P T
                          → #⇛!-NUM-type P T
                          → type-preserves-#⇛ T
                          → isType i w T
                          → ∈Type i w (#FUN #NAT T) f
                          → equalInType i w (#FUN #NAT T) (#upd name f) (#force f)
equalInType-upd-force-T i w name P T f wgn tyn nty prest tyt eqf =
  equalInType-FUN eqTypesNAT tyt aw
  where
    eqf1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                         → equalInType i w' T (#APPLY f a₁) (#APPLY f a₂))
    eqf1 = equalInType-FUN→ eqf

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' T (#APPLY (#upd name f) a₁) (#APPLY (#force f) a₂))
    aw w1 e1 a₁ a₂ eqa =
      equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 a₁ a₂ eqa))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂
                              → equalInType i w' T (#APPLY (#upd name f) a₁) (#APPLY (#force f) a₂))
        aw1 w2 e2 (k , c₁ , c₂) =
          equalInType-local (Mod.∀𝕎-□Func M aw2 (tyn (equalInType-FUN→ eqf w2 (⊑-trans· e1 e2) (#NUM k) (#NUM k) (NUM-equalInType-NAT i w2 k))))
            where
              aw2 : ∀𝕎 w2 (λ w' e' → Σ ℕ (λ n → #APPLY f (#NUM k) #⇛ #NUM n at w' × #APPLY f (#NUM k) #⇛ #NUM n at w' × P n)
                                    → equalInType i w' T (#APPLY (#upd name f) a₁) (#APPLY (#force f) a₂))
              aw2 w3 e3 (n , d₁ , d₂ , pn) =
                prest i w3 (#APPLY (#upd name f) a₁) (#NUM n) (#APPLY (#force f) a₂) (#NUM n)
                      (⇛-upd-body→⇛-APPLY {name} {⌜ f ⌝} {⌜ a₁ ⌝} {n} {w3} (CTerm.closed f) (⇛-upd-body w3 ⌜ f ⌝ ⌜ a₁ ⌝ k n name (∀𝕎-mon (⊑-trans· e1 (⊑-trans· e2 e3)) wgn) (CTerm.closed f) (∀𝕎-mon e3 c₁) d₁))
                      (APPLY-force⇛ (CTerm.closed f) (∀𝕎-mon e3 c₂) d₂)
                      (nty {i} {w3} {n} pn)


equalInType-force-T : {i : ℕ} {w : 𝕎·} (P : ℕ → Set) {T f : CTerm}
                      → type-#⇛-NUM P T
                      → #⇛!-NUM-type P T
                      → type-preserves-#⇛ T
                      → isType i w T
                      → ∈Type i w (#FUN #NAT T) f
                      → equalInType i w (#FUN #NAT T) f (#force f)
equalInType-force-T {i} {w} P {T} {f} tyn nty prest tyt eqi =
  equalInType-FUN eqTypesNAT tyt aw1
  where
    aw1 : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                        → equalInType i w' T (#APPLY f a₁) (#APPLY (#force f) a₂))
    aw1 w1 e1 a₁ a₂ ea = equalInType-local (Mod.∀𝕎-□Func M aw2 (equalInType-NAT→ i w1 a₁ a₂ ea))
      where
        aw2 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂
                              → equalInType i w' T (#APPLY f a₁) (#APPLY (#force f) a₂))
        aw2 w2 e2 (k , c₁ , c₂) = equalInType-local (Mod.∀𝕎-□Func M aw3 (tyn (equalInType-FUN→ eqi w2 (⊑-trans· e1 e2) a₁ (#NUM k) (#⇛NUM→equalInType-NAT i w2 a₁ k c₁))))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → Σ ℕ (λ n → #APPLY f a₁ #⇛ #NUM n at w' × #APPLY f (#NUM k) #⇛ #NUM n at w' × P n)
                                  → equalInType i w' T (#APPLY f a₁) (#APPLY (#force f) a₂))
            aw3 w3 e3 (n , d₁ , d₂ , pn) =
              prest i w3 (#APPLY f a₁) (#NUM n) (#APPLY (#force f) a₂) (#NUM n)
                    d₁
                    (⇛-trans (#APPLY-force {w3} {f} {a₂} (∀𝕎-mon e3 c₂)) d₂)
                    (nty pn)



abstract

  equalInType-upd : (i : ℕ) (w : 𝕎·) (name : Name) (P : ℕ → Set) (T f : CTerm)
                    → ∀𝕎-get0-NUM w name
                    → type-#⇛-NUM P T
                    → #⇛!-NUM-type P T
                    → type-preserves-#⇛ T
                    → isType i w T
                    → ∈Type i w (#FUN #NAT T) f
                    → equalInType i w (#FUN #NAT T) (#upd name f) f
  equalInType-upd i w name P T f wgn tyn nty prest tyt eqf =
    equalInType-trans
      (equalInType-upd-force-T i w name P T f wgn tyn nty prest tyt eqf)
      (equalInType-sym (equalInType-force-T {i} {w} P {T} {f} tyn nty prest tyt eqf))


abstract

  equalInType-APPLY-upd : (i : ℕ) (w : 𝕎·) (name : Name) (P : ℕ → Set) (T F f : CTerm)
                          → ∀𝕎-get0-NUM w name
                          → type-#⇛-NUM P T
                          → #⇛!-NUM-type P T
                          → type-preserves-#⇛ T
                          → isType i w T
                          → ∈Type i w (#FunBar T) F
                          → ∈Type i w (#FUN #NAT T) f
                          → equalInType i w #NAT (#APPLY F (#upd name f)) (#APPLY F f)
  equalInType-APPLY-upd i w name P T F f wgn tyn nty prest tyt F∈ f∈ =
    equalInType-FUN→ F∈ w (⊑-refl· w) (#upd name f) f (equalInType-upd i w name P T f wgn tyn nty prest tyt f∈)



abstract

  NATeq→#⇓NUMₗ : {w : 𝕎·} {a b : CTerm} {k : ℕ}
                  → NATeq w a b
                  → b #⇓ #NUM k at w
                  → a #⇓ #NUM k at w
  NATeq→#⇓NUMₗ {w} {a} {b} {k} (j , c1 , c2) c
    rewrite NUMinj (⇓-val-det {w} {⌜ b ⌝} {NUM j} {NUM k} tt tt (lower (c2 w (⊑-refl· w))) c)
    = lower (c1 w (⊑-refl· w))


abstract

  →#APPLY-upd⇓ : (kb : K□) (i : ℕ) (w : 𝕎·) (name : Name) (P : ℕ → Set) (T F f : CTerm) (n : ℕ)
                  → ∀𝕎-get0-NUM w name
                  → type-#⇛-NUM P T
                  → #⇛!-NUM-type P T
                  → type-preserves-#⇛ T
                  → isType i w T
                  → ∈Type i w (#FunBar T) F
                  → ∈Type i w (#FUN #NAT T) f
                  → #APPLY F f #⇓ #NUM n at w
                  → #APPLY F (#upd name f) #⇓ #NUM n at w
  →#APPLY-upd⇓ kb i w name P T F f n wgn tyn nty prest tyt F∈ f∈ comp =
    NATeq→#⇓NUMₗ {w} {#APPLY F (#upd name f)} {#APPLY F f} {n} eqn comp
    where
      eqn : NATeq w (#APPLY F (#upd name f)) (#APPLY F f)
      eqn = kb (equalInType-NAT→ i w _ _ (equalInType-APPLY-upd i w name P T F f wgn tyn nty prest tyt F∈ f∈)) w (⊑-refl· w)


abstract

  follow-NUM-ETA : (kb : K□) (can : comp→∀ℕ) (gc : get-choose-ℕ) (cn : cℕ)
                   (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T I F : CTerm) (s : 𝕊) (k n j : ℕ)
                   → #¬Names F
                   → ((n : ℕ) → P (s n))
                   → type-#⇛-NUM P T
                   → #⇛!-NUM-type P T
                   → type-preserves-#⇛ T
                   → isType i w T
                   → I #⇛! #tab F k (seq2list s k) at w
                   → ∈Type i w (#FunBar T) F
                   → #APPLY F (#MSEQ s) #⇛ #NUM n at w
                   → #tab F k (seq2list s k) #⇛ #ETA (#NUM j) at w
                   → #follow (#MSEQ s) I k #⇛ #NUM n at w
  follow-NUM-ETA kb can gc cn i w P T I F s k n j nnF ps tyn nty prest tyt cI F∈ comp c3 =
    #⇛-trans {w} {#follow (#MSEQ s) I k} {#NUM j} {#NUM n} c5 (≡ₗ→#⇛ w (#NUM j) (#NUM n) (≡#NUM j n eqjn))
    where
      abstract
        c5 : #follow (#MSEQ s) I k #⇛ #NUM j at w
        c5 = #follow-INL⇛
               w I (#INL (#NUM j)) #AX (#MSEQ s) (#NUM j) k j
               (#⇛-trans {w} {I} {#tab F k (seq2list s k)} {#ETA (#NUM j)} (#⇛!→#⇛ {w} {I} {#tab F k (seq2list s k)} cI) c3)
               (#⇛!-refl {w} {#INL (#NUM j)})
               (#⇛-refl w (#NUM j))
        -- we now need to prove that (j ≡ n)

        r : Name
        r = #loopName w F (#NUM k) (seq2list s k)

        w₀ : 𝕎·
        w₀ = #loop𝕎 w F (#NUM k) (seq2list s k)

        w0 : 𝕎·
        w0 = #loop𝕎0 w F (#NUM k) (seq2list s k)

        e0 : w ⊑· w0
        e0 = ⊑-trans· (startNewChoiceT⊏ Res⊤ w ⌜ #νloopFB F (#loop F) (#NUM k) (seq2list s k) ⌝) (choose⊑· r (#loop𝕎 w F (#NUM k) (seq2list s k)) (T→ℂ· N0))

        compat : compatible· r w₀ Res⊤
        compat = startChoiceCompatible· Res⊤ w r (¬newChoiceT∈dom𝕎 w ⌜ #νloopFB F (#loop F) (#NUM k) (seq2list s k) ⌝)

        compat0 : compatible· r w0 Res⊤
        compat0 = ⊑-compatible· (choose⊑· r w₀ (T→ℂ· N0)) compat

        h1 : Σ 𝕎· (λ w' → Σ ℕ (λ m →
                #APPLY F (#upd r (seq2list s k)) #⇓ #NUM j from w0 to w'
                × getT 0 r w' ≡ just (NUM m)
                × m < k))
        h1 = lower (#tab#⇛#ETA→ cn w F (seq2list s k) k j c3 w (⊑-refl· w))

        w' : 𝕎·
        w' = fst h1

        m : ℕ
        m = fst (snd h1)

        c6 : #APPLY F (#upd r (seq2list s k)) #⇓ #NUM j from w0 to w'
        c6 = fst (snd (snd h1))

        gt0 : getT 0 r w' ≡ just (NUM m)
        gt0 = fst (snd (snd (snd h1)))

        ltk : m < k
        ltk = snd (snd (snd (snd h1)))

        c7 : #APPLY F (#MSEQ s) #⇓ #NUM n at w0
        c7 = lower (comp w0 e0)

        c8 : #APPLY F (#upd r (#MSEQ s)) #⇓ #NUM n at (w0)
        c8 = →#APPLY-upd⇓
               kb i w0 r P T F (#MSEQ s) n
               (cn r w0 compat0)
               tyn nty prest (eqTypes-mon (uni i) tyt w0 e0)
               (equalInType-mon F∈ w0 e0)
               (mseq∈NAT→T i w0 s P T ps nty prest (eqTypes-mon (uni i) tyt w0 e0)) --(mseq∈baire i (chooseT r w N0) s)
               c7

        upds : updSeq r s k ⌜ #APPLY F (#upd r (seq2list s k)) ⌝ ⌜ #APPLY F (#upd r (#MSEQ s)) ⌝
        upds = #updSeq-APPLY-updr r s k F nnF

        ish : isHighestℕ {fst c6} {w0} {w'} {⌜ #APPLY F (#upd r (seq2list s k)) ⌝} {NUM j} (suc m) r (snd c6)
        ish = steps-sat-isHighestℕ
                gc {r} {⌜ seq2list s k ⌝} {proj₁ c6} (#¬Names-seq2list s k) (CTerm.closed (seq2list s k))
                {w0} {w'} {⌜ #APPLY F (#upd r (seq2list s k)) ⌝}
                {NUM j} {suc m} (snd c6) tt
                (updCtxt-APPLY-upd-seq2list r s k F nnF)
                compat0
                (cn r w0 compat0)
                (m , gt0 , ≤-refl)

        ish' : isHighestℕ {fst c6} {w0} {w'} {⌜ #APPLY F (#upd r (seq2list s k)) ⌝} {NUM j} k r (snd c6)
        ish' = isHighestℕ≤ (proj₁ c6) w0 w' ⌜ #APPLY F (#upd r (seq2list s k)) ⌝ (NUM j) (suc m) k r (snd c6) ltk ish

        c9 : Σ ℕ (λ k' → steps k' (⌜ #APPLY F (#upd r (#MSEQ s)) ⌝ , w0) ≡ (NUM j , w'))
        c9 = updSeq-steps-NUM
               cn gc r s k (fst c6)
               ⌜ #APPLY F (#upd r (seq2list s k)) ⌝ ⌜ #APPLY F (#upd r (#MSEQ s)) ⌝
               j w0 w' compat0 upds (snd c6) ish'

        -- use updSeq-steps-NUM in barContP6
        -- and steps-sat-isHighestℕ in continuity3

        eqjn : j ≡ n
        eqjn = NUMinj (⇓-val-det
                        {w0} {⌜ #APPLY F (#upd r (#MSEQ s)) ⌝} {NUM j} {NUM n} tt tt
                        (⇓-from-to→⇓  {w0} {w'} {⌜ #APPLY F (#upd r (#MSEQ s)) ⌝} {NUM j} c9)
                        c8)
        -- (j ≡ n) because in the computation c3 that uses c4, r never goes about k and so comp must compute to the same result
        -- use #tab#⇛#ETA→ on c3  + continuity

\end{code}
