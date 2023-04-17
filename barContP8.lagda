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
open import terms9(W)(C)(K)(G)(X)(N)(EC) using (#BAIRE!)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-trans)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (→equalInType-NAT! ; equalInType-W→)
--open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

--open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#upd ; #force ; equalInType-force)
--open import continuity1b(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇓sameℕ)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (steps-sat-isHighestℕ ; ¬Names→updCtxt)
--open import continuity4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import continuity5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import continuity6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-upd-force)
--open import continuity7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-TPURE→ₗ ; equalInType-TPURE→)
open import continuitySMb(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (isHighestℕ≤)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (#INIT ; #APPLY-loop⇓SUP→)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (seq2list ; mseq∈baire)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
--open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (#FunBarP ; sem ; #updSeq-APPLY-updr ; updSeq-steps-NUM ; seq2list≡)
open import barContP7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)



abstract

  #tab#⇛#ETA→ : (cn : cℕ) (w : 𝕎·) (r : Name) (F f : CTerm) (k j : ℕ)
                  → compatible· r w Res⊤
                  → #tab r F k f #⇛ #ETA (#NUM j) at w
                  → ∀𝕎 w (λ w1 e1 → Lift (lsuc L) (Σ 𝕎· (λ w' → Σ ℕ (λ n →
                       #APPLY F (#upd r f) #⇓ #NUM j from (chooseT r w1 N0) to w'
                       × getT 0 r w' ≡ just (NUM n)
                       × n < k))))
  #tab#⇛#ETA→ cn w r F f k j compat comp w1 e1
    with #APPLY-loop⇓SUP→ cn w1 r F (#NUM k) f (#INL (#NUM j)) #AX (⊑-compatible· e1 compat) (lower (comp w1 e1))
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


abstract

  equalInType-upd : (i : ℕ) (w : 𝕎·) (name : Name) (f : CTerm)
                    → ∀𝕎-get0-NUM w name
                    → ∈Type i w #BAIRE f
                    → equalInType i w #BAIRE (#upd name f) f
  equalInType-upd i w name f wgn eqf =
    equalInType-trans
      (equalInType-upd-force i w name f wgn eqf)
      (equalInType-sym (equalInType-force {i} {w} {f} eqf))


abstract

  equalInType-APPLY-upd : (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm)
                          → ∀𝕎-get0-NUM w name
                          → ∈Type i w #FunBar F
                          → ∈Type i w #BAIRE f
                          → equalInType i w #NAT (#APPLY F (#upd name f)) (#APPLY F f)
  equalInType-APPLY-upd i w name F f wgn F∈ f∈ =
    equalInType-FUN→ (≡CTerm→equalInType #BAIRE→NAT≡ F∈) w (⊑-refl· w) (#upd name f) f (equalInType-upd i w name f wgn f∈)



abstract

  NATeq→#⇓NUMₗ : {w : 𝕎·} {a b : CTerm} {k : ℕ}
                  → NATeq w a b
                  → b #⇓ #NUM k at w
                  → a #⇓ #NUM k at w
  NATeq→#⇓NUMₗ {w} {a} {b} {k} (j , c1 , c2) c
    rewrite NUMinj (⇓-val-det {w} {⌜ b ⌝} {NUM j} {NUM k} tt tt (lower (c2 w (⊑-refl· w))) c)
    = lower (c1 w (⊑-refl· w))


abstract

  →#APPLY-upd⇓ : (kb : K□) (i : ℕ) (w : 𝕎·) (name : Name) (F f : CTerm) (n : ℕ)
                  → ∀𝕎-get0-NUM w name
                  → ∈Type i w #FunBar F
                  → ∈Type i w #BAIRE f
                  → #APPLY F f #⇓ #NUM n at w
                  → #APPLY F (#upd name f) #⇓ #NUM n at w
  →#APPLY-upd⇓ kb i w name F f n wgn F∈ f∈ comp =
    NATeq→#⇓NUMₗ {w} {#APPLY F (#upd name f)} {#APPLY F f} {n} eqn comp
    where
      eqn : NATeq w (#APPLY F (#upd name f)) (#APPLY F f)
      eqn = kb (equalInType-NAT→ i w _ _ (equalInType-APPLY-upd i w name F f wgn F∈ f∈)) w (⊑-refl· w)


abstract

  follow-NUM-ETA : (kb : K□) (can : comp→∀ℕ) (gc : get-choose-ℕ) (cn : cℕ)
                   (i : ℕ) (w : 𝕎·) (r : Name) (I F : CTerm) (s : 𝕊) (k n j : ℕ)
                   → #¬Names F
                   → compatible· r w Res⊤
                   → I #⇛! #tab r F k (seq2list s k) at w
                   → ∈Type i w #FunBar F
                   → #APPLY F (#MSEQ s) #⇛ #NUM n at w
                   → #tab r F k (seq2list s k) #⇛ #ETA (#NUM j) at w
                   → #follow (#MSEQ s) I k #⇛ #NUM n at w
  follow-NUM-ETA kb can gc cn i w r I F s k n j nnF compat cI F∈ comp c3 =
    #⇛-trans {w} {#follow (#MSEQ s) I k} {#NUM j} {#NUM n} c5 (≡ₗ→#⇛ w (#NUM j) (#NUM n) (≡#NUM j n eqjn))
    where
      abstract
        c5 : #follow (#MSEQ s) I k #⇛ #NUM j at w
        c5 = #follow-INL⇛
               w I (#INL (#NUM j)) #AX (#MSEQ s) (#NUM j) k j
               (#⇛-trans {w} {I} {#tab r F k (seq2list s k)} {#ETA (#NUM j)} (#⇛!→#⇛ {w} {I} {#tab r F k (seq2list s k)} cI) c3)
               (#⇛!-refl {w} {#INL (#NUM j)})
               (#⇛-refl w (#NUM j))
        -- we now need to prove that (j ≡ n)

        h1 : Σ 𝕎· (λ w' → Σ ℕ (λ m →
                #APPLY F (#upd r (seq2list s k)) #⇓ #NUM j from (chooseT r w N0) to w'
                × getT 0 r w' ≡ just (NUM m)
                × m < k))
        h1 = lower (#tab#⇛#ETA→ cn w r F (seq2list s k) k j compat c3 w (⊑-refl· w))

        w' : 𝕎·
        w' = fst h1

        m : ℕ
        m = fst (snd h1)

        c6 : #APPLY F (#upd r (seq2list s k)) #⇓ #NUM j from (chooseT r w N0) to w'
        c6 = fst (snd (snd h1))

        gt0 : getT 0 r w' ≡ just (NUM m)
        gt0 = fst (snd (snd (snd h1)))

        ltk : m < k
        ltk = snd (snd (snd (snd h1)))

        c7 : #APPLY F (#MSEQ s) #⇓ #NUM n at (chooseT r w N0)
        c7 = lower (comp (chooseT r w N0) (choose⊑· r w (T→ℂ· N0)))

        c8 : #APPLY F (#upd r (#MSEQ s)) #⇓ #NUM n at (chooseT r w N0)
        c8 = →#APPLY-upd⇓
               kb i (chooseT r w N0) r F (#MSEQ s) n
               ((cn r (chooseT r w N0) (⊑-compatible· (choose⊑· r w (T→ℂ· N0)) compat)))
               (equalInType-mon F∈ (chooseT r w N0) (choose⊑· r w (T→ℂ· N0)))
               (mseq∈baire i (chooseT r w N0) s)
               c7

        upds : updSeq r s k ⌜ #APPLY F (#upd r (seq2list s k)) ⌝ ⌜ #APPLY F (#upd r (#MSEQ s)) ⌝
        upds = #updSeq-APPLY-updr r s k F nnF

        ish : isHighestℕ {fst c6} {chooseT r w N0} {w'} {⌜ #APPLY F (#upd r (seq2list s k)) ⌝} {NUM j} (suc m) r (snd c6)
        ish = steps-sat-isHighestℕ
                gc {r} {⌜ seq2list s k ⌝} {proj₁ c6} (#¬Names-seq2list s k) (CTerm.closed (seq2list s k))
                {chooseT r w N0} {w'} {⌜ #APPLY F (#upd r (seq2list s k)) ⌝}
                {NUM j} {suc m} (snd c6) tt
                (updCtxt-APPLY-upd-seq2list r s k F nnF)
                (⊑-compatible· (choose⊑· r w (T→ℂ· N0)) compat)
                (cn r (chooseT r w N0) (⊑-compatible· (choose⊑· r w (T→ℂ· N0)) compat))
                (m , gt0 , ≤-refl)

        ish' : isHighestℕ {fst c6} {chooseT r w N0} {w'} {⌜ #APPLY F (#upd r (seq2list s k)) ⌝} {NUM j} k r (snd c6)
        ish' = isHighestℕ≤ (proj₁ c6) (chooseT r w N0) w' ⌜ #APPLY F (#upd r (seq2list s k)) ⌝ (NUM j) (suc m) k r (snd c6) ltk ish

        c9 : Σ ℕ (λ k' → steps k' (⌜ #APPLY F (#upd r (#MSEQ s)) ⌝ , chooseT r w N0) ≡ (NUM j , w'))
        c9 = updSeq-steps-NUM
               cn gc r s k (fst c6)
               ⌜ #APPLY F (#upd r (seq2list s k)) ⌝ ⌜ #APPLY F (#upd r (#MSEQ s)) ⌝
               j (chooseT r w N0) w' (⊑-compatible· (choose⊑· r w (T→ℂ· N0)) compat) upds (snd c6) ish'

        -- use updSeq-steps-NUM in barContP6
        -- and steps-sat-isHighestℕ in continuity3

        eqjn : j ≡ n
        eqjn = NUMinj (⇓-val-det
                        {chooseT r w N0} {⌜ #APPLY F (#upd r (#MSEQ s)) ⌝} {NUM j} {NUM n} tt tt
                        (⇓-from-to→⇓  {chooseT r w N0} {w'} {⌜ #APPLY F (#upd r (#MSEQ s)) ⌝} {NUM j} c9)
                        c8)
        -- (j ≡ n) because in the computation c3 that uses c4, r never goes about k and so comp must compute to the same result
        -- use #tab#⇛#ETA→ on c3  + continuity

\end{code}
