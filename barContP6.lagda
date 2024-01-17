\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}
{-# OPTIONS --lossy-unification #-}
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
                 (C : Choice)
                 (K : Compatible {L} W C)
                 (G : GetChoice {L} W C K)
                 (X : ChoiceExt W C)
                 (N : NewChoice {L} W C K G)
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
open import terms8(W)(C)(K)(G)(X)(N)(EC) using (#APPLY2 ; APPLY-MSEQ⇛)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(G)(X)(N)(EC)
open import props0(W)(M)(C)(K)(G)(X)(N)(EC) using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(G)(X)(N)(EC)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(G)(X)(N)(EC)
open import props2(W)(M)(C)(K)(G)(X)(N)(EC)
--open import props3(W)(M)(C)(K)(G)(X)(N)(EC)
--open import props4(W)(M)(C)(K)(G)(X)(N)(EC)
open import props5(W)(M)(C)(K)(G)(X)(N)(EC) using (NATmem)
open import pure(W)(M)(C)(K)(G)(X)(N)(EC) using (equalInType-TPURE→ₗ ; equalInType-TPURE→)

open import list(W)(M)(C)(K)(G)(X)(N)(EC)

open import continuity-conds(W)(C)(K)(G)(X)(N)(EC)

open import continuity1(W)(M)(C)(K)(G)(X)(N)(EC) using (#upd)
open import continuity2(W)(M)(C)(K)(G)(X)(N)(EC)
open import continuity3(W)(M)(C)(K)(G)(X)(N)(EC) using (isHighestℕ→getT≤ℕ ; ¬Names→updCtxt ; steps-sat-isHighestℕ)
--open import continuity4(W)(M)(C)(K)(G)(X)(N)(EC) using (steps-trans+)
--open import continuity5(W)(M)(C)(K)(G)(X)(N)(EC) using (steps-decomp-isHighestℕ)
--open import continuity7(W)(M)(C)(K)(G)(X)(N)(EC)

open import barContP(W)(M)(C)(K)(G)(X)(N)(EM)(EC)
open import barContP2(W)(M)(C)(K)(G)(X)(N)(EM)(EC)
open import barContP3(W)(M)(C)(K)(G)(X)(N)(EM)(EC)
  using (seq2list ; mseq∈baire ; corSeq→correctSeq ; →corSeq)
open import barContP4(W)(M)(C)(K)(G)(X)(N)(EM)(EC)
  using (s2l ; updSeq ; updSeq-NUM→ ; updSeq-upd ; updSeq-updr ; updSeq-APPLY ; correctSeqN-inv0 ; steps→≡𝕎)
open import barContP5(W)(M)(C)(K)(G)(X)(N)(EM)(EC)
  using (updSeq-step ; updSeq-refl ; updSeq-steps)



#¬Names-seq2list : (s : 𝕊) (k : ℕ) → #¬Names (seq2list s k)
#¬Names-seq2list s 0 = refl
#¬Names-seq2list s (suc k) rewrite ¬names-shiftUp 0 ⌜ seq2list s k ⌝ | #¬Names-seq2list s k = refl


seq2list≡ : (s : 𝕊) (n : ℕ) → ⌜ seq2list s n ⌝ ≡ s2l s n
seq2list≡ s 0 = refl
seq2list≡ s (suc n) rewrite seq2list≡ s n = refl


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



mseq∈NAT→T : (i : ℕ) (w : 𝕎·) (s : 𝕊) (P : ℕ → Set) (T : CTerm)
               → ((n : ℕ) → P (s n))
               → #⇛!-NUM-type P T
               → type-preserves-#⇛ T
               → isType i w T
               → ∈Type i w (#FUN #NAT T) (#MSEQ s)
mseq∈NAT→T i w s P T cond tyn pres tyt =
  equalInType-FUN
    eqTypesNAT tyt
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' T (#APPLY (#MSEQ s) a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 n₁ n₂ n∈ =
      equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 n₁ n₂ n∈))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' n₁ n₂ → equalInType i w' T (#APPLY (#MSEQ s) n₁) (#APPLY (#MSEQ s) n₂))
        aw1 w2 e2 (k , c₁ , c₂) =
          pres i w2
               (#APPLY (#MSEQ s) n₁) (#NUM (s k))
               (#APPLY (#MSEQ s) n₂) (#NUM (s k))
               (APPLY-MSEQ⇛ w2 s ⌜ n₁ ⌝ k c₁)
               (APPLY-MSEQ⇛ w2 s ⌜ n₂ ⌝ k c₂)
               (tyn {i} {w2} {s k} (cond k))


P-path2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} (P : ℕ → Set) {T : CTerm} (tyn : type-#⇛!-NUM P T) (p0 : P 0)
            (p : path i w #IndBarB (#IndBarC T))
            (n : ℕ) → P (path2𝕊 kb P tyn p n)
P-path2𝕊 kb {i} {w} P {T} tyn p0 p n with p n
... | inj₁ (a , b , a∈ , b∈) with snd (kb (∈Type-IndBarB-IndBarC→ i w P T a b tyn a∈ b∈) w (⊑-refl· w))
... |   (j , x , y)  = y
P-path2𝕊 kb {i} {w} P {T} tyn p0 p n | inj₂ q = p0


abstract
  -- We want to create a Term ∈ BAIRE from this path.
  noInfPath : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
              (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F : CTerm)
              → P 0
              → type-#⇛!-NUM P T
              → #⇛!-NUM-type P T
              → type-preserves-#⇛ T
              → isType i w T
              → #¬Names F -- This is currently required by continuity
  --            → compatible· r w Res⊤
              → ∈Type i w (#FunBar T) F
              → (p : path i w #IndBarB (#IndBarC T))
              → correctPath {i} {w} {#IndBarB} {#IndBarC T} (#APPLY2 (#loop F) (#NUM 0) #INIT) p
              → isInfPath {i} {w} {#IndBarB} {#IndBarC T} p
              → ⊥
  noInfPath kb cn can exb gc i w P T F p0 tyn nty prest tyt nnF {--compat--} F∈ p cor inf =
    ltsn (≡getT≤ℕ→< w2 w' r (suc n) j eqw' (trans (sym gt01) gt0) gtn) --(≡getT≤ℕ→< w0 w' r (suc n) j eqw' gt0 gtn)
    where
      s : 𝕊
      s = path2𝕊 kb P tyn p

      f : CTerm
      f = #MSEQ s

      --nnf : #¬Names f
      --nnf = refl

      --f∈ : ∈Type i w #BAIRE f
      --f∈ = mseq∈baire i w s

      r : Name
      r = #loopName w F (#NUM 0) f

      w₁ : 𝕎·
      w₁ = #loop𝕎 w F (#NUM 0) f

      e₁ : w ⊑· w₁
      e₁ = startNewChoiceT⊏ Res⊤ w ⌜ #νloopFB F (#loop F) (#NUM 0) f ⌝

      w1 : 𝕎·
      w1 = #loop𝕎0 w F (#NUM 0) f

      e1 : w₁ ⊑· w1
      e1 = choose⊑· r (#loop𝕎 w F (#NUM 0) f) (T→ℂ· N0)

      compat : compatible· r w₁ Res⊤
      compat = startChoiceCompatible· Res⊤ w r (¬newChoiceT∈dom𝕎 w ⌜ #νloopFB F (#loop F) (#NUM 0) f ⌝)

      a∈1 : ∈Type i w₁ #NAT (#APPLY F (#upd r f))
      a∈1 = equalInType-FUN→
               F∈ w₁ e₁ (#upd r f) (#upd r f)
               (upd∈BAIRE cn i w₁ r T f compat prest (eqTypes-mon (uni i) tyt w₁ e₁) (mseq∈NAT→T i w₁ s P T (P-path2𝕊 kb P tyn p0 p) nty prest (eqTypes-mon (uni i) tyt w₁ e₁)))

      a∈2 : NATmem w₁ (#APPLY F (#upd r f))
      a∈2 = kb (equalInType-NAT→ i w₁ (#APPLY F (#upd r f)) (#APPLY F (#upd r f)) a∈1) w₁ (⊑-refl· w₁)

      k : ℕ
      k = fst a∈2

      ca1 : Σ 𝕎· (λ w' → #APPLY F (#upd r f) #⇓ #NUM k from w1 to w')
      ca1 = #⇓→from-to {w1} {#APPLY F (#upd r f)} {#NUM k} (lower (fst (snd a∈2) w1 e1)) --w (⊑-refl· w)))

      w' : 𝕎·
      w' = fst ca1

      ca2 : #APPLY F (#upd r f) #⇓ #NUM k from w1 to w'
      ca2 = snd ca1

      e' : w₁ ⊑· w'
      e' = ⊑-trans· e1 (#⇓from-to→⊑ {w1} {w'} {#APPLY F (#upd r f)} {#NUM k} ca2)

      d1 : Σ ℕ (λ n → getT 0 r w' ≡ just (NUM n))
      d1 = lower (cn r w₁ compat w' e')

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
              gc {r} {⌜ f ⌝} {fst ca2} refl (CTerm.closed f) {w1} {w'}
              {APPLY ⌜ F ⌝ (upd r ⌜ f ⌝)} {NUM k} {suc n} (snd ca2)
              tt uc (⊑-compatible· e1 compat) wgt0 gtn

      r₀ : Name
      r₀ = #loopName w F (#NUM (suc n)) (seq2list s (suc n))

      w₀₀ : 𝕎·
      w₀₀ = #loop𝕎 w F (#NUM (suc n)) (seq2list s (suc n))

      w₀ : 𝕎·
      w₀ = #loop𝕎0 w F (#NUM (suc n)) (seq2list s (suc n))

      compat₀ : compatible· r₀ w₀₀ Res⊤
      compat₀ = startChoiceCompatible· Res⊤ w r₀ (¬newChoiceT∈dom𝕎 w ⌜ #νloopFB F (#loop F) (#NUM (suc n)) (seq2list s (suc n)) ⌝)

      inv : Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
              #APPLY F (#upd r₀ (seq2list s (suc n))) #⇓ #NUM m from w₀ to w'
              × getT 0 r₀ w' ≡ just (NUM j)
              × ¬ j < (suc n))))
      inv = correctSeqN-inv0 i w F s (suc n) (corSeq→correctSeq w F s (→corSeq kb cn i w P T F tyn F∈ p cor inf) (suc (suc n)))

      m0 : ℕ
      m0 = fst inv

      w0 : 𝕎·
      w0 = fst (snd inv)

      j : ℕ
      j = fst (snd (snd inv))

      comp0 : #APPLY F (#upd r₀ (seq2list s (suc n))) #⇓ #NUM m0 from w₀ to w0
      comp0 = fst (snd (snd (snd inv)))

      gt0 : getT 0 r₀ w0 ≡ just (NUM j)
      gt0 = fst (snd (snd (snd (snd inv))))

      ltsn : ¬ j < (suc n)
      ltsn = snd (snd (snd (snd (snd inv))))

      comp00 : Σ 𝕎· (λ w2' → #APPLY F (#upd r (seq2list s (suc n))) #⇓ #NUM m0 from w1 to w2'
                      × getT 0 r₀ w0 ≡ getT 0 r w2')
      comp00 = differ⇓APPLY-upd can gc ⌜ F ⌝ ⌜ seq2list s (suc n) ⌝ (CTerm.closed (seq2list s (suc n))) (#¬Names-seq2list s (suc n)) nnF r₀ r
                                (#loop𝕎 w F (#NUM (suc n)) (seq2list s (suc n))) w0
                                (#loop𝕎 w F (#NUM 0) f) m0 compat₀ compat comp0

      w2 : 𝕎·
      w2 = fst comp00

      comp01 : #APPLY F (#upd r (seq2list s (suc n))) #⇓ #NUM m0 from w1 to w2
      comp01 = fst (snd comp00)

      gt01 : getT 0 r₀ w0 ≡ getT 0 r w2
      gt01 = snd (snd comp00)

      c : Σ ℕ (λ k' → steps k' (⌜ #APPLY F (#upd r (seq2list s (suc n))) ⌝ , w1) ≡ (NUM k , w'))
      c = updSeq-steps-NUM
            cn gc r s (suc n) (fst ca2)
            ⌜ #APPLY F (#upd r f) ⌝ ⌜ #APPLY F (#upd r (seq2list s (suc n))) ⌝
            k w1 w' (⊑-compatible· e1 compat)
            (#updSeq-APPLY-upd r s (suc n) F nnF)
            (snd ca2) ish

      eqw' : w2 ≡ w'
      eqw' = steps→≡𝕎 w1 w2 w' ⌜ #APPLY F (#upd r (seq2list s (suc n))) ⌝ (NUM m0) (NUM k) (fst comp01) (fst c) tt tt
                       (snd comp01) {--(snd comp0)--} (snd c)


FunBarP : Term → Term
FunBarP T = TPURE (FunBar T)


barThesisP : Term → Term
barThesisP T = FUN (FunBarP T) (IndBar T)


#FunBarP : CTerm → CTerm
#FunBarP T = #TPURE (#FunBar T)


#barThesisP : CTerm → CTerm
#barThesisP T = #FUN (#FunBarP T) (#IndBar T)


LAM0∈NAT→T : (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T : CTerm)
               → P 0
               → #⇛!-NUM-type P T
               → isType i w T
               → type-preserves-#⇛ T
               → ∈Type i w (#FUN #NAT T) #LAM0
LAM0∈NAT→T i w P T p0 nty tyt prest = equalInType-FUN eqTypesNAT tyt aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' T (#APPLY #LAM0 a₁) (#APPLY #LAM0 a₂))
    aw w1 e1 n₁ n₂ n∈ =
      prest i w1 (#APPLY #LAM0 n₁) #N0 (#APPLY #LAM0 n₂) #N0
            (λ w2 e2 → lift (1 , refl)) (λ w2 e2 → lift (1 , refl))
            (nty {i} {w1} {0} p0)


-- comp→∀ℕ is stronger than cℕ. get rid of cℕ?
sem : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
      (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F : CTerm)
      (nnF : #¬Names F)
--      → #¬Names F -- This is currently required by continuity (captured by #FunBarP)
      → P 0
      → type-preserves-#⇛ T
      → type-#⇛!-NUM P T
      → #⇛!-NUM-type P T
      → isType i w T
      → ∈Type i w (#FunBarP T) F
      → ∈Type i w (#IndBar T) (#APPLY2 (#loop F) (#NUM 0) #INIT)
sem kb cn can exb gc i w P T F nnF {--nnF--} p0 prest tyn nty tyt F∈P = concl
  where
{--    nnF  : #¬Names F
    nnF = {!!} --equalInType-TPURE→ₗ F∈P
--}

    F∈ : ∈Type i w (#FunBar T) F
    F∈ = equalInType-TPURE→ F∈P

    co : ∈Type i w (#CoIndBar T) (#APPLY2 (#loop F) (#NUM 0) #INIT)
    co = coSem can gc kb cn i w P T F (#NUM 0) #INIT refl refl nnF prest tyn nty tyt F∈
               (NUM-equalInType-NAT! i w 0) (LAM0∈NAT→T i w P T p0 nty tyt prest) --(LAM0∈BAIRE i w)

    concl : ∈Type i w (#IndBar T) (#APPLY2 (#loop F) (#NUM 0) #INIT)
    concl with EM {∃𝕎 w (λ w' _ → Σ (path i w' #IndBarB (#IndBarC T))
                                   (λ p → correctPath {i} {w'} {#IndBarB} {#IndBarC T} (#APPLY2 (#loop F) (#NUM 0) #INIT) p
                                         × isInfPath {i} {w'} {#IndBarB} {#IndBarC T} p))}
    ... | yes (w' , e' , p , cor , inf) = c
      where
        c : ∈Type i w (#IndBar T) (#APPLY2 (#loop F) (#NUM 0) #INIT)
        c = ⊥-elim (noInfPath kb cn can exb gc i w' P T F p0 tyn nty prest (eqTypes-mon (uni i) tyt w' e') nnF (equalInType-mon F∈ w' e') p cor inf )
    ... | no pp = CoIndBar2IndBar kb i w T (#APPLY2 (#loop F) (#NUM 0) #INIT) tyt cond co
      where
        cond : ∀𝕎 w (λ w' _ → (p : path i w' #IndBarB (#IndBarC T))
               → correctPath {i} {w'} {#IndBarB} {#IndBarC T} (#APPLY2 (#loop F) (#NUM 0) #INIT) p
               → isFinPath {i} {w'} {#IndBarB} {#IndBarC T} p)
        cond w1 e1 p cor with EM {Lift {0ℓ} (lsuc(L)) (isFinPath {i} {w1} {#IndBarB} {#IndBarC T} p)}
        ... | yes qq = lower qq
        ... | no qq = ⊥-elim (pp (w1 , e1 , p , cor , ¬isFinPath→isInfPath {i} {w1} {#IndBarB} {#IndBarC T} p (λ z → qq (lift z))))

--sem : (w : 𝕎·) → ∈Type i w #barThesis tab
--sem w  ?



{--

Plan:

(1) Prove by coinduction that if (F ∈ FunBar) then (loop F ∈ CoIndBar) which does not require to proving termination
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
