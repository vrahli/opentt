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


module barContP3 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import list(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import continuity-conds(W)(C)(K)(G)(X)(N)

open import continuity1(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity2(W)(M)(C)(K)(P)(G)(X)(N)(E)
open import continuity3(W)(M)(C)(K)(P)(G)(X)(N)(E)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)





≡→¬< : (k1 k2 m : ℕ) → k2 ≡ m → ¬ k1 < k2 → ¬ k1 < m
≡→¬< k1 k2 m e h rewrite e = h


IFLT-NUM<⇛ : {n m : ℕ} (p : n < m) (a b : Term) (w : 𝕎·) → IFLT (NUM n) (NUM m) a b ⇛ a at w
IFLT-NUM<⇛ {n} {m} p a b w w1 e1 =
  lift (⇓-from-to→⇓ {w1} {w1} {IFLT (NUM n) (NUM m) a b} {a} (IFLT-NUM<⇓ {n} {m} p a b w1))


IFLT-NUM¬<⇛ : {n m : ℕ} (p : ¬ n < m) (a b : Term) (w : 𝕎·) → IFLT (NUM n) (NUM m) a b ⇛ b at w
IFLT-NUM¬<⇛ {n} {m} p a b w w1 e1 =
  lift (⇓-from-to→⇓ {w1} {w1} {IFLT (NUM n) (NUM m) a b} {b} (IFLT-NUM¬<⇓ {n} {m} p a b w1))


→APPLY-APPENDf⇛NUM₁ : (w : 𝕎·) (j k m : ℕ) (f a b : CTerm)
                       → j < k
                       → a #⇛ #NUM j at w
                       → #APPLY f a #⇛ #NUM m at w
                       → #APPLY (#APPENDf (#NUM k) f b) a #⇛ #NUM m at w
→APPLY-APPENDf⇛NUM₁ w j k m f a b ltk compn compa =
  #⇛-trans {w} {#APPLY (#APPENDf (#NUM k) f b) a} {#IFEQ a (#NUM k) b (#APPLY f a)} {#NUM m}
            (APPLY-APPENDf⇛ w (#NUM k) f b a)
            (#⇛-trans {w} {#IFEQ a (#NUM k) b (#APPLY f a)} {#IFEQ (#NUM j) (#NUM k) b (#APPLY f a)} {#NUM m}
                       (IFEQ⇛₃ {w} {j} {k} {⌜ a ⌝} {NUM k} {⌜ b ⌝} {⌜ #APPLY f a ⌝} compn (#⇛-refl w (#NUM k)))
                       (#⇛-trans {w} {#IFEQ (#NUM j) (#NUM k) b (#APPLY f a)} {#APPLY f a} {#NUM m}
                                  (IFEQ⇛¬= {k} {j} {w} {⌜ b ⌝} {⌜ #APPLY f a ⌝} (<⇒≢ ltk))
                                  compa))


→APPLY-APPENDf⇛NUM₂ : (w : 𝕎·) (k : ℕ) (f a b : CTerm)
                       → a #⇛ #NUM k at w
                       → #APPLY (#APPENDf (#NUM k) f b) a #⇛ b at w
→APPLY-APPENDf⇛NUM₂ w k f a b compa =
  #⇛-trans {w} {#APPLY (#APPENDf (#NUM k) f b) a} {#IFEQ a (#NUM k) b (#APPLY f a)} {b}
            (APPLY-APPENDf⇛ w (#NUM k) f b a)
            (#⇛-trans {w} {#IFEQ a (#NUM k) b (#APPLY f a)} {#IFEQ (#NUM k) (#NUM k) b (#APPLY f a)} {b}
                       (IFEQ⇛₃ {w} {k} {k} {⌜ a ⌝} {NUM k} {⌜ b ⌝} {⌜ #APPLY f a ⌝} compa (#⇛-refl w (#NUM k)))
                       (IFEQ⇛= {k} {k} {w} {⌜ b ⌝} {⌜ #APPLY f a ⌝} refl))


equalInType-APPENDf-last : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm) (k : ℕ) (s : 𝕊)
                           → a₁ #⇛ #NUM k at w
                           → a₂ #⇛ #NUM k at w
                           → equalInType i w #NAT (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂)
equalInType-APPENDf-last i w f a₁ a₂ k s c1 c2 =
  →equalInType-NAT i w (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂) (Mod.∀𝕎-□ M aw)
  where
    aw : ∀𝕎 w (λ w' _ → NATeq w' (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 = s k , →APPLY-APPENDf⇛NUM₂ w1 k f a₁ (#NUM (s k)) (∀𝕎-mon e1 c1) , APPLY-MSEQ⇛ w1 s ⌜ a₂ ⌝ k (∀𝕎-mon e1 c2)


equalInType-APPENDf-last≡ : (i : ℕ) (w : 𝕎·) (f a₁ a₂ : CTerm) (j k : ℕ) (s : 𝕊)
                            → j ≡ k
                            → a₁ #⇛ #NUM j at w
                            → a₂ #⇛ #NUM j at w
                            → equalInType i w #NAT (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂)
equalInType-APPENDf-last≡ i w f a₁ a₂ j k s e c1 c2 rewrite e = equalInType-APPENDf-last i w f a₁ a₂ k s c1 c2


→equalInType-BAIREn-suc-APPENDf : (i : ℕ) (w : 𝕎·) (k : ℕ) (s : 𝕊) (f : CTerm)
                                   → equalInType i w (#BAIREn (#NUM k)) f (#MSEQ s)
                                   → equalInType i w (#BAIREn (#NUM (suc k))) (#APPENDf (#NUM k) f (#NUM (s k))) (#MSEQ s)
→equalInType-BAIREn-suc-APPENDf i w k s f eqb =
  equalInType-FUN
    (→equalTypesNATn i w (#NUM (suc k)) (#NUM (suc k)) (NUM-equalInType-NAT i w (suc k)))
    eqTypesNAT
    aw
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) →  equalInType i w' (#NATn (#NUM (suc k))) a₁ a₂
                       → equalInType i w' #NAT (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ eqa = equalInType-local (Mod.∀𝕎-□Func M aw1 eqa1)
      where
        eqa1 : □· w1 (λ w' _ → Σ ℕ (λ j → a₁ #⇛ #NUM j at w' × a₂ #⇛ #NUM j at w' × j < suc k))
        eqa1 = equalInType-NATn→ {i} {w1} {suc k} {#NUM (suc k)} {a₁} {a₂} (#⇛-refl w1 (#NUM (suc k))) eqa

        aw1 : ∀𝕎 w1 (λ w' e' → Σ ℕ (λ j → a₁ #⇛ #NUM j at w' × a₂ #⇛ #NUM j at w' × j < suc k)
                              → equalInType i w' #NAT (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (j , c1 , c2 , ltk) with j <? k
        ... | yes p =
          →equalInType-NAT
            i w2 (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂)
            (Mod.∀𝕎-□Func M aw3 (equalInType-NAT→ i w2 (#APPLY f a₁) (#APPLY (#MSEQ s) a₂) eqa2))
          where
            aw3 : ∀𝕎 w2 (λ w' e' → NATeq w' (#APPLY f a₁) (#APPLY (#MSEQ s) a₂)
                                  → NATeq w' (#APPLY (#APPENDf (#NUM k) f (#NUM (s k))) a₁) (#APPLY (#MSEQ s) a₂))
            aw3 w3 e3 (m , d1 , d2) = m , →APPLY-APPENDf⇛NUM₁ w3 j k m f a₁ (#NUM (s k)) p (∀𝕎-mon e3 c1) d1 , d2

            aw2 : ∀𝕎 w2 (λ w' _ → Σ ℕ (λ k₁ → a₁ #⇛ #NUM k₁ at w' × a₂ #⇛ #NUM k₁ at w' × k₁ < k))
            aw2 w3 e3 = j , ∀𝕎-mon e3 c1 , ∀𝕎-mon e3 c2 , p

            eqn1 : equalInType i w2 (#NATn (#NUM k)) a₁ a₂
            eqn1 = →equalInType-NATn {i} {w2} {k} {#NUM k} {a₁} {a₂} (#⇛-refl w2 (#NUM k)) (Mod.∀𝕎-□ M aw2)

            eqa2 : equalInType i w2 #NAT (#APPLY f a₁) (#APPLY (#MSEQ s) a₂)
            eqa2 = equalInType-FUN→ eqb w2 (⊑-trans· e1 e2) a₁ a₂ eqn1
        ... | no p = equalInType-APPENDf-last≡ i w2 f a₁ a₂ j k s eqk c1 c2
          where
            eqk : j ≡ k
            eqk = <s→¬<→≡ {j} {k} ltk p


seq2list : (s : 𝕊) (n : ℕ) → CTerm
seq2list s 0 = #INIT
seq2list s (suc n) = #APPENDf (#NUM n) (seq2list s n) (#NUM (s n))


seq2list+suc : (s : 𝕊) (n k : ℕ) → seq2list s (n + suc k) ≡ seq2list s (suc (n + k))
seq2list+suc s n k rewrite +-suc n k = refl


correctSeqN-inv : (i : ℕ) (r : Name) (w : 𝕎·) (F : CTerm) (s : 𝕊) (k n : ℕ)
                  → correctSeqN r w F k (seq2list s k) s (suc n)
                  → Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
                      #APPLY F (#upd r (seq2list s (n + k))) #⇓ #NUM m from (chooseT r w N0) to w'
                      × getT 0 r w' ≡ just (NUM j)
                      × ¬ j < n + k)))
correctSeqN-inv i r w F s k 0 (m , w' , j , comp , gt0 , nlt , cor) = m , w' , j , comp , gt0 , nlt
correctSeqN-inv i r w F s k (suc n) (m , w' , j , comp , gt0 , nlt , cor) =
  fst ind , fst (snd ind) , fst (snd (snd ind)) ,
  comp' (fst (snd (snd (snd ind)))) ,
  fst (snd (snd (snd (snd ind)))) ,
  nlt'
  where
    ind : Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
            #APPLY F (#upd r (seq2list s (n + suc k))) #⇓ #NUM m from (chooseT r w N0) to w'
            × getT 0 r w' ≡ just (NUM j)
            × ¬ j < n + suc k)))
    ind = correctSeqN-inv i r w F s (suc k) n cor

    comp' : #APPLY F (#upd r (seq2list s (n + suc k))) #⇓ #NUM (fst ind) from (chooseT r w N0) to fst (snd ind)
            → #APPLY F (#upd r (seq2list s (suc (n + k)))) #⇓ #NUM (fst ind) from (chooseT r w N0) to fst (snd ind)
    comp' x rewrite +-suc n k = x

    nlt' : ¬ fst (snd (snd ind)) < suc (n + k)
    nlt' rewrite sym (+-suc n k) = snd (snd (snd (snd (snd ind))))


correctSeqN-inv2 : (i : ℕ) (r : Name) (w : 𝕎·) (F f : CTerm) (s : 𝕊) (k n : ℕ)
                   → equalInType i w (#BAIREn (#NUM k)) f (#MSEQ s)
                   → correctSeqN r w F k f s (suc n)
                   → Σ CTerm (λ f' → Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
                       #APPLY F (#upd r f') #⇓ #NUM m from (chooseT r w N0) to w'
                       × equalInType i w (#BAIREn (#NUM (n + k))) f' (#MSEQ s)
                       × getT 0 r w' ≡ just (NUM j)
                       × ¬ j < n + k))))
correctSeqN-inv2 i r w F f s k 0 eqb (m , w' , j , comp , gt0 , nlt , cor) = f , m , w' , j , comp , eqb , gt0 , nlt
correctSeqN-inv2 i r w F f s k (suc n) eqb (m , w' , j , comp , gt0 , nlt , cor) =
  fst ind , fst (snd ind) , fst (snd (snd ind)) , fst (snd (snd (snd ind))) ,
  fst (snd (snd (snd (snd ind)))) ,
  eqb' ,
  fst (snd (snd (snd (snd (snd (snd ind)))))) ,
  nlt'
  where
    ind : Σ CTerm (λ f' → Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
            #APPLY F (#upd r f') #⇓ #NUM m from (chooseT r w N0) to w'
            × equalInType i w (#BAIREn (#NUM (n + suc k))) f' (#MSEQ s)
            × getT 0 r w' ≡ just (NUM j)
            × ¬ j < n + suc k))))
    ind = correctSeqN-inv2 i r w F (#APPENDf (#NUM k) f (#NUM (s k))) s (suc k) n
                          (→equalInType-BAIREn-suc-APPENDf i w k s f eqb) cor

    eqb' : equalInType i w (#BAIREn (#NUM (suc (n + k)))) (fst ind)  (#MSEQ s)
    eqb' rewrite sym (+-suc n k) = fst (snd (snd (snd (snd (snd ind)))))

    nlt' : ¬ fst (snd (snd (snd ind))) < suc (n + k)
    nlt' rewrite sym (+-suc n k) = snd (snd (snd (snd (snd (snd (snd ind))))))


𝕊∷ : (k m : ℕ) (s : 𝕊) → 𝕊
𝕊∷ 0 m s = ∷𝕊 m s
𝕊∷ (suc k) m s = ∷𝕊 (s 0) (𝕊∷ k m (shift𝕊 s))


-- n is the fuel
-- k is the length of f
corSeqN : (r : Name) (w : 𝕎·) (F : CTerm) (k : ℕ) (f : CTerm) (s : 𝕊) (n : ℕ) → Set(lsuc L)
corSeqN r w F k f s 0 = Lift (lsuc L) ⊤
corSeqN r w F k f s (suc n) =
  Σ ℕ (λ m → Σ 𝕎· (λ w' → Σ ℕ (λ j →
    #APPLY F (#upd r f) #⇓ #NUM m from (chooseT r w N0) to w'
    × getT 0 r w' ≡ just (NUM j)
    × ¬ j < k
    × corSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s 0))) (shift𝕊 s) n)))


corSeq : (r : Name) (w : 𝕎·) (F : CTerm) (s : 𝕊) → Set(lsuc L)
corSeq r w F s = (n : ℕ) → corSeqN r w F 0 #INIT s n


→≡corSeqN : (r : Name) (w : 𝕎·) (F : CTerm) (k : ℕ) (f : CTerm) (s1 s2 : 𝕊) (n : ℕ)
             → ((k : ℕ) → s1 k ≡ s2 k)
             → corSeqN r w F k f s1 n
             → corSeqN r w F k f s2 n
→≡corSeqN r w F k f s1 s2 0 imp cor = cor
→≡corSeqN r w F k f s1 s2 (suc n) imp (m , w' , j , x , y , z , c) =
  m , w' , j , x , y , z , ind2
  where
    ind1 : corSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s1 0))) (shift𝕊 s2) n
    ind1 = →≡corSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s1 0))) (shift𝕊 s1) (shift𝕊 s2) n (λ j → imp (suc j)) c

    ind2 : corSeqN r w F (suc k) (#APPENDf (#NUM k) f (#NUM (s2 0))) (shift𝕊 s2) n
    ind2 rewrite sym (imp 0) = ind1



++𝕊0 : (m : ℕ) (s0 s : 𝕊) → ++𝕊 m s0 s m ≡ s 0
++𝕊0 0 s0 s = refl
++𝕊0 (suc m) s0 s = ++𝕊0 m (shift𝕊 s0) s


≡∷𝕊 : {k m : ℕ} {s1 s2 : 𝕊} → ((n : ℕ) → s1 n ≡ s2 n) → ∷𝕊 k s1 m ≡ ∷𝕊 k s2 m
≡∷𝕊 {k} {0} {s1} {s2} imp = refl
≡∷𝕊 {k} {suc m} {s1} {s2} imp = imp m


≡++𝕊 : {k m : ℕ} {sa sb s : 𝕊} → ((n : ℕ) → sa n ≡ sb n) → ++𝕊 k sa s m ≡ ++𝕊 k sb s m
≡++𝕊 {0} {m} {sa} {sb} {s} imp = refl
≡++𝕊 {suc k} {m} {sa} {sb} {s} imp rewrite imp 0 =
  ≡∷𝕊 {sb 0} {m} λ n → ≡++𝕊 {k} {n} (λ z → imp (suc z))


∷𝕊≡++𝕊 : (m : ℕ) (s0 s : 𝕊) (k : ℕ) →  ∷𝕊 (𝕊∷ m (s 0) s0 0) (++𝕊 m (shift𝕊 (𝕊∷ m (s 0) s0)) (shift𝕊 s)) k ≡ ++𝕊 m s0 s k
∷𝕊≡++𝕊 0 s0 s 0 = refl
∷𝕊≡++𝕊 0 s0 s (suc k) = refl
∷𝕊≡++𝕊 (suc m) s0 s 0 = refl
∷𝕊≡++𝕊 (suc m) s0 s (suc k) = c
  where
    a : (k : ℕ) → ++𝕊 m
                        (shift𝕊 (shift𝕊 (∷𝕊 (s0 0) (𝕊∷ m (s 0) (shift𝕊 s0))))) -- need to replace with (shift𝕊 (𝕊∷ m (s 0) (shift𝕊 s0)))
                        (shift𝕊 s)
                        k
                   ≡ ++𝕊 m (shift𝕊 (𝕊∷ m (s 0) (shift𝕊 s0))) (shift𝕊 s) k
    a k = ≡++𝕊 {m} {k} (λ n → refl)

    c : ∷𝕊 (𝕊∷ m (s 0) (shift𝕊 s0) 0)
             (++𝕊 m
                   (shift𝕊 (shift𝕊 (∷𝕊 (s0 0) (𝕊∷ m (s 0) (shift𝕊 s0))))) -- need to replace with (shift𝕊 (𝕊∷ m (s 0) (shift𝕊 s0)))
                   (shift𝕊 s))

             k
        ≡ ++𝕊 m (shift𝕊 s0) s k
    c = trans (≡∷𝕊 {𝕊∷ m (s 0) (shift𝕊 s0) 0} {k} a) (∷𝕊≡++𝕊 m (shift𝕊 s0) s k)


-- n is the fuel
-- m is the length of f
corSeqN→correctSeqN : (r : Name) (w : 𝕎·) (m n : ℕ) (F f : CTerm) (s0 s : 𝕊)
                       → corSeqN r w F m f s n
                       → correctSeqN r w F m f (++𝕊 m s0 s) n
corSeqN→correctSeqN r w m 0 F f s0 s cor = cor
corSeqN→correctSeqN r w m (suc n) F f s0 s (z , w' , j , comp , gt0 , nlt , cor) =
  z , w' , j , comp , gt0 , nlt , ind2
  where
    ind : correctSeqN r w F (suc m) (#APPENDf (#NUM m) f (#NUM (s 0))) (++𝕊 (suc m) (𝕊∷ m (s 0) s0) (shift𝕊 s)) n
    ind = corSeqN→correctSeqN r w (suc m) n F (#APPENDf (#NUM m) f (#NUM (s 0))) (𝕊∷ m (s 0) s0) (shift𝕊 s) cor

    imp : (k : ℕ) →  ∷𝕊 (𝕊∷ m (s 0) s0 0) (++𝕊 m (shift𝕊 (𝕊∷ m (s 0) s0)) (shift𝕊 s)) k ≡ ++𝕊 m s0 s k
    imp = ∷𝕊≡++𝕊 m s0 s

    ind1 : correctSeqN r w F (suc m) (#APPENDf (#NUM m) f (#NUM (s 0))) (++𝕊 m s0 s) n
    ind1 = →≡correctSeqN
             r w F (suc m) (#APPENDf (#NUM m) f (#NUM (s 0)))
             (++𝕊 (suc m) (𝕊∷ m (s 0) s0) (shift𝕊 s)) (++𝕊 m s0 s)
             n imp ind

    ind2 : correctSeqN r w F (suc m) (#APPENDf (#NUM m) f (#NUM (++𝕊 m s0 s m))) (++𝕊 m s0 s) n
    ind2 rewrite ++𝕊0 m s0 s = ind1


corSeq→correctSeq : (r : Name) (w : 𝕎·) (F : CTerm) (s : 𝕊)
                     → corSeq r w F s
                     → correctSeq r w F s
corSeq→correctSeq r w F s cor n = corSeqN→correctSeqN r w 0 n F #INIT s s (cor n)


-- n is the fuel
→corSeqN : (kb : K□) (cn : cℕ) (i : ℕ) (r : Name) (t F g : CTerm) (m : ℕ) (n : ℕ) (w : 𝕎·)
                → compatible· r w Res⊤
                → ∈Type i w #FunBar F
--                → ∈Type i w (#LIST #NAT) l
--                → l #⇛ #PAIR z g at w
--                → z #⇛! #NUM m at w
--                → ∈Type i w #BAIRE g
                → (p : path i w #IndBarB #IndBarC)
                → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
                → t #⇓! #APPLY2 (#loop r F) (#NUM m) g at w
                → correctPathN {i} {w} {#IndBarB} {#IndBarC} t p n
                → corSeqN r w F m g (path2𝕊 kb p) n
→corSeqN kb cn i r t F g m 0 w compat F∈ {--g∈--} p inf compt cor = lift tt
→corSeqN kb cn i r t F g m (suc n) w compat F∈ {--g∈--} p inf compt cor with inf 0
... | inf0 with p 0
... |    inj₁ (a , b , ia , ib) with cor
... |       (f , comp , cp) =
  k , w' , k1 , compF1 , compG0 , nlt , ind
  where
--    compz' : z #⇛ #NUM m at w
--    compz' = #⇛!-#⇛ {w} {z} {#NUM m} compz

--    comp0 : t #⇛ #SUP a f at w
--    comp0 = comp

    comp1 : #APPLY2 (#loop r F) (#NUM m) g #⇓ #SUP a f at w
    comp1 = val-⇓→ {w} {w} {⌜ t ⌝} {⌜ #APPLY2 (#loop r F) (#NUM m) g ⌝} {⌜ #SUP a f ⌝} tt compt (lower (comp w (⊑-refl· w)))

{--
-- Get all that from comp1? We're still uing F∈ and l∈ here.
    F∈1 : ∈Type i w #NAT (#APPLY F (#upd r g))
    F∈1 = ∈BAIRE→NAT→
             {i} {w} {F} {F} {#upd r g} {#upd r g}
             F∈
             (upd∈BAIRE cn i w r g compat g∈)

    F∈2 : NATmem w (#APPLY F (#upd r g))
    F∈2 = kb (equalInType-NAT→ i w (#APPLY F (#upd r g)) (#APPLY F (#upd r g)) F∈1) w (⊑-refl· w)

    k : ℕ
    k = fst F∈2
--}

    compF : Σ ℕ (λ k → Σ 𝕎· (λ w' → Σ ℕ (λ k1 → Σ ℕ (λ k2 →
              #APPLY F (#upd r g) #⇓ #NUM k from (chooseT r w N0) to w'
              × getT 0 r w' ≡ just (NUM k1)
              × #NUM m #⇓ #NUM k2 at w'
              × ((k1 < k2 × a ≡ #INL (#NUM k) × f ≡ #AX)
                 ⊎ (¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g))))))
    compF = #APPLY-loop⇓SUP→ cn w r F (#NUM m) g a f {--k--} compat {--(fst (snd F∈2))--} comp1

    k : ℕ
    k = fst compF

    w' : 𝕎·
    w' = fst (snd compF)

    k1 : ℕ
    k1 = fst (snd (snd compF))

    k2 : ℕ
    k2 = fst (snd (snd (snd compF)))

    compF1 : #APPLY F (#upd r g) #⇓ #NUM k from (chooseT r w N0) to w'
    compF1 = fst (snd (snd (snd (snd compF))))
--

    compG0 : getT 0 r w' ≡ just (NUM k1)
    compG0 = fst (snd (snd (snd (snd (snd compF)))))

    compFL : #NUM m #⇓ #NUM k2 at w'
    compFL = fst (snd (snd (snd (snd (snd (snd compF))))))

    e' : w ⊑· w'
    e' = ⊑-trans· (choose⊑· r w (T→ℂ· N0)) (⇓from-to→⊑ {chooseT r w N0} {w'} {APPLY ⌜ F ⌝ (upd r ⌜ g ⌝)} {NUM k} compF1)

    eqm : k2 ≡ m
    eqm = NUMinj (sym (compVal (NUM m) (NUM k2) w' compFL tt))

    ia' : Σ CTerm (λ t → a #⇛! #INR t at w)
    ia' = fst (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))

    ib' : Σ ℕ (λ n → b #⇛! #NUM n at w)
    ib' = snd (kb (∈Type-IndBarB-IndBarC→ i w a b ia ib) w (⊑-refl· w))

    bn : ℕ
    bn = fst ib'

    compF2 : (k1 < k2 × a ≡ #INL (#NUM k) × f ≡ #AX) ⊎ (¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g)
             → ¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g
    compF2 (inj₁ (x , y , z)) = ⊥-elim (#INL→¬#⇛!#INR w a (#NUM k) (proj₁ ia') y (snd ia'))
    compF2 (inj₂ x) = x

    compF3 : ¬ k1 < k2 × a ≡ #INR #AX × f ≡ #loopR (#loop r F) (#NUM m) g
    compF3 = compF2 (snd (snd (snd (snd (snd (snd (snd compF)))))))

    nlt : ¬ k1 < m
    nlt = ≡→¬< k1 k2 m eqm (fst compF3)

    cp1 : correctPathN {i} {w} {#IndBarB} {#IndBarC} (#APPLY f b) (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
    cp1 = cp

    cp2 : correctPathN {i} {w} {#IndBarB} {#IndBarC} (#APPLY (#loopR (#loop r F) (#NUM m) g) b) (shiftPath {i} {w} {#IndBarB} {#IndBarC} p) n
    cp2 = ≡→correctPathN
            {i} {w} {#IndBarB} {#IndBarC} (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)
            {#APPLY f b} {#APPLY (#loopR (#loop r F) (#NUM m) g) b} n (→≡#APPLY (snd (snd compF3)) refl) cp1

    ind1 : corSeqN r w F (suc m) (#APPENDf (#NUM m) g (#NUM bn)) (path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)) n
    ind1 = →corSeqN
             kb cn i r (#APPLY (#loopR (#loop r F) (#NUM m) g) b) F
             (#APPENDf (#NUM m) g (#NUM bn)) (suc m)
             n w compat F∈
             {--(APPENDf∈BAIRE
               {i} {w} {#NUM m} {#NUM m} {g} {g} {#NUM bn} {#NUM bn}
               (NUM-equalInType-NAT i w m)
               (NUM-equalInType-NAT i w bn)
               g∈)--}
             (shiftPath {i} {w} {#IndBarB} {#IndBarC} p)
             (isInfPath-shiftPath {i} {w} {#IndBarB} {#IndBarC} p inf)
             (APPLY-loopR-⇓ w w w (#loop r F) (#NUM m) g b bn m (lower (snd ib' w (⊑-refl· w))) (⇓!-refl (NUM m) w))
             cp2

    ind : corSeqN r w F (suc m) (#APPENDf (#NUM m) g (#NUM bn)) (shift𝕊 (path2𝕊 kb p)) n
    ind = →≡corSeqN r w F (suc m) (#APPENDf (#NUM m) g (#NUM bn))
            (path2𝕊 kb (shiftPath {i} {w} {#IndBarB} {#IndBarC} p))
            (shift𝕊 (path2𝕊 kb p))
            n (λ z → sym (shift-path2𝕊 kb {i} {w} p z)) ind1


→corSeq : (kb : K□) (cb : cℕ) (i : ℕ) (w : 𝕎·) (r : Name) (F : CTerm)
               → compatible· r w Res⊤
               → ∈Type i w #FunBar F
               → (p : path i w #IndBarB #IndBarC)
               → correctPath {i} {w} {#IndBarB} {#IndBarC} (#APPLY2 (#loop r F) (#NUM 0) #INIT) p
               → isInfPath {i} {w} {#IndBarB} {#IndBarC} p
               → corSeq r w F (path2𝕊 kb p)
→corSeq kb cb i w r F compat F∈ p cor inf n =
  →corSeqN
    kb cb i r (#APPLY2 (#loop r F) (#NUM 0) #INIT) F #INIT 0 n w compat F∈
    {--(LAM0∈BAIRE i w)--}
    p inf (#⇓!-refl (#APPLY2 (#loop r F) (#NUM 0) #INIT) w) (cor n)


{--
infPath-mon :  {i : ℕ} {w1 w2 : 𝕎·} {B : CTerm} {C : CTerm0} {t : CTerm}
               → w1 ⊑· w2
               → (p : path i w1 B C)
               → correctPath {i} {w1} {B} {C} t p
               → isInfPath {i} {w1} {B} {C} p
               → Σ (path i w2 B C) (λ q → correctPath {i} {w2} {B} {C} t q × isInfPath {i} {w2} {B} {C} q)
infPath-mon {i} {w1} {w2} {B} {C} {t} e p cor inf = {!!}
--}


mseq∈baire : (i : ℕ) (w : 𝕎·) (s : 𝕊) → ∈Type i w #BAIRE (#MSEQ s)
mseq∈baire i w s =
  ≡CTerm→equalInType (sym #BAIRE≡) (equalInType-FUN eqTypesNAT eqTypesNAT aw)
  where
    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                      → equalInType i w' #NAT (#APPLY (#MSEQ s) a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ eqa =
      →equalInType-NAT
        i w1 (#APPLY (#MSEQ s) a₁) (#APPLY (#MSEQ s) a₂)
        (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 a₁ a₂ eqa))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂ → NATeq w' (#APPLY (#MSEQ s) a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (k , c1 , c2) = s k , APPLY-MSEQ⇛ w2 s ⌜ a₁ ⌝ k c1 , APPLY-MSEQ⇛ w2 s ⌜ a₂ ⌝ k c2

\end{code}
