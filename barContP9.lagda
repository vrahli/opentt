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


module barContP9 {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
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
open import terms8(W)(C)(K)(G)(X)(N)(EC) using (#APPLY2 ; #⇛-trans ; #INL¬≡INR ; APPLY-MSEQ⇛)
open import terms9 using (#BAIRE!) --(W)(C)(K)(G)(X)(N)(EC)

open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (eqTypes-mon)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (#⇛-refl)

open import choiceDef{L}(C)
open import compatibleDef{L}(W)(C)(K)
open import getChoiceDef(W)(C)(K)(G)
open import newChoiceDef(W)(C)(K)(G)(N)
open import choiceExtDef(W)(C)(K)(G)(X)

--open import props1(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (TSext-equalTypes-equalInType)
open import props2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (equalInType-trans ; equalInType-#⇛-LR)
open import props4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC) using (→equalInType-NAT! ; equalInType-W→)
--open import props5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import pure(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

open import props_w(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)

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
--open import continuitySMb(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (isHighestℕ≤)

open import barContP(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (#INIT ; #APPLY-loop⇓SUP→ ; #⇛!-NUM-type)
open import barContP3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (seq2list ; mseq∈baire)
open import barContP4(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
--open import barContP5(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP6(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
  using (#FunBarP ; sem ; #updSeq-APPLY-updr ; updSeq-steps-NUM ; seq2list≡ ; #¬Names-seq2list)
open import barContP7(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC)
open import barContP8(W)(M)(C)(K)(P)(G)(X)(N)(E)(EM)(EC) using (follow-NUM-ETA ; type-#⇛-NUM)


abstract

  follow-NUM : (kb : K□) (can : comp→∀ℕ) (gc : get-choose-ℕ) (cn : cℕ)
               (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T I J F : CTerm) (s : 𝕊) (k n : ℕ)
               → #¬Names F
               → P 0
               → ((n : ℕ) → P (s n))
               → #⇛!-NUM-type P T
               → type-#⇛-NUM P T
               → type-preserves-#⇛ T
               → isType i w T
               → I #⇛! #tab F k (seq2list s k) at w
               → weq₀ (equalInType i w #IndBarB) (λ a b eqa → equalInType i w (sub0 a (#IndBarC T))) w I J
               → ∈Type i w (#FunBar T) F
               → #APPLY F (#MSEQ s) #⇛ #NUM n at w
               → #follow (#MSEQ s) I k #⇛ #NUM n at w
  follow-NUM kb can gc cn i w P T I J F s k n nnF p0 ps nty tyn prest tyt cI (weqC₀ a1 f1 a2 f2 e c1 c2 ind) F∈ comp
    with #APPLY-#loop#⇓5
           kb can gc cn i T F (#NUM k) (seq2list s k)
           k w (#¬Names-seq2list s k) nnF prest tyt (#⇛!-refl {w} {#NUM k}) F∈
           (∈Type-NAT→T-seq2list i w s k P T p0 ps nty prest tyt)
  ... | inj₁ c3 =
    follow-NUM-ETA
      kb can gc cn i w P T I F s k n
      (fst c3)
      nnF ps tyn nty prest tyt cI F∈ comp (snd c3)
  ... | inj₂ c3 =
    #⇛-trans
      {w}
      {#follow (#MSEQ s) I k}
      {#follow (#MSEQ s) (#APPLY f1 (#NUM (s k))) (suc k)}
      {#NUM n}
      (#⇛-trans
        {w}
        {#follow (#MSEQ s) I k}
        {#follow (#MSEQ s) (#APPLY (#loopR (#loop F) (#NUM k) (seq2list s k)) (#NUM (s k))) (suc k)}
        {#follow (#MSEQ s) (#APPLY f1 (#NUM (s k))) (suc k)}
        c5
        (≡ₗ→#⇛
          w
          (#follow (#MSEQ s) (#APPLY (#loopR (#loop F) (#NUM k) (seq2list s k)) (#NUM (s k))) (suc k))
          (#follow (#MSEQ s) (#APPLY f1 (#NUM (s k))) (suc k))
          (≡#follow
            (#MSEQ s) (#MSEQ s)
            (#APPLY (#loopR (#loop F) (#NUM k) (seq2list s k)) (#NUM (s k))) (#APPLY f1 (#NUM (s k)))
            (suc k) (suc k)
            refl (CTerm≡ (≡APPLY (≡CTerm (sym ef1)) refl)) refl)))
      ind'
    where
      abstract
        c4 : #APPLY2 (#loop F) (#NUM k) (seq2list s k) #⇛ #DIGAMMA (#loopR (#loop F) (#NUM k) (seq2list s k)) at w
        c4 = c3

        c5 : #follow (#MSEQ s) I k #⇛ #follow (#MSEQ s) (#APPLY (#loopR (#loop F) (#NUM k) (seq2list s k)) (#NUM (s k))) (suc k) at w
        c5 = #follow-INR⇛
               w I (#INR #AX) (#loopR (#loop F) (#NUM k) (seq2list s k)) (#MSEQ s) #AX k (s k)
               (#⇛-trans {w} {I} {#tab F k (seq2list s k)} {#DIGAMMA (#loopR (#loop F) (#NUM k) (seq2list s k))} (#⇛!→#⇛ {w} {I} {#tab F k (seq2list s k)} cI) c3)
               (#⇛!-refl {w} {#INR #AX})
               (#APPLY-MSEQ-NUM#⇛! s k w)

        ea1 : a1 ≡ #INR #AX
        ea1 = fst (#⇛SUP→× w I (#tab F k (seq2list s k)) a1 f1 (#INR #AX) (#loopR (#loop F) (#NUM k) (seq2list s k)) cI c1 c3)

        ef1 : f1 ≡ #loopR (#loop F) (#NUM k) (seq2list s k)
        ef1 = snd (#⇛SUP→× w I (#tab F k (seq2list s k)) a1 f1 (#INR #AX) (#loopR (#loop F) (#NUM k) (seq2list s k)) cI c1 c3)

        eqb : ∈Type i w (sub0 a1 (#IndBarC T)) (#NUM (s k))
        eqb = NUM∈sub0-IndBarc i w P T a1 #AX (s k) (ps k) nty (≡ₗ→#⇛! w a1 (#INR #AX) ea1)

        c6 : #APPLY f1 (#NUM (s k)) #⇛! #tab F (suc k) (seq2list s (suc k)) at w
        c6 = #⇛!-trans
               {w}
               {#APPLY f1 (#NUM (s k))}
               {#APPLY (#loopR (#loop F) (#NUM k) (seq2list s k)) (#NUM (s k))}
               {#tab F (suc k) (seq2list s (suc k))}
               (≡ₗ→#⇛! w (#APPLY f1 (#NUM (s k)))
                 (#APPLY (#loopR (#loop F) (#NUM k) (seq2list s k)) (#NUM (s k)))
                 (CTerm≡ (≡APPLY (≡CTerm ef1) refl)))
               (APPLY-loopR-NUM⇛! w (#loop F) (seq2list s k) (s k) k)

        ind' : #follow (#MSEQ s) (#APPLY f1 (#NUM (s k))) (suc k) #⇛ #NUM n at w
        ind' = follow-NUM
                 kb can gc cn i w P T
                 (#APPLY f1 (#NUM (s k)))
                 (#APPLY f2 (#NUM (s k)))
                 F s (suc k) n nnF
                 p0 ps nty tyn prest tyt
                 c6
                 (ind (#NUM (s k)) (#NUM (s k)) eqb)
                 F∈ comp


type-#⇛-NUM→! : (P : ℕ → Set) (T : CTerm)
                  → type-#⇛-NUM P T
                  → type-#⇛!-NUM P T
type-#⇛-NUM→! P T tyn {i} {w} {a} {b} a∈ =
  Mod.□-idem M (Mod.∀𝕎-□Func M aw (equalInTypeNOWRITEMOD→ a∈))
  where
    aw : ∀𝕎 w (λ w' e' → NOWRITEMODeq (equalInType i w' T) w' a b
                        → □· w' (↑wPred' (λ w'' _ → Σ ℕ (λ n → a #⇛! #NUM n at w'' × b #⇛! #NUM n at w'' × P n)) e'))
    aw w1 e1 (h , c₁ , c₂) = Mod.∀𝕎-□Func M aw1 (tyn {i} {w1} {a} {b} h)
      where
        aw1 : ∀𝕎 w1 (λ w' e' → Σ ℕ (λ n → a #⇛ #NUM n at w' × b #⇛ #NUM n at w' × P n)
                              → ↑wPred' (λ w'' _ → Σ ℕ (λ n → a #⇛! #NUM n at w'' × b #⇛! #NUM n at w'' × P n)) e1 w' e')
        aw1 w2 e2 (n , d₁ , d₂ , pn) z = n , #⇛→#⇛! {w2} {a} {#NUM n} (∀𝕎-mon e2 c₁) tt d₁ , #⇛→#⇛! {w2} {b} {#NUM n} (∀𝕎-mon e2 c₂) tt d₂ , pn


NAT→T!2𝕊 : (kb : K□) {i : ℕ} {w : 𝕎·} (P : ℕ → Set) {T f : CTerm}
             (tyn : type-#⇛!-NUM P T) (f∈ : ∈Type i w (#FUN #NAT (#NOWRITEMOD T)) f) → 𝕊
NAT→T!2𝕊 kb {i} {w} P {T} {f} tyn f∈ n = fst j
  where
    j : Σ ℕ (λ k → #APPLY f (#NUM n) #⇛! #NUM k at w × #APPLY f (#NUM n) #⇛! #NUM k at w × P k)
    j = kb (tyn {i} {w} {#APPLY f (#NUM n)} {#APPLY f (#NUM n)} (equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)) ) w (⊑-refl· w)


NAT→T!2𝕊-P : (kb : K□) {i : ℕ} {w : 𝕎·} (P : ℕ → Set) {T f : CTerm}
             (tyn : type-#⇛!-NUM P T) (f∈ : ∈Type i w (#FUN #NAT (#NOWRITEMOD T)) f)
             (n : ℕ) → P (NAT→T!2𝕊 kb P tyn f∈ n)
NAT→T!2𝕊-P kb {i} {w} P {T} {f} tyn f∈ n
  with kb (tyn {i} {w} {#APPLY f (#NUM n)} {#APPLY f (#NUM n)} (equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM n) (#NUM n) (NUM-equalInType-NAT i w n)) ) w (⊑-refl· w)
... | k , c₁ , c₂ , pk = pk


NAT→T2𝕊-equalIn-NAT→T : (kb : K□) {i : ℕ} {w : 𝕎·} (P : ℕ → Set) {T f : CTerm}
                          (tyn : type-#⇛!-NUM P T) (f∈ : ∈Type i w (#FUN #NAT (#NOWRITEMOD T)) f)
                          → isType i w T
                          → #⇛!-NUM-type P T
                          → type-preserves-#⇛ T
                          → equalInType i w (#FUN #NAT T) f (#MSEQ (NAT→T!2𝕊 kb P tyn f∈))
NAT→T2𝕊-equalIn-NAT→T kb {i} {w} P {T} {f} tyn f∈ tyt nty prest =
  equalInType-FUN eqTypesNAT tyt aw
  where
    s : 𝕊
    s = NAT→T!2𝕊 kb P tyn f∈

    aw : ∀𝕎 w (λ w' _ → (a₁ a₂ : CTerm) → equalInType i w' #NAT a₁ a₂
                       → equalInType i w' T (#APPLY f a₁) (#APPLY (#MSEQ s) a₂))
    aw w1 e1 a₁ a₂ ea =
      equalInType-local (Mod.∀𝕎-□Func M aw1 (equalInType-NAT→ i w1 a₁ a₂ ea))
      where
        aw1 : ∀𝕎 w1 (λ w' e' → NATeq w' a₁ a₂
                              → equalInType i w' T (#APPLY f a₁) (#APPLY (#MSEQ s) a₂))
        aw1 w2 e2 (k , c₁ , c₂) =
          equalInType-local (Mod.∀𝕎-□Func M aw2 (tyn (equalInType-FUN→ f∈ w2 (⊑-trans· e1 e2) a₁ (#NUM k) (#⇛NUM→equalInType-NAT i w2 a₁ k c₁))))
            where
              aw2 : ∀𝕎 w2 (λ w' e' → Σ ℕ (λ n → #APPLY f a₁ #⇛! #NUM n at w' × #APPLY f (#NUM k) #⇛! #NUM n at w' × P n)
                                    → equalInType i w' T (#APPLY f a₁) (#APPLY (#MSEQ s) a₂))
              aw2 w3 e3 (n , d₁ , d₂ , pn) =
                prest i w3 (#APPLY f a₁) (#NUM n) (#APPLY (#MSEQ s) a₂) (#NUM n)
                      (#⇛!→#⇛ {w3} {#APPLY f a₁} {#NUM n} d₁)
                      comp
                      (nty {i} {w3} {n} pn)
                where
                  eqn : n ≡ s k
                  eqn with kb (tyn {i} {w} {#APPLY f (#NUM k)} {#APPLY f (#NUM k)} (equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM k) (#NUM k) (NUM-equalInType-NAT i w k))) w (⊑-refl· w)
                  ... | j , x₁ , x₂ , pj = #NUMinj (#⇛-val-det {w3} {#APPLY f (#NUM k)} {#NUM n} {#NUM j} tt tt (#⇛!→#⇛ {w3} {#APPLY f (#NUM k)} {#NUM n} d₂) (∀𝕎-mon (⊑-trans· e1 (⊑-trans· e2 e3)) (#⇛!→#⇛ {w} {#APPLY f (#NUM k)} {#NUM j} x₁)))

                  comp : #APPLY (#MSEQ s) a₂ #⇛ #NUM n at w3
                  comp rewrite eqn = APPLY-MSEQ⇛ w3 s ⌜ a₂ ⌝ k (∀𝕎-mon e3 c₂)


type-preserves-#⇛-NOWRITEMOD : {T : CTerm} {i : ℕ} {w : 𝕎·} {a₁ a₂ b₁ b₂ : CTerm}
                            → type-preserves-#⇛ T
                            → a₁ #⇛! a₂ at w
                            → b₁ #⇛! b₂ at w
                            → equalInType i w (#NOWRITEMOD T) a₂ b₂
                            → equalInType i w (#NOWRITEMOD T) a₁ b₁
type-preserves-#⇛-NOWRITEMOD {T} {i} {w} {a₁} {a₂} {b₁} {b₂} prest c₁ c₂ a∈ =
  →equalInTypeNOWRITEMOD (Mod.∀𝕎-□Func M aw (equalInTypeNOWRITEMOD→ a∈))
  where
    aw : ∀𝕎 w (λ w' e' → NOWRITEMODeq (equalInType i w' T) w' a₂ b₂
                        → NOWRITEMODeq (equalInType i w' T) w' a₁ b₁)
    aw w1 e1 (x , d₁ , d₂) =
      prest i w1 a₁ a₂ b₁ b₂ (#⇛!→#⇛ {w1} {a₁} {a₂} (∀𝕎-mon e1 c₁)) (#⇛!→#⇛ {w1} {b₁} {b₂} (∀𝕎-mon e1 c₂)) x ,
      #⇛!-pres-#⇓→#⇓!-rev {w1} {a₂} {a₁} (∀𝕎-mon e1 c₁) d₁ ,
      #⇛!-pres-#⇓→#⇓!-rev {w1} {b₂} {b₁} (∀𝕎-mon e1 c₂) d₂


{--
#⇛!-NUM→type : (P : ℕ → Set) (T : CTerm) → Set(lsuc(L))
#⇛!-NUM→type P T =
  {i : ℕ} {w : 𝕎·} {a b : CTerm}
  → □· w (λ w' _ → Σ ℕ (λ n → a #⇛! #NUM n at w' × b #⇛! #NUM n at w' × P n))
  → equalInType i w (#NOWRITE T) a b
--}


NAT→T!2𝕊-equalInNAT! : (kb : K□) {i : ℕ} {w : 𝕎·} (P : ℕ → Set) {T f : CTerm}
                         (prest : type-preserves-#⇛ T) (nty : #⇛!-NUM-type P T)
                         (tyn : type-#⇛!-NUM P T) (f∈ : ∈Type i w (#FUN #NAT (#NOWRITEMOD T)) f) (k : ℕ)
                         → equalInType i w (#NOWRITEMOD T) (#APPLY f (#NUM k)) (#APPLY (#MSEQ (NAT→T!2𝕊 kb P tyn f∈)) (#NUM k))
NAT→T!2𝕊-equalInNAT! kb {i} {w} P {T} {f} prest nty tyn f∈ k =
  type-preserves-#⇛-NOWRITEMOD
    {T} {i} {w} {#APPLY f (#NUM k)} {#NUM (NAT→T!2𝕊 kb P tyn f∈ k)}
    {#APPLY (#MSEQ (NAT→T!2𝕊 kb P tyn f∈)) (#NUM k)}
    {#NUM (NAT→T!2𝕊 kb P tyn f∈ k)}
    prest
    h2
    (#APPLY-MSEQ-NUM#⇛! (NAT→T!2𝕊 kb P tyn f∈) k w)
    h1
  where
    h1 : equalInType i w (#NOWRITEMOD T) (#NUM (NAT→T!2𝕊 kb P tyn f∈ k)) (#NUM (NAT→T!2𝕊 kb P tyn f∈ k))
    h1 with kb (tyn {i} {w} {#APPLY f (#NUM  k)} {#APPLY f (#NUM k)} (equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM k) (#NUM k) (NUM-equalInType-NAT i w k)) ) w (⊑-refl· w)
    ... | j , c₁ , c₂ , cj = #⇛!-NUM-type-NOWRITEMOD P T i w j nty cj

    h2 : #APPLY f (#NUM k) #⇛! #NUM (NAT→T!2𝕊 kb P tyn f∈ k) at w
    h2 with kb (tyn {i} {w} {#APPLY f (#NUM  k)} {#APPLY f (#NUM k)} (equalInType-FUN→ f∈ w (⊑-refl· w) (#NUM k) (#NUM k) (NUM-equalInType-NAT i w k)) ) w (⊑-refl· w)
    ... | j , c₁ , c₂ , cj = c₁


semCond : (kb : K□) (cn : cℕ) (can : comp→∀ℕ) (exb : ∃□) (gc : get-choose-ℕ)
          (i : ℕ) (w : 𝕎·) (P : ℕ → Set) (T F f : CTerm)
          → P 0
          → #⇛!-NUM-type P T
          → type-#⇛-NUM P T
          → type-preserves-#⇛ T
          → isType i w T
          → ∈Type i w (#FunBarP T) F
          → ∈Type i w (#FUN #NAT (#NOWRITEMOD T)) f
          → equalInType i w #NAT (#APPLY F f) (#follow f (#tab F 0 #INIT) 0)
-- It's a #QNAT and not a #NAT because of the computation on #tab, which is a "time-dependent" computation
semCond kb cn can exb gc i w P T F f p0 nty tyn prest tyt F∈P f∈ =
  →equalInType-NAT
    i w (#APPLY F f) (#follow f I 0)
    (Mod.∀𝕎-□Func M aw (equalInType-W₀→ kb i w #IndBarB (#IndBarC T) I I I∈))
  where
    nnF  : #¬Names F
    nnF = equalInType-TPURE→ₗ F∈P

    F∈ : ∈Type i w (#FunBar T) F
    F∈ = equalInType-TPURE→ F∈P

    s : 𝕊
    s = NAT→T!2𝕊 kb P (type-#⇛-NUM→! P T tyn) f∈

    ps : (n : ℕ) → P (s n)
    ps = NAT→T!2𝕊-P kb P (type-#⇛-NUM→! P T tyn) f∈

    I : CTerm
    I = #tab F 0 #INIT

    I∈ : ∈Type i w (#IndBar T) I
    I∈ = sem kb cn can exb gc i w P T F p0 prest (type-#⇛-NUM→! P T tyn) nty tyt F∈P

    f≡1 : (k : ℕ) → equalInType i w (#NOWRITEMOD T) (#APPLY f (#NUM k)) (#APPLY (#MSEQ s) (#NUM k))
    f≡1 k = NAT→T!2𝕊-equalInNAT! kb P prest nty (type-#⇛-NUM→! P T tyn) f∈ k

    f≡2 : equalInType i w (#FUN #NAT T) f (#MSEQ s)
    f≡2 = NAT→T2𝕊-equalIn-NAT→T kb {i} {w} P {T} {f} (type-#⇛-NUM→! P T tyn) f∈ tyt nty prest

    aw : ∀𝕎 w (λ w' e' → wmem (equalInType i w' #IndBarB) (λ a b eqa → equalInType i w' (sub0 a (#IndBarC T))) w' I
                        → NATeq {--#weakMonEq--} w' (#APPLY F f) (#follow f I 0))
    aw w1 e1 h =
      NATeq-trans {w1} {#APPLY F f} {#follow (#MSEQ s) I 0} {#follow f I 0}
        (NATeq-trans {w1} {#APPLY F f} {#APPLY F (#MSEQ s)} {#follow (#MSEQ s) I 0} neq1 neq2)
        (weq→follow-NATeq kb i w1 P T I I (#MSEQ s) f 0 (type-#⇛-NUM→! P T tyn) nty h (λ k → equalInType-mon (equalInType-sym (f≡1 k)) w1 e1))
      where
        neq1 : NATeq w1 (#APPLY F f) (#APPLY F (#MSEQ s))
        neq1 = kb (equalInType-NAT→ i w1 _ _ (equalInType-FUN→ F∈ w1 e1 f (#MSEQ s) (equalInType-mon f≡2 w1 e1))) w1 (⊑-refl· w1)

        neq2 : NATeq w1 (#APPLY F (#MSEQ s)) (#follow (#MSEQ s) I 0)
        neq2 = fst neq1 ,
               snd (snd neq1) ,
               follow-NUM
                 kb can gc cn i w1 P T I I F s 0 (fst neq1) nnF
                 p0 ps nty tyn prest (eqTypes-mon (uni i) tyt w1 e1)
                 (#⇛!-refl {w1} {I}) h (equalInType-mon F∈ w1 e1) (snd (snd neq1))

\end{code}
