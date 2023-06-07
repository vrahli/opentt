\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --guardedness #-}


--open import bar
--module type_sys_props_nat (bar : Bar) where

open import Level using (Level ; 0ℓ ; Lift ; lift ; lower) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Product.Properties
open import Data.Sum
open import Data.Empty
open import Data.Maybe
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _+_ ; pred)
open import Data.Nat.Properties
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Function.Bundles
open import Axiom.Extensionality.Propositional


open import util
open import calculus
open import terms
open import world
open import choice
open import compatible
open import getChoice
open import progress
open import choiceExt
open import newChoice
open import mod
open import encode


module type_sys_props_nat {L : Level} (W : PossibleWorlds {L}) (M : Mod W)
                          (C : Choice) (K : Compatible {L} W C) (P : Progress {L} W C K) (G : GetChoice {L} W C K)
                          (X : ChoiceExt W C)
                          (N : NewChoice W C K G)
                          (E : Extensionality 0ℓ (lsuc(lsuc(L))))
                          (EC : Encode)
       where


open import worldDef(W)
open import computation(W)(C)(K)(G)(X)(N)(EC)
open import bar(W)
open import barI(W)(M)--(C)(K)(P)
open import forcing(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import props0(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
open import ind(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind2(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
--open import ind3(W)(M)(C)(K)(P)(G)(X)(N)(E)(EC)
\end{code}



\begin{code}[hide]

typeSysConds-NAT-extl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                          (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                          → eqInTypeExtL1 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extl1 u w A B x x₁ C eqt' =
  concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NAT at w') (a b : CTerm) → □· w' (λ w'' _ → NATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'



typeSysConds-NAT-extl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeExtL2 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NAT at w') (a b : CTerm) → □· w' (λ w'' _ → NATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : A #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-NAT-extr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeExtR1 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NAT at w') (a b : CTerm) → □· w' (λ w'' _ → NATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p c₁ c₂) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp c₂))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih comp a b eqi = Mod.∀𝕎-□-□' M y aw
      where
        aw : ∀𝕎 w (λ w' e' → (x : eqTypes u w' T1 T2) (at : at□· y w' e' x) → eqInType u w' x a b)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-NAT-extr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeExtR2 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NAT at w') (a b : CTerm) → □· w' (λ w'' _ → NATeq w'' a b) → eqInType u' w' eqt'' a b)
          → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt a b
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.∀𝕎-□-□' M x aw
      where
        aw : ∀𝕎 w (λ w' e' → (x₃ : eqTypes u w' T1 T2) (at : at□· x w' e' x₃) → eqInType u w' x₃ a b)
        aw w1 e1 y at = ih {u} {w1} {T1} {T2} y (<Type1 y (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 y at)) (∀𝕎-mon e1 comp) a b (Mod.↑□ M eqi e1)

    concl : (comp : B #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → □· w (λ w' _ → NATeq w' a b) → eqInType u w eqt' a b)
        ind
        eqt'


typeSysConds-NAT-extrevl1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevL1 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extrevl1 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NATeq w'' a b))
          → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b))
        ind
        eqt'


typeSysConds-NAT-extrevl2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevL2 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extrevl2 u w A B x x₁ C eqt' = concl x
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NATeq w'' a b))
          → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : A #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b))
        ind
        eqt'


typeSysConds-NAT-extrevr1 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevR1 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extrevr1 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T2' #⇛ #NAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NATeq w'' a b))
          → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y₁))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y₁))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T2 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b))
        ind
        eqt'


typeSysConds-NAT-extrevr2 : (u : univs) (w : 𝕎·) (A B : CTerm)
                            (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                            → eqInTypeExtRevR2 {u} {_} {A} {B} (EQTNAT x x₁)
typeSysConds-NAT-extrevr2 u w A B x x₁ C eqt' = concl x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (comp : T1' #⇛ #NAT at w') (a b : CTerm) → eqInType u' w' eqt'' a b → □· w' (λ w'' _ → NATeq w'' a b))
          → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt a b → □· w (λ w' _ → NATeq w' a b)
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih comp a b eqi = eqi
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqQNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih comp a b eqi = ⊥-elim (NATneqTNAT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₂ x₃) ih comp a b eqi = ⊥-elim (NATneqQLT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih comp a b eqi = ⊥-elim (NATneqFREE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqPI (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqW (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqSET (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqISECT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih comp a b eqi = ⊥-elim (NATneqTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A B y y₁ eqtA exta eqt1 eqt2) ih comp a b eqi = ⊥-elim (NATneqEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB exta extb) ih comp a b eqi = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqTCONST (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt comp y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih comp a b eqi = ⊥-elim (NATneqDUM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA exta eqx) ih comp a b eqi = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih comp a b eqi = ⊥-elim (NATneqPURE (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih comp a b eqi = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTTERM t1 t2 y y₁ x₂) ih comp a b eqi = ⊥-elim (NATneqTERM (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih comp a b eqi = ⊥-elim (NATneqUNIV (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA exta) ih comp a b eqi = ⊥-elim (NATneqLIFT (⇛-val-det tt tt comp y))
    ind {u} {w} {T1} {T2} (EQTBAR x) ih comp a b eqi = Mod.□-idem M (Mod.∀𝕎-□'-□ M x aw eqi)
      where
        aw0 : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                             → Mod.□ M w' (↑wPred (λ w'' e → NATeq w'' a b) e'))
        aw0 w1 e1 z at eqz = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR x) (<TypeBAR u w T1 T2 x w1 e1 z at)) (⇛-mon e1 comp) a b eqz

        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· x w' e' z) → eqInType u w' z a b
                            → Mod.□ M w' (↑wPred' (λ w'' e → NATeq w'' a b) e'))
        aw w1 e1 z at eqz = Mod.∀𝕎-□Func M (λ w1 e1 z x → z) (aw0 w1 e1 z at eqz)

    concl : (comp : B #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b)
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (comp : T1 #⇛ #NAT at w) (a b : CTerm) → eqInType u w eqt' a b → □· w (λ w' _ → NATeq w' a b))
        ind
        eqt'


eqInType-⇛-NAT : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                  → A #⇛ #NAT at w
                  → B #⇛ #NAT at w
                  → (eqt : eqTypes u w A B)
                  → eqInType u w eqt a b
                  → □· w (λ w' e → NATeq w' a b)
eqInType-⇛-NAT u w A B a b c₁ c₂ eqt ei = typeSysConds-NAT-extrevl1 u w A B c₁ c₂ B eqt a b ei


eqInType-⇛-NAT-rev : (u : univs) (w : 𝕎·) (A B a b : CTerm)
                      → A #⇛ #NAT at w
                      → B #⇛ #NAT at w
                      → (eqt : eqTypes u w A B)
                      → □· w (λ w' e → NATeq w' a b)
                      → eqInType u w eqt a b
eqInType-⇛-NAT-rev u w A B a b c₁ c₂ eqt ei = typeSysConds-NAT-extl1 u w A B c₁ c₂ B eqt a b ei


typeSysConds-NAT-local : (u : univs) (w : 𝕎·) (A B : CTerm)
                         (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                         → eqInTypeLocal {u} (EQTNAT x x₁)
typeSysConds-NAT-local u w A B x x₁ a b i j =
  Mod.□-idem M (Mod.∀𝕎-□'-□ M i aw j)
  where
    aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' A B) (at : at□· i w' e' z) → eqInType u w' z a b → □· w' (λ w'' e → w ⊑· w'' → NATeq w'' a b))
    aw w1 e1 z at ei = Mod.∀𝕎-□Func M (λ w' e' s x → s) aw'
      where
        aw' : □· w1 (λ w' e → NATeq w' a b)
        aw' = eqInType-⇛-NAT u w1 A B a b (⇛-mon e1 x) (⇛-mon e1 x₁) z ei



typeSysConds-NAT-ttrans : (u : univs) (w : 𝕎·) (A B : CTerm)
                           (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                           → eqTypesTrans u w A B
typeSysConds-NAT-ttrans u w A B x x₁ C eqt = concl x x₁
  where
    ind : {u : univs} {w : 𝕎·} {T1 T2 : CTerm} (eqt : eqTypes u w T1 T2)
          → ({u' : univs} {w' : 𝕎·} {T1' T2' : CTerm} (eqt'' : eqTypes u' w' T1' T2')
                 → <Type eqt'' eqt → (c₁ : A #⇛ #NAT at w') (c₂ : T1' #⇛ #NAT at w') → eqTypes u' w' A T2')
          → (c₁ : A #⇛ #NAT at w) (c₂ : T1 #⇛ #NAT at w) → eqTypes u w A T2
    ind {u} {w} {T1} {T2} (EQTNAT y y₁) ih c₁ c₂ = EQTNAT c₁ y₁
    ind {u} {w} {T1} {T2} (EQTQNAT y y₁) ih c₁ c₂ = ⊥-elim (NATneqQNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTNAT y y₁) ih c₁ c₂ = ⊥-elim (NATneqTNAT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (NATneqLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQLT a1 a2 b1 b2 y y₁ x₄ x₅) ih c₁ c₂ = ⊥-elim (NATneqQLT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTFREE y y₁) ih c₁ c₂ = ⊥-elim (NATneqFREE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPI A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NATneqPI (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTW A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NATneqW (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NATneqM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUM A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NATneqSUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSET A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NATneqSET (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTISECT A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (NATneqISECT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTUNION A1 B1 A2 B2 y y₁ eqta eqtb exta extb) ih c₁ c₂ = ⊥-elim (NATneqTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTEQ a1 b1 a2 b2 A₁ B₁ y y₁ eqtA exta eqt1 eqt2) ih c₁ c₂ = ⊥-elim (NATneqEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (NATneqUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTQTUNION A1 B1 A2 B2 y y₁ eqtA eqtB extA extB) ih c₁ c₂ = ⊥-elim (NATneqQTUNION (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSQUASH A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NATneqTSQUASH (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTRUNC A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NATneqTTRUNC (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTCONST A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NATneqTCONST (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTSUBSING A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NATneqSUBSING (⇛-val-det tt tt c₂ y))
--    ind {u} {w} {T1} {T2} (EQTDUM A1 A2 y y₁ eqtA) ih c₁ c₂ = ⊥-elim (NATneqDUM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTPURE y y₁) ih c₁ c₂ = ⊥-elim (NATneqPURE (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTNOSEQ y y₁) ih c₁ c₂ = ⊥-elim (NATneqNOSEQ (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTTERM z₁ z₂ y y₁ y₂) ih c₁ c₂ = ⊥-elim (NATneqTERM (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQFFDEFS A1 A2 x1 x2 y y₁ eqtA extA eqx) ih c₁ c₂ = ⊥-elim (NATneqFFDEFS (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTUNIV i p y y₁) ih c₁ c₂ = ⊥-elim (NATneqUNIV (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTLIFT A1 A2 y y₁ eqtA extA) ih c₁ c₂ = ⊥-elim (NATneqLIFT (⇛-val-det tt tt c₂ y))
    ind {u} {w} {T1} {T2} (EQTBAR y) ih c₁ c₂ = EQTBAR (∀𝕎-□at W M y aw)
      where
        aw : ∀𝕎 w (λ w' e' → (z : eqTypes u w' T1 T2) (at : at□· y w' e' z) → eqTypes u w' A T2)
        aw w1 e1 z at = ih {u} {w1} {T1} {T2} z (<Type1 z (EQTBAR y) (<TypeBAR u w T1 T2 y w1 e1 z at)) (⇛-mon e1 c₁) (⇛-mon e1 c₂)

    concl : (c₁ : A #⇛ #NAT at w) (c₁ : B #⇛ #NAT at w) → eqTypes u w A C
    concl =
      ind<Type
        (λ {u} {w} {T1} {T2} eqt' → (c₁ : A #⇛ #NAT at w) (c₂ : T1 #⇛ #NAT at w) → eqTypes u w A T2)
        ind
        eqt


typeSysConds-NAT : (u : univs) (w : 𝕎·) (A B : CTerm)
                   (x : A #⇛ #NAT at w) (x₁ : B #⇛ #NAT at w)
                   → TSP {u} (EQTNAT x x₁)
typeSysConds-NAT u w A B x x₁ =
  mktsp tsym ttrans isym itrans iextl1 iextl2 iextr1 iextr2 iextrl1 iextrl2 iextrr1 iextrr2 local
  where
    tsym : eqTypes u w B A
    tsym = EQTNAT x₁ x

    ttrans : eqTypesTrans u w A B
    ttrans = typeSysConds-NAT-ttrans u w A B x x₁

 {-ttrans C eqt1 = EQTBAR (Mod.∀𝕎-□Func M d c)
      where
        c : □· w (λ w' _ → C #⇛ #NAT at w')
        c = eqTypes⇛NAT eqt1 x₁

        d : ∀𝕎 w (λ w' e' → C #⇛ #NAT at w' → eqTypes u w' A C)
        d w1 e1 comp = EQTNAT (⇛-mon e1 x) comp--}

    isym : eqInTypeSym u {_} {A} {B} (EQTNAT x x₁)
    isym a b eqi = □NATeq-sym {w} {a} {b} eqi

    itrans : eqInTypeTrans u {_} {A} {B} (EQTNAT x x₁)
    itrans a b c eqi₁ eqi₂ = □NATeq-trans {w} {a} {b} {c} eqi₁ eqi₂

    iextl1 : eqInTypeExtL1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextl1 = typeSysConds-NAT-extl1 u w A B x x₁

    iextl2 : eqInTypeExtL2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextl2 = typeSysConds-NAT-extl2 u w A B x x₁

    iextr1 : eqInTypeExtR1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextr1 = typeSysConds-NAT-extr1 u w A B x x₁

    iextr2 : eqInTypeExtR2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextr2 = typeSysConds-NAT-extr2 u w A B x x₁

    iextrl1 : eqInTypeExtRevL1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrl1 = typeSysConds-NAT-extrevl1 u w A B x x₁

    iextrl2 : eqInTypeExtRevL2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrl2 = typeSysConds-NAT-extrevl2 u w A B x x₁

    iextrr1 : eqInTypeExtRevR1 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrr1 = typeSysConds-NAT-extrevr1 u w A B x x₁

    iextrr2 : eqInTypeExtRevR2 {_} {_} {A} {B} (EQTNAT x x₁)
    iextrr2 = typeSysConds-NAT-extrevr2 u w A B x x₁

    local : eqInTypeLocal (EQTNAT x x₁)
    local = typeSysConds-NAT-local u w A B x x₁
\end{code}
