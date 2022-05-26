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


module terms5c {L : Level} (W : PossibleWorlds {L})
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
open import terms5(W)(C)(M)(G)(E)(N)
open import terms3b(W)(C)(M)(G)(E)(N)
open import terms5b(W)(C)(M)(G)(E)(N)

open import continuity-conds(W)(C)(M)(G)(E)(N)


{--
¬∈→upd⇓names-concl-val : {w1' w2 : 𝕎·} {name1 name2 : Name} {f b v : Term}
                          → Σ 𝕎· (λ w2' → Σ Term (λ v' →
                               APPLY (upd name2 f) b ⇓ v' from w1' to w2'
                               × differ2 name1 name2 f v v'
                               × getT 0 name1 w2 ≡ getT 0 name2 w2'))
                          → Σ 𝕎· (λ w2' → Σ Term (λ v' →
                               APPLY (upd name2 f) b ⇓ v' from w1' to w2'
                               × differ2 name1 name2 f v v'
                               × getT 0 name1 w2 ≡ getT 0 name2 w2'))
¬∈→upd⇓names-concl-val {w1'} {w2} {name1} {name2} {f} {b} {v} (w2' , v' , comp , diff , g0) = {!!}
--}


differ2-CS→ : {name1 name2 name : Name} {f t : Term}
               → differ2 name1 name2 f (CS name) t
               → t ≡ CS name
differ2-CS→ {name1} {name2} {name} {f} {.(CS name)} (differ2-CS .name) = refl


differ2-NAME→ : {name1 name2 name : Name} {f t : Term}
                 → differ2 name1 name2 f (NAME name) t
                 → t ≡ NAME name
differ2-NAME→ {name1} {name2} {name} {f} {.(NAME name)} (differ2-NAME .name) = refl


¬∈→differ⇓-aux2 : (gc0 : get-choose-ℕ)
               (f : Term) (cf : # f) (name1 name2 : Name) (w1 w2 w1' w0 : 𝕎·) (a b a' v : Term) (k : ℕ)
               → compatible· name1 w1 Res⊤
               → compatible· name2 w1' Res⊤
               → ∀𝕎-get0-NUM w1 name1
               → differ2 name1 name2 f a b
               → getT 0 name1 w1 ≡ getT 0 name2 w1'
               → step a w1 ≡ just (a' , w2)
               → steps k (a' , w2) ≡ (v , w0)
               → isValue v
               → ((k' : ℕ) → k' < k → ⇓PresDiff2 f name1 name2 k')
               → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   a' ⇓ a'' from w2 to w3
                   × b ⇓ b'' from w1' to w3'
                   × differ2 name1 name2 f a'' b''
                   × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .NAT .NAT a' v k compat1 compat2 agtn differ2-NAT g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NAT , NAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-NAT , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .QNAT .QNAT a' v k compat1 compat2 agtn differ2-QNAT g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QNAT , QNAT , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-QNAT , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(LT a₁ b₁) .(LT a₂ b₂) a' v k compat1 compat2 agtn (differ2-LT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LT a₁ b₁ , LT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-LT _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(QLT a₁ b₁) .(QLT a₂ b₂) a' v k compat1 compat2 agtn (differ2-QLT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QLT a₁ b₁ , QLT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-QLT _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(NUM x) .(NUM x) a' v k compat1 compat2 agtn (differ2-NUM x) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NUM _ , NUM _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-NUM _ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(IFLT a₁ b₁ c₁ d₁) .(IFLT a₂ b₂ c₂ d₂) a' v k compat1 compat2 agtn (differ2-IFLT a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ diff diff₁ diff₂ diff₃) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(SUC a) .(SUC b) a' v k compat1 compat2 agtn (differ2-SUC a b diff) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(PI a₁ b₁) .(PI a₂ b₂) a' v k compat1 compat2 agtn (differ2-PI a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PI a₁ b₁ , PI a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-PI _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(LAMBDA a) .(LAMBDA b) a' v k compat1 compat2 agtn (differ2-LAMBDA a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LAMBDA a , LAMBDA b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-LAMBDA _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(APPLY f₁ a₁) .(APPLY f₂ a₂) a' v k compat1 compat2 agtn (differ2-APPLY f₁ f₂ a₁ a₂ diff diff₁) g0 s hv isvv pd with is-LAM f₁
... | inj₁ (t , p) rewrite p | sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = concl d
  where
    d : Σ Term (λ t' → f₂ ≡ LAMBDA t' × differ2 name1 name2 f t t') ⊎ (t ≡ updBody name1 f × f₂ ≡ upd name2 f)
    d = differ2-LAMBDAₗ→ diff

    concl : Σ Term (λ t' → f₂ ≡ LAMBDA t' × differ2 name1 name2 f t t') ⊎ (t ≡ updBody name1 f × f₂ ≡ upd name2 f)
            → Σ Term (λ a'' → Σ Term (λ b'' → Σ 𝕎· (λ w3 → Σ 𝕎· (λ w3' →
                   sub a₁ t ⇓ a'' from w1 to w3
                   × APPLY f₂ a₂ ⇓ b'' from w1' to w3'
                   × differ2 name1 name2 f a'' b''
                   × getT 0 name1 w3 ≡ getT 0 name2 w3'))))
    concl (inj₁ (t' , e₁ , e₂)) rewrite e₁ =
      sub a₁ t , sub a₂ t' , w1 , w1' ,
      ⇓from-to-refl _ _ , APPLY-LAMBDA⇓ w1' t' a₂ ,
      differ2-sub cf e₂ diff₁ , g0
    concl (inj₂ (e₁ , e₂)) rewrite e₁ | e₂ | sub-upd name1 f a₁ cf =
      v , fst (snd hv2) , w0 , fst hv2 , (k , hv1) , fst (snd (snd hv2)) ,
      fst (snd (snd (snd hv2))) , snd (snd (snd (snd hv2)))
      where
        hv0 : steps k (sub a₁ (updBody name1 f) , w1) ≡ (v , w0)
        hv0 rewrite e₁ = hv

        hv1 : steps k (LET a₁ (SEQ (updGt name1 (VAR 0)) (APPLY f (VAR 0))) , w1) ≡ (v , w0)
        hv1 rewrite sym (sub-upd name1 f a₁ cf) = hv0

        hv2 : Σ 𝕎· (λ w2' → Σ Term (λ v' →
                 APPLY (upd name2 f) a₂ ⇓ v' from w1' to w2'
                 × differ2 name1 name2 f v v'
                 × getT 0 name1 w0 ≡ getT 0 name2 w2'))
        hv2 = ¬∈→upd⇓names gc0 k f name1 name2 w1 w1' w0 a₁ a₂ v cf agtn compat1 compat2 isvv pd g0 diff₁ hv1
... | inj₂ x with is-CS f₁
... |    inj₁ (name , p) rewrite p with is-NUM a₁
... |       inj₁ (n , q) rewrite q | differ2-NUM→ diff₁ | differ2-CS→ diff = {!!} --Data.Maybe.map (λ t → t , w) (getT n name w)
... |       inj₂ y with step⊎ a₁ w1
... |          inj₁ (a₁' , w3 , z) rewrite z = {!!} --ret (APPLY (CS name) u) w'
... |          inj₂ z rewrite z = {!!} --nothing
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(APPLY f₁ a₁) .(APPLY f₂ a₂) a' v k compat1 compat2 agtn (differ2-APPLY f₁ f₂ a₁ a₂ diff diff₁) g0 s hv isvv pd | inj₂ x | inj₂ name with step⊎ f₁ w1
... | inj₁ (f₁' , w3 , z) rewrite z = {!!} --ret (APPLY g a) w'
... | inj₂ z rewrite z = {!!} --nothing
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(FIX a) .(FIX b) a' v k compat1 compat2 agtn (differ2-FIX a b diff) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(LET a₁ b₁) .(LET a₂ b₂) a' v k compat1 compat2 agtn (differ2-LET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(SUM a₁ b₁) .(SUM a₂ b₂) a' v k compat1 compat2 agtn (differ2-SUM a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUM a₁ b₁ , SUM a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-SUM _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(PAIR a₁ b₁) .(PAIR a₂ b₂) a' v k compat1 compat2 agtn (differ2-PAIR a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PAIR a₁ b₁ , PAIR a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-PAIR _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(SPREAD a₁ b₁) .(SPREAD a₂ b₂) a' v k compat1 compat2 agtn (differ2-SPREAD a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(SET a₁ b₁) .(SET a₂ b₂) a' v k compat1 compat2 agtn (differ2-SET a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SET a₁ b₁ , SET a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-SET _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(ISECT a₁ b₁) .(ISECT a₂ b₂) a' v k compat1 compat2 agtn (differ2-ISECT a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = ISECT a₁ b₁ , ISECT a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-ISECT _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(TUNION a₁ b₁) .(TUNION a₂ b₂) a' v k compat1 compat2 agtn (differ2-TUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TUNION a₁ b₁ , TUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-TUNION _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(UNION a₁ b₁) .(UNION a₂ b₂) a' v k compat1 compat2 agtn (differ2-UNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNION a₁ b₁ , UNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-UNION _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(QTUNION a₁ b₁) .(QTUNION a₂ b₂) a' v k compat1 compat2 agtn (differ2-QTUNION a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = QTUNION a₁ b₁ , QTUNION a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-QTUNION _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(INL a) .(INL b) a' v k compat1 compat2 agtn (differ2-INL a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INL a , INL b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-INL _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(INR a) .(INR b) a' v k compat1 compat2 agtn (differ2-INR a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = INR a , INR b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-INR _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(DECIDE a₁ b₁ c₁) .(DECIDE a₂ b₂ c₂) a' v k compat1 compat2 agtn (differ2-DECIDE a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(EQ a₁ b₁ c₁) .(EQ a₂ b₂ c₂) a' v k compat1 compat2 agtn (differ2-EQ a₁ a₂ b₁ b₂ c₁ c₂ diff diff₁ diff₂) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = EQ a₁ b₁ c₁ , EQ a₂ b₂ c₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-EQ _ _ _ _ _ _ diff diff₁ diff₂ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .AX .AX a' v k compat1 compat2 agtn differ2-AX g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = AX , AX , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-AX , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .FREE .FREE a' v k compat1 compat2 agtn differ2-FREE g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FREE , FREE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-FREE , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(CS name) .(CS name) a' v k compat1 compat2 agtn (differ2-CS name) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = CS _ , CS _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-CS _ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(NAME name) .(NAME name) a' v k compat1 compat2 agtn (differ2-NAME name) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = NAME _ , NAME _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-NAME _ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(FRESH a) .(FRESH b) a' v k compat1 compat2 agtn (differ2-FRESH a b diff) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(CHOOSE a₁ b₁) .(CHOOSE a₂ b₂) a' v k compat1 compat2 agtn (differ2-CHOOSE a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd = {!!}
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(TSQUASH a) .(TSQUASH b) a' v k compat1 compat2 agtn (differ2-TSQUASH a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TSQUASH a , TSQUASH b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-TSQUASH _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(TTRUNC a) .(TTRUNC b) a' v k compat1 compat2 agtn (differ2-TTRUNC a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TTRUNC a , TTRUNC b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-TTRUNC _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(TCONST a) .(TCONST b) a' v k compat1 compat2 agtn (differ2-TCONST a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = TCONST a , TCONST b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-TCONST _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(SUBSING a) .(SUBSING b) a' v k compat1 compat2 agtn (differ2-SUBSING a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SUBSING a , SUBSING b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-SUBSING _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .PURE .PURE a' v k compat1 compat2 agtn differ2-PURE g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = PURE , PURE , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-PURE , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(DUM a) .(DUM b) a' v k compat1 compat2 agtn (differ2-DUM a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = DUM a , DUM b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-DUM _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(FFDEFS a₁ b₁) .(FFDEFS a₂ b₂) a' v k compat1 compat2 agtn (differ2-FFDEFS a₁ a₂ b₁ b₂ diff diff₁) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = FFDEFS a₁ b₁ , FFDEFS a₂ b₂ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-FFDEFS _ _ _ _ diff diff₁ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(UNIV x) .(UNIV x) a' v k compat1 compat2 agtn (differ2-UNIV x) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = UNIV _ , UNIV _ , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-UNIV _ , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(LIFT a) .(LIFT b) a' v k compat1 compat2 agtn (differ2-LIFT a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LIFT a , LIFT b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-LIFT _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(LOWER a) .(LOWER b) a' v k compat1 compat2 agtn (differ2-LOWER a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = LOWER a , LOWER b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-LOWER _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(SHRINK a) .(SHRINK b) a' v k compat1 compat2 agtn (differ2-SHRINK a b diff) g0 s hv isvv pd rewrite sym (pair-inj₁ (just-inj s)) | sym (pair-inj₂ (just-inj s)) = SHRINK a , SHRINK b , w1 , w1' , ⇓from-to-refl _ _ , ⇓from-to-refl _ _ , differ2-SHRINK _ _ diff , g0
¬∈→differ⇓-aux2 gc0 f cf name1 name2 w1 w2 w1' w0 .(upd name1 f) .(upd name2 f) a' v k compat1 compat2 agtn differ2-upd g0 s hv isvv pd = {!!}

\end{code}
