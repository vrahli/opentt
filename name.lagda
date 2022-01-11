\begin{code}
{-# OPTIONS --rewriting #-}


module name where


open import Level using (Level ; 0ℓ) renaming (suc to lsuc)
open import Agda.Builtin.Bool
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Relation.Nullary
open import Relation.Unary using (Pred; Decidable)
open import Relation.Binary.PropositionalEquality using (sym ; subst)
open import Data.Product
open import Data.Sum
open import Data.Empty
open import Data.Unit using (⊤ ; tt)
open import Data.Nat using (ℕ ; _≟_ ;  _<_ ; _≤_ ; _≥_ ; _≤?_ ; suc ; _⊔_)
open import Data.Nat.Properties
open import Data.Bool.Properties using ()
open import Agda.Builtin.String
open import Agda.Builtin.String.Properties
open import Data.List using (List ; [] ; _∷_ ; [_] ; _++_)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.DecSetoid(≡-decSetoid) using (_∈?_)
open import Data.List.Membership.Propositional.Properties
open import Axiom.UniquenessOfIdentityProofs


open import util
\end{code}


\begin{code}
-- the Name of a choice operator is taken as being a ℕ here
Name : Set
Name = ℕ


freshNameAux : (l : List Name) → Σ Name (λ n → (x : Name) → x ∈ l → x < n)
freshNameAux [] = (0 , λ x i → ⊥-elim (¬∈[] i))
freshNameAux (n ∷ l) =
  let (m , c) = freshNameAux l in
  let z : suc (n ⊔ m) ≡ suc n ⊔ suc m
      z = refl in
  (suc (n ⊔ m) , λ { x (here p) → <-transˡ (subst (λ x → x < suc n) (sym p) (n<1+n n)) (≤⊔l (suc n) (suc m)) ;
                     x (there p) → let c1 = c x p in <-trans c1 (<-transˡ (n<1+n _) (≤⊔r (suc n) (suc m)))} )


freshName : (l : List Name) → Σ Name (λ n → ¬ (n ∈ l))
freshName l = let (m , c) = freshNameAux l in (m , λ x → let z = c _ x in n≮n _ z)
\end{code}
