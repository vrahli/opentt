\begin{code}[hide]
{-# OPTIONS --rewriting #-}

module beth where

open import world
open import Data.List
open import Data.Nat
open import Data.Unit renaming (â¤ to ð; tt to â)
open import Data.Product
open import Relation.Binary.PropositionalEquality
\end{code}

\begin{code}
record PossibleWorlds : Setâ where
  field
    ð      : Setâ
    _â_    : ð â ð â Setâ
    action : ð â Setâ
    Î´      : (w : ð) â action w â ð

open PossibleWorlds

rel-of : (P : PossibleWorlds) â P .ð â P .ð â Setâ
rel-of P = P ._â_

syntax rel-of P x y = x â[ P ] y
\end{code}

\begin{code}
data Tree (P : PossibleWorlds) : P .ð â Setâ where
  leaf   : (w : P .ð) â Tree P w
  branch : {w : P .ð} â ((a : action P w) â Tree P (P .Î´ w a)) â Tree P w

actions : (P : PossibleWorlds) â {w : P .ð} â Tree P w â Setâ
actions P {_} (leaf _)   = ð
actions P {w} (branch f) = Î£[ a â action P w ] actions P (f a)

Î´â : (P : PossibleWorlds) {w : P. ð} (t : Tree P w) â (as : actions P t) â P .ð
Î´â P {w} (leaf w)   â        = w
Î´â P {w} (branch f) (a , as) = Î´â P (f a) as
\end{code}

\begin{code}
isALeafOf : (P : PossibleWorlds) {w : P .ð}
          â (wâ² : P .ð) â (t : Tree P w) â Setâ
isALeafOf P {w} wâ² t = Î£[ as â actions P t ] Î´â P t as â¡  wâ²

leaves : (P : PossibleWorlds) {w : P .ð} â Tree P w â Setâ
leaves P t = Î£[ w â P .ð ] isALeafOf P w t
\end{code}

\begin{code}
bars : (P : PossibleWorlds) â P .ð â (P .ð â Setâ) â Set
bars P w Ï =
  Î£[ t â Tree P w ]
    ((wâ : P .ð) â (Î£[ (wâ , _) â leaves P t ] wâ â[ P ] wâ) â Ï wâ)

syntax bars P w S = w â[ P ] S
\end{code}
