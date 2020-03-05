{-# OPTIONS --without-K --exact-split --safe #-}
module Isekai where

open import Universes public

{- To see special unicodes input method in agda-mode,
   Use command 'C-u C-x =' in emacs-agda-mode.
   Here list some unicode input methods we will use later: 
   𝓤 : MCU
   𝓥 : MCV
   𝓦 : MCW
   𝓣 : MCT
   ₀ : _0
   ̇ : ^.
   𝟙 : b1
   𝟘 : b0
   ¬ : neg
-}

variable
 𝓤 𝓥 𝓦 𝓣 : Universe

data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇)
            → A ⋆
            ----------------
            → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇) → B → 𝟙 → B
𝟙-recursion B = 𝟙-induction (λ _ → B)


!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆


data 𝟘 : 𝓤₀ ̇ where

𝟘-induction : (A : 𝟘 → 𝓤 ̇)
            -----------------
            → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (B : 𝓤 ̇) → 𝟘 → B
𝟘-recursion B = 𝟘-induction (λ _ → B)

!𝟘 : (B : 𝓤 ̇) → 𝟘 → B
!𝟘 = 𝟘-recursion

is-empty : 𝓤 ̇ → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇ → 𝓤 ̇
¬ = is-empty



data ℕ : 𝓤₀ ̇ where
  zero : ℕ
  succ : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

ℕ-induction : (A : ℕ → 𝓤 ̇)
            → A 0
            → ((n : ℕ) → A n → A (succ n))
            -------------------------------
            → (n : ℕ) → A n
ℕ-induction A a₀ f = h where
  h : (n : ℕ) → A n
  h 0        = a₀
  h (succ n) = f n (h n)

ℕ-recursion : (X : 𝓤 ̇)
            → X
            → (ℕ → X → X)
            → ℕ → X
ℕ-recursion X = ℕ-induction (λ _ → X)

ℕ-iteration : (X : 𝓤 ̇)
            → X
            → (X → X)
            → ℕ → X
ℕ-iteration X x f = ℕ-recursion X x (λ _ x → f x)


module Arithmetic where

  _+_ _×_ : ℕ → ℕ → ℕ

  x + 0 = x
  x + succ y = succ (x + y)

  x × 0 = 0
  x × succ y = x + x × y

  infixl 20 _+_
  infixl 21 _×_

module Arithmetic' where

  _+_ _×_ : ℕ → ℕ → ℕ

  x + y = h y where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ x succ

  x × y = h y where
    h : ℕ → ℕ
    h = ℕ-iteration ℕ 0 (x +_)

  infixl 20 _+_
  infixl 21 _×_


module ℕ-order where

  _≤_ _≥_ : ℕ → ℕ → 𝓤₀ ̇

  0      ≤ y      = 𝟙
  succ x ≤ 0      = 𝟘
  succ x ≤ succ y = x ≤ y

  x ≥ y = y ≤ x

  infix 10 _≤_
  infix 10 _≥_










