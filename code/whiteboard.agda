{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product
  using (_×_; proj₁; proj₂; ∃; ∃-syntax)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Data.Unit using (⊤; tt)
open import Data.Empty
open import Data.List



-- mutual inductive types
data Even : Set

data Odd : Set where
  even2odd : Even -> Odd

data Even where
  even : Even
  od2even : Odd -> Even


-- higher-order inductive types
data NAT : Set where
  Z : NAT
  S : (⊤ → NAT) -> NAT

ZERO : NAT -> NAT
ZERO Z = Z
ZERO (S f) = ZERO (f tt)


-- mutual inductive-coinductive types
-- as fixpoints:
--   nat' := μ x. 1 + (ν y. 1 → x)
--   fun⊤nat' := ν y. 1 → (μ x. 1 + x)
--   supernat' := μ x. nat' + (ν y. (1 → x) × (1 → y))
--   strsupernat' := ν y. (1 → (μ x. nat' + y)) × (1 → y))
-- and general (symmetric) codata
--   codata t
--     d₁(γ₁ᵖ,γ₁ᶜ)
--     ...
--     dₙ(γ₂ᵖ,γ₂ᶜ)
-- as fixpoint:
--   t := ν z. (γ₁ᵖ(1) × ... × γ₁ᵖ(p₁) → γ₁ᶜ(1) + ... + γ₁ᶜ(c₁)) × ... × (... → ...)
data Nat' : Set

record Fun⊤Nat' : Set where
  coinductive
  field
    apply : ⊤ -> Nat'
open Fun⊤Nat'

data Nat' where
  z' : Nat'
  succ' : Fun⊤Nat' -> Nat'

{-# TERMINATING #-}
scrwd : Nat' -> Nat'
scrwd z' = z'
scrwd (succ' f) = scrwd (apply f tt)

-- termination problem is
up : Nat'

badfun : Fun⊤Nat'
apply badfun x = up

up = succ' badfun

scrwdup : Nat'
scrwdup = scrwd up


data SuperNat' : Set

record StrSuperNat' : Set where
  coinductive
  field
    superhead : SuperNat'
    supertail : StrSuperNat'
open StrSuperNat'

data SuperNat' where
  nat' : Nat' -> SuperNat'
  strnat' : StrSuperNat' -> SuperNat'

{-# TERMINATING #-}
super : SuperNat' -> SuperNat'
super (nat' n) = nat' n
super (strnat' x) = super (superhead x)

-- termination problem is
bad : SuperNat'

bads : StrSuperNat'
superhead bads = bad
supertail bads = bads

bad = strnat' bads

superbad : SuperNat'
superbad = super bad



-- positivity violations
{-# NO_POSITIVITY_CHECK #-}
data X : Set where
  c : (X -> X) -> X


{-# NO_POSITIVITY_CHECK #-}
record Y : Set where
  coinductive
  field
    d : Y -> Y
open Y


data X' : Set

record FunX'X' : Set where
  coinductive
  field
    apply : X' -> X'
open FunX'X'

{-# NO_POSITIVITY_CHECK #-}
data X' where
  c' : FunX'X' -> X'



-- termination complaints
data Nat : Set where
  z : Nat
  succ : Nat -> Nat

record N : Set where
  coinductive
  field
    new : N
open N


idNat : Nat -> Nat
idNat n = n

idN : N -> N
idN n = n


new1 : Nat -> Nat
new1 z =  z
new1 (succ n) = succ (succ n)

z1 : N
new z1 = z1

{-# TERMINATING #-}
succ1 : N -> N
new (succ1 n) = succ1 (succ1 n)  -- even with = idN (scc1 n)


{-# TERMINATING #-}
new2 : Nat -> Nat
new2 z =  z
new2 (succ n) = new2 (new2 n) -- even with = new2 (idNat n)

z2 : N
new z2 = z2

succ2 : N -> N
new (succ2 n) = new (new n)


new3 : Nat -> Nat
new3 z = z
new3 (succ n) = succ (new3 n)

z3 : N
new z3 = z3

succ3 : N -> N
new (succ3 n) = succ3 (new n)


-- termination complaints which are syntactically forbidden in ouroboro
{-# TERMINATING #-}
f : Nat
f = succ f

data A : Set where
  prf : A
  iden : (⊤ -> A) -> A
{-# TERMINATING #-}
newprf : ⊤ -> A
newprf x = iden newprf



{- Mendler-style inductive types in Agda -}
-- Sugar
-- A + B := Π Z. (A → Z) → (B → Z) → Z
-- inl := λ x. Λ Z. λ fl. λ fr. fl x
-- inr := λ x. Λ Z. λ fl. λ fr. fr x
-- A × B := Π Z. (A → B → Z) → Z
-- pr1 := λ pair. pair A (λ a. λ b. a) 
-- pr2 := λ pair. pair A (λ a. λ b. b)

-- SPNatBool: stream processors turning Nats to Bools
--
-- Type Encoding
-- SPNatBool: ν X. μ Y. Bool × X + (Nat → Y)
--
-- Intro
-- IN : Bool × X + (Nat → μ) → μ
-- OUT : ν → μ Y. Bool × ν + (Nat → Y)
--
-- Elimination
-- R : Π A. ( Π X. (X → A) → (Bool × X + (Nat → Y))) → A ) → (μ Y. ...) → A
-- S : Π A. ( Π X. (A → X) → A → (μ Y. Bool × X + (Nat → Y)) ) → A → (ν X. ...)
--
-- Sugar
-- put := IN ∘ inl
-- get := IN ∘ inr
--
-- so wrappedMapp compiles to
-- wrappedMapp := (S (Nat -> Bool)) ( ΛX. λWRAPPEDMAPP : (Nat → Bool) → X. λf : Nat → Bool. get (λa : Nat. put (f a) (WRAPPEDMAPP f)) )
record StreamBool : Set

data SPNatBool : Set where
  get : (Nat -> SPNatBool) -> SPNatBool
  put : Bool -> StreamBool -> SPNatBool

record StreamBool where
  coinductive
  field
    proc : SPNatBool
open StreamBool

wrappedMapp : (Nat -> Bool) -> StreamBool

mapp : (Nat -> Bool) -> SPNatBool
mapp f = get (λ a → put (f a) (wrappedMapp f))

proc (wrappedMapp f) = mapp f


-- SPNatBool': codata instead of arrow type
--
-- Type Encoding
-- SPNatBool' := ν X. μ Y. Bool × X + (ν Z. Nat → Y)
--
-- Intro
-- OUT1 : ν → (Nat → Y)
-- IN : Bool × X + (ν Z. Nat → μ) → μ
-- OUT2 : ν → μ Y. Bool × ν + (ν Z. Nat → Y)
--
-- Elimination
-- S : Π A. ( Π X. (A → X) → A → (Nat → Y) ) → A → (ν Z. ...)
-- R : Π A. ( Π X. (X → A) → (Bool × X + (Nat → Y))) → A ) → (μ Y. ...) → A
-- S : Π A. ( Π X. (A → X) → A → (μ Y. Bool × X + (ν Z. Nat → Y)) ) → A → (ν X. ...)
--
-- Sugar
-- put' := IN ∘ inl
-- get' := IN ∘ inr
--
-- wrappedFun' compiles to
-- wrappedFun' := (S (Nat -> Bool)) ( ΛX. λWRAPPEDFUN' : (Nat → Bool) → X. λf : Nat → Bool. λa : Nat. put' (f a) (wrappedMapp' f) )
--
-- wrappedMapp' compiles to
-- wrappedMapp' := (S (Nat -> Bool)) ( ΛX. λWRAPPEDMAPP' : (Nat → Bool) → X. λf : Nat → Bool. get' (wrappedFun' f) )
record StreamBool' : Set

data SPNatBool' : Set

record Nat2SPNatBool' : Set where
  coinductive
  field
    apply : Nat -> SPNatBool'
open Nat2SPNatBool'

data SPNatBool' where
  get' : Nat2SPNatBool' -> SPNatBool'
  put' : Bool -> StreamBool' -> SPNatBool'

record StreamBool' where
  coinductive
  field
    proc' : SPNatBool'
open StreamBool'

wrappedMapp' : (Nat -> Bool) -> StreamBool'

wrappedFun' : (Nat -> Bool) -> Nat2SPNatBool'
apply (wrappedFun' f) a = put' (f a) (wrappedMapp' f)

mapp' : (Nat -> Bool) -> SPNatBool'
mapp' f = get' (wrappedFun' f)

proc' (wrappedMapp' f) = mapp' f


-- Nat with plus
--
-- Type Encoding
-- Nat := μ X. 1 + X
--
-- Intro
-- IN : 1 + μ → μ
--
-- Elimination
-- R : Π A. ( Π X. (X → A) → (1 + X) → A ) → (μ X. ...) → A
--
-- Sugar
-- z := IN ∘ inl
-- succ := IN ∘ inr
--
-- plus compiles to (Mendler)
-- plus := (R (Nat -> Nat)) ( ΛX. λPLUS : X → (Nat → Nat). λN : 1 + X. N (Nat → Nat) (λx : 1. λm : Nat. m) (λx : X. λm : Nat. PLUS x (succ m)) )
--
-- plus compiles to (Ordinary)
-- plus := (R (Nat -> Nat)) ( λc : 1 + (Nat → Nat). c (Nat → Nat) (λx: 1. λ m : Nat. m) (λPLUS : Nat → Nat. λm : Nat. PLUS (succ m)) )
--
-- plus compiles to (Foetus)
-- plus := ρPLUS : Nat → (Nat → Nat). λn : Nat. ( (λx : 1. λm : Nat. m) + (λx : Nat. λm : Nat. PLUS x (succ m)) ) (invIN n)
plus : Nat -> Nat -> Nat
plus z = λ m → m
plus (succ n) = λ m →  plus n (succ m)


-- StreamNat with 0s
--
-- Type Encoding
-- StreamNat := ν X. Nat × X
--
-- Intro
-- OUT : ν → Nat × ν
--
-- Elimination
-- S : Π A. ( Π X. (A → X) → A → (Nat × X) ) → A → (ν X. ...)
--
-- Sugar
-- head := pr1 ∘ OUT
-- tail := pr2 ∘ OUT
--
-- 0s compiles to (Mendler)
-- 0s := (R 1) ( ΛX. λ0S : 1 → X. λx : 1. ΛZ. λg : Nat → X → Z. g z (0S x) )
--
-- 0s compiles to (Foetus)
-- 0s := ρ0S : 1 → StreamNat. λx : 1. invOUT(z,0S x)
record StreamNat : Set where
  coinductive
  field
    head' : Nat
    tail' : StreamNat
open StreamNat

0s : StreamNat
head' 0s = z
tail' 0s = 0s

idstr : StreamNat -> StreamNat
head' (idstr s) = head' s
tail' (idstr s) = tail' s


-- Nat with sub
--
-- Type Encoding
-- Nat := μ X. (1,1) + (X,X)
--
-- Intro
-- IN : 1 + μ → μ
--
-- Elimination
-- R : Π A. ( Π X. (X → A) → 1 + X → A ) → (μ X. ...) → A
--
-- Sugar
-- z := IN ∘ inl
-- succ := IN ∘ inr
--
-- sub and subaux compile to
-- sub := R (Nat → Nat) ( ΛX₁. λSUB : X₁ → Nat → Nat. (λx : 1. λm : Nat. z) + (λx₁ : X₁. R Nat ( ΛX₂. SUBAUX : X₂ → Nat. (λx : 1. succ (SUB x₁ z)) + (λx₂ : X₂. SUB x₁ (SUBAUX x₂)))) )
sub : Nat -> Nat -> Nat

subaux : Nat -> Nat -> Nat
subaux z = λ n → succ n
subaux (succ m) = λ n → sub n m

sub z = λ m → z
sub (succ n) = λ m → subaux m n

-- sub : Nat -> Nat -> Nat
-- sub z = λ m → z
-- sub (succ n) = λ {z → succ (sub n z),succ m → sub n m}
