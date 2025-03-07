\begin{code}
module Scoped.RenamingSubstitution where
\end{code}

\begin{code}
open import Data.Nat using (ℕ;zero;suc)
open import Data.Fin using (Fin;zero;suc)
open import Data.Vec using ([];_∷_)
open import Function using (id)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;cong;cong₂)

open import Scoped using (ScopedTy;Tel;Tel⋆;Weirdℕ;WeirdFin;ScopedTm)
open ScopedTy
open ScopedTm
open Weirdℕ
open WeirdFin
open import Builtin.Constant.Type ℕ ScopedTy using (TyCon)
open TyCon
\end{code}

\begin{code}
Ren⋆ : ℕ → ℕ → Set
Ren⋆ m n = Fin m → Fin n

lift⋆ : ∀{m n} → Ren⋆ m n → Ren⋆ (suc m) (suc n)
lift⋆ ρ zero    = zero
lift⋆ ρ (suc α) = suc (ρ α)

ren⋆ : ∀{m n} → Ren⋆ m n → ScopedTy m → ScopedTy n
renTyCon⋆ : ∀{m n} → Ren⋆ m n → TyCon m → TyCon n

renTyCon⋆ ρ integer = integer
renTyCon⋆ ρ bytestring = bytestring
renTyCon⋆ ρ string = string
renTyCon⋆ ρ unit = unit
renTyCon⋆ ρ bool = bool
renTyCon⋆ ρ (list A) = list (ren⋆ ρ A)
renTyCon⋆ ρ (pair A B) = pair (ren⋆ ρ A) (ren⋆ ρ B)
renTyCon⋆ ρ pdata = pdata
renTyCon⋆ ρ bls12-381-g1-element = bls12-381-g1-element
renTyCon⋆ ρ bls12-381-g2-element = bls12-381-g2-element
renTyCon⋆ ρ bls12-381-mlresult = bls12-381-mlresult


ren⋆ ρ (` α) = ` (ρ α)
ren⋆ ρ (A ⇒ B) = ren⋆ ρ A ⇒ ren⋆ ρ B
ren⋆ ρ (Π K A) = Π K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (ƛ K A) = ƛ K (ren⋆ (lift⋆ ρ) A)
ren⋆ ρ (A · B) = ren⋆ ρ A · ren⋆ ρ B
ren⋆ ρ (con c) = con (renTyCon⋆ ρ c)
ren⋆ ρ (μ A B) = μ (ren⋆ ρ A) (ren⋆ ρ B)
ren⋆ ρ missing = missing

ren⋆T : ∀{m n o} → Ren⋆ m n → Tel⋆ m o → Tel⋆ n o
ren⋆T ρ⋆ []       = []
ren⋆T ρ⋆ (A ∷ As) = ren⋆ ρ⋆ A ∷ ren⋆T ρ⋆ As

Ren : ∀{m n} → Weirdℕ m → Weirdℕ n → Set
Ren m n = WeirdFin m → WeirdFin n

lift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Ren w v → Ren (S w) (S v)
lift ρ Z     = Z
lift ρ (S x) = S (ρ x)

⋆lift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Ren w v → Ren (T w) (T v)
⋆lift ρ (T x) = T (ρ x)

ren : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Ren⋆ m n → Ren w v → ScopedTm w
  → ScopedTm v
renT : ∀{m n o}{w : Weirdℕ m}{v : Weirdℕ n} → Ren⋆ m n → Ren w v
  → Tel w o → Tel v o

ren ρ⋆ ρ (` x) = ` (ρ x)
ren ρ⋆ ρ (Λ K t) = Λ K (ren (lift⋆ ρ⋆) (⋆lift ρ) t) 
ren ρ⋆ ρ (t ·⋆ A) = ren ρ⋆ ρ t ·⋆ ren⋆ ρ⋆ A
ren ρ⋆ ρ (ƛ A t)  = ƛ (ren⋆ ρ⋆ A) (ren ρ⋆ (lift ρ) t)
ren ρ⋆ ρ (t · u) = ren ρ⋆ ρ t · ren ρ⋆ ρ u
ren ρ⋆ ρ (con c) = con c
ren ρ⋆ ρ (error A) = error (ren⋆ ρ⋆ A)
ren ρ⋆ ρ (builtin b) = builtin b
ren ρ⋆ ρ (wrap A B t) = wrap (ren⋆ ρ⋆ A) (ren⋆ ρ⋆ B) (ren ρ⋆ ρ t)
ren ρ⋆ ρ (unwrap t) = unwrap (ren ρ⋆ ρ t)

renT ρ⋆ ρ []       = []
renT ρ⋆ ρ (t ∷ ts) = ren ρ⋆ ρ t ∷ renT ρ⋆ ρ ts

-- substitution
Sub⋆ : ℕ → ℕ → Set
Sub⋆ m n = Fin m → ScopedTy n

slift⋆ : ∀{m n} → Sub⋆ m n → Sub⋆ (suc m) (suc n)
slift⋆ ρ zero    = ` zero
slift⋆ ρ (suc α) = ren⋆ suc (ρ α)

sub⋆ : ∀{m n} → Sub⋆ m n → ScopedTy m → ScopedTy n
subTyCon⋆ : ∀{m n} → Sub⋆ m n → TyCon m → TyCon n

subTyCon⋆ σ integer = integer
subTyCon⋆ σ bytestring = bytestring
subTyCon⋆ σ string = string
subTyCon⋆ σ unit = unit
subTyCon⋆ σ bool = bool
subTyCon⋆ σ (list A) = list (sub⋆ σ A)
subTyCon⋆ σ (pair A B) = pair (sub⋆ σ A) (sub⋆ σ B)
subTyCon⋆ σ pdata = pdata
subTyCon⋆ σ bls12-381-g1-element = bls12-381-g1-element
subTyCon⋆ σ bls12-381-g2-element = bls12-381-g2-element
subTyCon⋆ σ bls12-381-mlresult = bls12-381-mlresult

sub⋆ σ (` α)   = σ α
sub⋆ σ (A ⇒ B) = sub⋆ σ A ⇒ sub⋆ σ B
sub⋆ σ (Π K A) = Π K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (ƛ K A) = ƛ K (sub⋆ (slift⋆ σ) A)
sub⋆ σ (A · B) = sub⋆ σ A · sub⋆ σ B
sub⋆ σ (con c) = con (subTyCon⋆ σ c)
sub⋆ σ (μ A B) = μ (sub⋆ σ A) (sub⋆ σ B)
sub⋆ ρ missing = missing

sub⋆T : ∀{m n o} → Sub⋆ m n → Tel⋆ m o → Tel⋆ n o
sub⋆T σ⋆ []       = []
sub⋆T σ⋆ (A ∷ As) = sub⋆ σ⋆ A ∷ sub⋆T σ⋆ As

Sub : ∀{m n} → Weirdℕ m → Weirdℕ n → Set
Sub v w = WeirdFin v → ScopedTm w

slift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Sub v w → Sub (S v) (S w)
slift σ Z     = ` Z
slift σ (S x) = ren id S (σ x)

⋆slift : ∀{m n}{w : Weirdℕ m}{v : Weirdℕ n} → Sub w v → Sub (T w) (T v)
⋆slift σ (T x) = ren suc T (σ x)

sub : ∀{m n}{v : Weirdℕ m}{w : Weirdℕ n} → Sub⋆ m n → Sub v w
  → ScopedTm v → ScopedTm w
subT : ∀{m n o}{v : Weirdℕ m}{w : Weirdℕ n} → Sub⋆ m n → Sub v w
  → Tel v o → Tel w o

sub σ⋆ σ (` x) = σ x
sub σ⋆ σ (Λ K t) = Λ K (sub (slift⋆ σ⋆) (⋆slift σ) t)
sub σ⋆ σ (t ·⋆ A) = sub σ⋆ σ t ·⋆ sub⋆ σ⋆ A
sub σ⋆ σ (ƛ A t) = ƛ (sub⋆ σ⋆ A) (sub σ⋆ (slift σ) t)
sub σ⋆ σ (t · u) = sub σ⋆ σ t · sub σ⋆ σ u
sub σ⋆ σ (con c) = con c
sub σ⋆ σ (error A) = error (sub⋆ σ⋆ A)
sub σ⋆ σ (builtin b) = builtin b
sub σ⋆ σ (wrap A B t) = wrap (sub⋆ σ⋆ A) (sub⋆ σ⋆ B) (sub σ⋆ σ t)
sub σ⋆ σ (unwrap t) = unwrap (sub σ⋆ σ t)

subT σ⋆ σ []       = []
subT σ⋆ σ (t ∷ ts) = sub σ⋆ σ t ∷ subT σ⋆ σ ts

ext : ∀{m n}{v : Weirdℕ m}{w : Weirdℕ n} → Sub v w → ScopedTm w → Sub (S v) w
ext σ t Z = t
ext σ t (S x) = σ x

⋆ext : ∀{m n}{v : Weirdℕ m}{w : Weirdℕ n} → Sub v w → Sub (T v) w
⋆ext σ (T x) = σ x

ext⋆ : ∀{m n} → Sub⋆ m n → ScopedTy n → Sub⋆ (suc m) n
ext⋆ σ A zero = A
ext⋆ σ A (suc α) = σ α

_[_] : ∀{n}{v : Weirdℕ n} → ScopedTm (S v) → ScopedTm v → ScopedTm v
t [ u ] = sub ` (ext ` u) t

_[_]⋆ : ∀{n}{w : Weirdℕ n} → ScopedTm (T w) → ScopedTy n → ScopedTm w
t [ A ]⋆ = sub (ext⋆ ` A) (⋆ext `) t
\end{code}

# Proofs

\begin{code}
lift⋆-cong : ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → lift⋆ ρ x ≡ lift⋆ ρ' x
lift⋆-cong p zero    = refl
lift⋆-cong p (suc x) = cong suc (p x)

ren⋆-cong : ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → ren⋆ ρ x ≡ ren⋆ ρ' x
renTyCon⋆-cong : ∀{m n}{ρ ρ' : Ren⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → renTyCon⋆ ρ x ≡ renTyCon⋆ ρ' x

renTyCon⋆-cong p integer = refl
renTyCon⋆-cong p bytestring = refl
renTyCon⋆-cong p string = refl
renTyCon⋆-cong p unit = refl
renTyCon⋆-cong p bool = refl
renTyCon⋆-cong p (list A) = cong list (ren⋆-cong p A)
renTyCon⋆-cong p (pair A B) = cong₂ pair (ren⋆-cong p A) (ren⋆-cong p B)
renTyCon⋆-cong p pdata = refl
renTyCon⋆-cong p bls12-381-g1-element = refl
renTyCon⋆-cong p bls12-381-g2-element = refl
renTyCon⋆-cong p bls12-381-mlresult = refl

ren⋆-cong p (` x)       = cong ` (p x)
ren⋆-cong p (A ⇒ B)     = cong₂ _⇒_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (Π K A)     = cong (Π K) (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (ƛ K A)     = cong (ƛ K) (ren⋆-cong (lift⋆-cong p) A)
ren⋆-cong p (A · B)     = cong₂ _·_ (ren⋆-cong p A) (ren⋆-cong p B)
ren⋆-cong p (con c)     = cong con (renTyCon⋆-cong p c)
ren⋆-cong p (μ pat arg) = cong₂ μ (ren⋆-cong p pat) (ren⋆-cong p arg)
ren⋆-cong p missing     = refl

slift⋆-cong : ∀{m n}{ρ ρ' : Sub⋆ m n}
  → (∀ x → ρ x ≡ ρ' x)
  → ∀ x → slift⋆ ρ x ≡ slift⋆ ρ' x
slift⋆-cong p zero    = refl
slift⋆-cong p (suc x) = cong (ren⋆ suc) (p x) 

sub⋆-cong : ∀{m n}{σ σ' : Sub⋆ m n}
  → (∀ x → σ x ≡ σ' x)
  → ∀ x → sub⋆ σ x ≡ sub⋆ σ' x
subTyCon⋆-cong : ∀{m n}{σ σ' : Sub⋆ m n}
  → (∀ x → σ x ≡ σ' x)
  → ∀ x → subTyCon⋆ σ x ≡ subTyCon⋆ σ' x

subTyCon⋆-cong p integer = refl
subTyCon⋆-cong p bytestring = refl
subTyCon⋆-cong p string = refl
subTyCon⋆-cong p unit = refl
subTyCon⋆-cong p bool = refl
subTyCon⋆-cong p (list A) = cong list (sub⋆-cong p A)
subTyCon⋆-cong p (pair A B) = cong₂ pair (sub⋆-cong p A) (sub⋆-cong p B)
subTyCon⋆-cong p pdata = refl
subTyCon⋆-cong p bls12-381-g1-element = refl
subTyCon⋆-cong p bls12-381-g2-element = refl
subTyCon⋆-cong p bls12-381-mlresult = refl

sub⋆-cong p (` x)       = p x
sub⋆-cong p (A ⇒ B)     = cong₂ _⇒_ (sub⋆-cong p A) (sub⋆-cong p B)
sub⋆-cong p (Π K A)     = cong (Π K) (sub⋆-cong (slift⋆-cong p) A)
sub⋆-cong p (ƛ K A)     = cong (ƛ K) (sub⋆-cong (slift⋆-cong p) A)
sub⋆-cong p (A · B)     = cong₂ _·_ (sub⋆-cong p A) (sub⋆-cong p B)
sub⋆-cong p (con c)     = cong con (subTyCon⋆-cong p c)
sub⋆-cong p (μ pat arg) = cong₂ μ (sub⋆-cong p pat) (sub⋆-cong p arg)
sub⋆-cong p missing     = refl

sub-cons : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'} → Sub w w' → ScopedTm w' →
  Sub (S w) w'
sub-cons σ t Z     = t
sub-cons σ t (S x) = σ x  

sub-cons⋆ : ∀{n n'}{w : Weirdℕ n}{w' : Weirdℕ n'} → Sub w w' → Sub (T w) w'
sub-cons⋆ σ (T x) = σ x

\end{code}
