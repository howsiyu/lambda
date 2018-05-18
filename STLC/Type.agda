module STLC.Type (T : Set) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function using (id; _∘_)

data Type : Set where
  base : T → Type
  _⇒_ : Type → Type → Type

data Ctx : Set where
  [] : Ctx
  _∷_ : Type → Ctx → Ctx
  
infix 4 _∋_
data _∋_ : Ctx → Type → Set where
  here  : ∀ {Γ a} → a ∷ Γ ∋ a
  there : ∀ {a Γ b} → Γ ∋ b → a ∷ Γ ∋ b

infix 4 _⊆_
_⊆_ : Ctx → Ctx → Set
Γ ⊆ Δ = ∀ {a} → Γ ∋ a → Δ ∋ a

infix 4 _≡⊆_
_≡⊆_ : ∀ {Γ₁ Γ₂} (ρ₁ ρ₂ : Γ₁ ⊆ Γ₂) → Set
ρ₁ ≡⊆ ρ₂ = ∀ {a} i → ρ₁ {a} i ≡ ρ₂ {a} i

lift : ∀ {a Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → a ∷ Γ₁ ⊆ a ∷ Γ₂
lift ρ here = here
lift ρ (there i) = there (ρ i)

lift-ext : ∀ {a Γ₁ Γ₂} → {ρ₁ ρ₂ : Γ₁ ⊆ Γ₂} → ρ₁ ≡⊆ ρ₂ → lift {a} ρ₁ ≡⊆ lift {a} ρ₂
lift-ext eq here = refl
lift-ext eq (there i) = cong there (eq i)

lift-id : ∀ {a Γ} → id ≡⊆ lift {a} {Γ} {Γ} id
lift-id here = refl
lift-id (there i) = refl

lift-comp : ∀ {a Γ₁ Γ₂ Γ₃} (ρ₂ : Γ₂ ⊆ Γ₃) (ρ₁ : Γ₁ ⊆ Γ₂) → lift {a} (ρ₂ ∘ ρ₁) ≡⊆ lift {a} ρ₂ ∘ lift {a} ρ₁
lift-comp ρ₂ ρ₁ here = refl
lift-comp ρ₂ ρ₁ (there i) = refl
