-- direct translation from STLC.Term

module LC.Term where

open import Data.Nat.Base using (ℕ; suc) public
open import Data.Fin using (Fin) renaming (zero to here; suc to there) public
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

data Term (Γ : ℕ) : Set where
  var : (i : Fin Γ) → Term Γ
  app : Term Γ → Term Γ → Term Γ
  abs : Term (suc Γ) → Term Γ

infix 4 _⊆_
_⊆_ : ℕ → ℕ → Set
Γ₁ ⊆ Γ₂ = Fin Γ₁ → Fin Γ₂

infix 4 _≡⊆_
_≡⊆_ : ∀ {Γ₁ Γ₂ : ℕ} (ρ₁ ρ₂ : Γ₁ ⊆ Γ₂) → Set
ρ₁ ≡⊆ ρ₂ = ∀ i → ρ₁ i ≡ ρ₂ i

lift : ∀ {Γ₁ Γ₂ : ℕ} → Γ₁ ⊆ Γ₂ → suc Γ₁ ⊆ suc Γ₂
lift ρ here = here
lift ρ (there i) = there (ρ i)

lift-ext : ∀ {Γ₁ Γ₂ : ℕ} → {ρ₁ ρ₂ : Γ₁ ⊆ Γ₂} → ρ₁ ≡⊆ ρ₂ → lift ρ₁ ≡⊆ lift ρ₂
lift-ext eq here = refl
lift-ext eq (there i) = cong there (eq i)

lift-id : ∀ {Γ : ℕ} → id ≡⊆ lift {Γ} {Γ} id
lift-id here = refl
lift-id (there i) = refl

lift-comp : ∀ {Γ₁ Γ₂ Γ₃} (ρ₂ : Γ₂ ⊆ Γ₃) (ρ₁ : Γ₁ ⊆ Γ₂) → lift (ρ₂ ∘ ρ₁) ≡⊆ lift ρ₂ ∘ lift ρ₁
lift-comp ρ₂ ρ₁ here = refl
lift-comp ρ₂ ρ₁ (there i) = refl


infix 4 _◀_
_◀_ : ℕ → ℕ → Set
Γ ◀ Δ = Term Γ → Term Δ

infix 4 _≡◄_
_≡◄_ : ∀ {Γ Δ} (τ₁ τ₂ : Γ ◀ Δ) → Set
τ₁ ≡◄ τ₂ = ∀ t → τ₁ t ≡ τ₂ t

rename : ∀ {Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → Γ₁ ◀ Γ₂
rename ρ (var i) = var (ρ i)
rename ρ (app t t₁) = app (rename ρ t) (rename ρ t₁)
rename ρ (abs t) = abs (rename (lift ρ) t)

rename-ext : ∀ {Γ₁ Γ₂} → {ρ₁ ρ₂ : Γ₁ ⊆ Γ₂} → ρ₁ ≡⊆ ρ₂ → rename ρ₁ ≡◄ rename ρ₂
rename-ext eq (var i) = cong var (eq i)
rename-ext eq (app t t₁) = cong₂ app (rename-ext eq t) (rename-ext eq t₁)
rename-ext eq (abs t) = cong abs (rename-ext (lift-ext eq) t)

rename-id : ∀ {Γ} → id ≡◄ rename {Γ} {Γ} id
rename-id (var i) = refl
rename-id (app t t₁) = cong₂ app (rename-id t) (rename-id t₁)
rename-id (abs t) = cong abs (trans (rename-id t) (rename-ext lift-id t))

rename-comp : ∀ {Γ₁ Γ₂ Γ₃} (ρ₂ : Γ₂ ⊆ Γ₃) (ρ₁ : Γ₁ ⊆ Γ₂) → rename (ρ₂ ∘ ρ₁) ≡◄ rename ρ₂ ∘ rename ρ₁
rename-comp ρ₂ ρ₁ (var i) = refl
rename-comp ρ₂ ρ₁ (app t t₁) = cong₂ app (rename-comp ρ₂ ρ₁ t) (rename-comp ρ₂ ρ₁ t₁)
rename-comp ρ₂ ρ₁ (abs t) = cong abs (trans (rename-ext (lift-comp ρ₂ ρ₁) t) (rename-comp (lift ρ₂) (lift ρ₁) t))

weak : ∀ {Γ} → Γ ◀ suc Γ
weak = rename there


infix 4 _◁_
_◁_ : ℕ → ℕ → Set
Γ ◁ Δ = Fin Γ → Term Δ

infix 4 _≡◅_
_≡◅_ : ∀ {Γ Δ} (σ₁ σ₂ : Γ ◁ Δ) → Set
σ₁ ≡◅ σ₂ = ∀ i → σ₁ i ≡ σ₂ i

Mlift : ∀ {Γ Δ} → Γ ◁ Δ → suc Γ ◁ suc Δ
Mlift σ here = var here
Mlift σ (there i) = weak (σ i)

Mlift-ext : ∀ {Γ Δ} → {σ₁ σ₂ : Γ ◁ Δ} → σ₁ ≡◅ σ₂ → Mlift σ₁ ≡◅ Mlift σ₂
Mlift-ext eq here = refl
Mlift-ext eq (there i) = cong weak (eq i)

subst : ∀ {Γ Δ} → Γ ◁ Δ → Γ ◀ Δ
subst σ (var i) = σ i
subst σ (app t t₁) = app (subst σ t) (subst σ t₁)
subst σ (abs t) = abs (subst (Mlift σ) t)

subst-ext : ∀ {Γ Δ} {σ₁ σ₂ : Γ ◁ Δ} → σ₁ ≡◅ σ₂ → subst σ₁ ≡◄ subst σ₂
subst-ext eq (var i) = eq i
subst-ext eq (app t t₁) = cong₂ app (subst-ext eq t) (subst-ext eq t₁)
subst-ext eq (abs t) = cong abs (subst-ext (Mlift-ext eq) t)

subst-rename : ∀ {Γ₁ Γ₂ Δ} (σ : Γ₂ ◁ Δ) (ρ : Γ₁ ⊆ Γ₂) → subst (σ ∘ ρ) ≡◄ subst σ ∘ rename ρ
subst-rename σ ρ (var i) = refl
subst-rename σ ρ (app t t₁) = cong₂ app (subst-rename σ ρ t) (subst-rename σ ρ t₁)
subst-rename σ ρ (abs t) = cong abs (trans (subst-ext lem t) (subst-rename (Mlift σ) (lift ρ) t))
  where
  lem : Mlift (σ ∘ ρ) ≡◅ Mlift σ ∘ lift ρ
  lem here = refl
  lem (there i) = refl

distrib-lift2 : ∀ {Γ Δ₁ Δ₂} (ρ : Δ₁ ⊆ Δ₂) (σ : Γ ◁ Δ₁) → Mlift (rename ρ ∘ σ) ≡◅ rename (lift ρ) ∘ Mlift σ
distrib-lift2 ρ σ here = refl
distrib-lift2 ρ σ (there i) = trans (sym (rename-comp there ρ (σ i))) (rename-comp (lift ρ) there (σ i))
  
rename-subst : ∀ {Γ Δ₁ Δ₂} (ρ : Δ₁ ⊆ Δ₂) (σ : Γ ◁ Δ₁) → rename ρ ∘ subst σ ≡◄ subst (rename ρ ∘ σ)
rename-subst ρ σ (var i) = refl
rename-subst ρ σ (app t t₁) = cong₂ app (rename-subst ρ σ t) (rename-subst ρ σ t₁)
rename-subst ρ σ (abs t) = cong abs (trans (rename-subst (lift ρ) (Mlift σ) t) (sym (subst-ext (distrib-lift2 ρ σ) t)))


id◅ : ∀ {Γ} → Γ ◁ Γ
id◅ = var

Mlift-id : ∀ {Γ} →  id◅ {suc Γ} ≡◅ Mlift (id◅ {Γ})
Mlift-id here = refl
Mlift-id (there t) = refl

subst-id : ∀ {Γ} → id  ≡◄ subst {Γ} id◅
subst-id (var i) = refl
subst-id (app t t₁) = cong₂ app (subst-id t) (subst-id t₁)
subst-id (abs t) = cong abs (trans (subst-id t) (subst-ext Mlift-id t))

infix 9 _∘◅_
_∘◅_ : ∀ {Γ Δ Ξ} → Δ ◁ Ξ → Γ ◁ Δ → Γ ◁ Ξ
(σ₂ ∘◅ σ₁) i = subst σ₂ (σ₁ i)

Mlift-comp : ∀ {Γ Δ Ξ} (σ₂ : Δ ◁ Ξ) (σ₁ : Γ ◁ Δ) → Mlift (σ₂ ∘◅ σ₁) ≡◅ Mlift σ₂ ∘◅ Mlift σ₁
Mlift-comp σ₂ σ₁ here = refl
Mlift-comp σ₂ σ₁ (there i) = trans (rename-subst there σ₂ (σ₁ i)) (subst-rename (Mlift σ₂) there (σ₁ i))

subst-comp : ∀ {Γ Δ Ξ} (σ₂ : Δ ◁ Ξ) (σ₁ : Γ ◁ Δ) → subst (σ₂ ∘◅ σ₁) ≡◄ subst σ₂ ∘ subst σ₁
subst-comp σ₂ σ₁ (var i) = refl
subst-comp σ₂ σ₁ (app t t₁) = cong₂ app (subst-comp σ₂ σ₁ t) (subst-comp σ₂ σ₁ t₁)
subst-comp σ₂ σ₁ (abs t) = cong abs (trans (subst-ext (Mlift-comp σ₂ σ₁) t) (subst-comp (Mlift σ₂) (Mlift σ₁) t))


Msub : ∀ {Γ} → Term Γ → suc Γ ◁ Γ
Msub t here = t
Msub t (there i) = var i

_⟦_⟧ : ∀ {Γ} → Term (suc Γ) → Term Γ → Term Γ
s ⟦ t ⟧ = subst (Msub t) s

⟦⟧-weak : ∀ {Γ} → (t s : Term Γ) → s ≡ weak s ⟦ t ⟧
⟦⟧-weak t s = trans (subst-id s) (subst-rename (Msub t) there s)

distrib-rename-⟦⟧ : ∀ {Γ Δ} → (ρ : Γ ⊆ Δ) → (s : Term (suc Γ)) → (t : Term Γ) → rename ρ (s ⟦ t ⟧) ≡ rename (lift ρ) s ⟦ rename ρ t ⟧
distrib-rename-⟦⟧ ρ s t = trans (rename-subst ρ (Msub t) s) (trans (subst-ext lem s) (subst-rename (Msub (rename ρ t)) (lift ρ) s))
  where
  lem : rename ρ ∘ Msub t ≡◅ Msub (rename ρ t) ∘ (lift ρ)
  lem here = refl
  lem (there i) = refl
  
distrib-subst-⟦⟧ : ∀ {Γ Δ} → (σ : Γ ◁ Δ) → (s : Term (suc Γ)) → (t : Term Γ) → subst σ (s ⟦ t ⟧) ≡ subst (Mlift σ) s ⟦ subst σ t ⟧
distrib-subst-⟦⟧ σ s t = trans (sym (subst-comp σ (Msub t) s)) (trans (subst-ext lem s) (subst-comp (Msub (subst σ t)) (Mlift σ) s))
  where
  lem : σ ∘◅ Msub t ≡◅ Msub (subst σ t) ∘◅ Mlift σ
  lem here = refl
  lem (there i) = ⟦⟧-weak (subst σ t) (σ i)

⟦⟧-varhere : ∀ {Γ} → (t : Term (suc Γ)) → t ≡ rename (lift there) t ⟦ var here ⟧
⟦⟧-varhere t = trans (trans (subst-id t) (subst-ext lem t)) (subst-rename (Msub (var here)) (lift there) t)
  where
  lem : id◅ ≡◅ Msub (var here) ∘ lift there
  lem here = refl
  lem (there i) = refl
