-- lots of codes are shamelessly copied from
-- https://hub.darcs.net/roconnor/STLC/browse/src/STLC
-- though the main idea is probably well-known as can be seen in
-- http://strictlypositive.org/ren-sub.pdf
-- https://www.lri.fr/~keller/Documents-recherche/Stage08/Parallel-substitution/report.pdf

module STLC.Term (T : Set) where

open import STLC.Type T
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)

infix 4 _⊢_
data _⊢_ (Γ : Ctx) : Type → Set where
  var : ∀ {a} → (i : Γ ∋ a) → Γ ⊢ a
  app : ∀ {a b} → Γ ⊢ a ⇒ b → Γ ⊢ a → Γ ⊢ b
  abs : ∀ {a b} → a ∷ Γ ⊢ b → Γ ⊢ a ⇒ b


infix 4 _◀_
_◀_ : Ctx → Ctx → Set
Γ ◀ Δ = ∀ {a} → Γ ⊢ a → Δ ⊢ a

infix 4 _≡◄_
_≡◄_ : ∀ {Γ Δ} (τ₁ τ₂ : Γ ◀ Δ) → Set
τ₁ ≡◄ τ₂ = ∀ {a} t → τ₁ {a} t ≡ τ₂ {a} t

map : ∀ {Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → Γ₁ ◀ Γ₂
map ρ (var i) = var (ρ i)
map ρ (app t t₁) = app (map ρ t) (map ρ t₁)
map ρ (abs t) = abs (map (lift ρ) t)

map-ext : ∀ {Γ₁ Γ₂} → {ρ₁ ρ₂ : Γ₁ ⊆ Γ₂} → ρ₁ ≡⊆ ρ₂ → map ρ₁ ≡◄ map ρ₂
map-ext eq (var i) = cong var (eq i)
map-ext eq (app t t₁) = cong₂ app (map-ext eq t) (map-ext eq t₁)
map-ext eq (abs t) = cong abs (map-ext (lift-ext eq) t)

map-id : ∀ {Γ} → id ≡◄ map {Γ} {Γ} id
map-id (var i) = refl
map-id (app t t₁) = cong₂ app (map-id t) (map-id t₁)
map-id (abs t) = cong abs (trans (map-id t) (map-ext lift-id t))

map-comp : ∀ {Γ₁ Γ₂ Γ₃} (ρ₂ : Γ₂ ⊆ Γ₃) (ρ₁ : Γ₁ ⊆ Γ₂) → map (ρ₂ ∘ ρ₁) ≡◄ map ρ₂ ∘ map ρ₁
map-comp ρ₂ ρ₁ (var i) = refl
map-comp ρ₂ ρ₁ (app t t₁) = cong₂ app (map-comp ρ₂ ρ₁ t) (map-comp ρ₂ ρ₁ t₁)
map-comp ρ₂ ρ₁ (abs t) = cong abs (trans (map-ext (lift-comp ρ₂ ρ₁) t) (map-comp (lift ρ₂) (lift ρ₁) t))

weak : ∀ {a Γ} → Γ ◀ a ∷ Γ
weak = map there


infix 4 _◁_
_◁_ : Ctx → Ctx → Set
Γ ◁ Δ = ∀ {a} → Γ ∋ a → Δ ⊢ a

infix 4 _≡◅_
_≡◅_ : ∀ {Γ Δ : Ctx} (σ₁ σ₂ : Γ ◁ Δ) → Set
σ₁ ≡◅ σ₂ = ∀ {a} i → σ₁ {a} i ≡ σ₂ {a} i

Mlift : ∀ {a Γ Δ} → Γ ◁ Δ → a ∷ Γ ◁ a ∷ Δ
Mlift σ here = var here
Mlift σ (there i) = weak (σ i)

Mlift-ext : ∀ {a Γ Δ} → {σ₁ σ₂ : Γ ◁ Δ} → σ₁ ≡◅ σ₂ → Mlift {a} σ₁ ≡◅ Mlift {a} σ₂
Mlift-ext eq here = refl
Mlift-ext eq (there i) = cong weak (eq i)

bind : ∀ {Γ Δ} → Γ ◁ Δ → Γ ◀ Δ
bind σ (var i) = σ i
bind σ (app t t₁) = app (bind σ t) (bind σ t₁)
bind σ (abs t) = abs (bind (Mlift σ) t)

bind-ext : ∀ {Γ Δ} {σ₁ σ₂ : Γ ◁ Δ} → σ₁ ≡◅ σ₂ → bind σ₁ ≡◄ bind σ₂
bind-ext eq (var i) = eq i
bind-ext eq (app t t₁) = cong₂ app (bind-ext eq t) (bind-ext eq t₁)
bind-ext eq (abs t) = cong abs (bind-ext (Mlift-ext eq) t)

distrib-lift : ∀ {Γ₁ Γ₂ Δ} (σ : Γ₂ ◁ Δ) (ρ : Γ₁ ⊆ Γ₂) {a} → Mlift {a} (σ ∘ ρ) ≡◅ Mlift σ ∘ lift ρ
distrib-lift σ ρ here = refl
distrib-lift σ ρ (there i) = refl
  
bind-map : ∀ {Γ₁ Γ₂ Δ} (σ : Γ₂ ◁ Δ) (ρ : Γ₁ ⊆ Γ₂) → bind (σ ∘ ρ) ≡◄ bind σ ∘ map ρ
bind-map σ ρ (var i) = refl
bind-map σ ρ (app t t₁) = cong₂ app (bind-map σ ρ t) (bind-map σ ρ t₁)
bind-map σ ρ (abs t) = cong abs (trans (bind-ext (distrib-lift σ ρ) t) (bind-map (Mlift σ) (lift ρ) t))

distrib-lift2 : ∀ {Γ Δ₁ Δ₂} (ρ : Δ₁ ⊆ Δ₂) (σ : Γ ◁ Δ₁) {a} → Mlift {a} (map ρ ∘ σ) ≡◅ map (lift ρ) ∘ Mlift {a} σ
distrib-lift2 ρ σ here = refl
distrib-lift2 ρ σ (there i) = trans (sym (map-comp there ρ (σ i))) (map-comp (lift ρ) there (σ i))
  
map-bind : ∀ {Γ Δ₁ Δ₂} (ρ : Δ₁ ⊆ Δ₂) (σ : Γ ◁ Δ₁) → map ρ ∘ bind σ ≡◄ bind (map ρ ∘ σ)
map-bind ρ σ (var i) = refl
map-bind ρ σ (app t t₁) = cong₂ app (map-bind ρ σ t) (map-bind ρ σ t₁)
map-bind ρ σ (abs t) = cong abs (trans (map-bind (lift ρ) (Mlift σ) t) (sym (bind-ext (distrib-lift2 ρ σ) t)))

comm-weak-bind : ∀ {a Γ Δ} (σ : Γ ◁ Δ) → weak {a} ∘ bind σ ≡◄ bind (Mlift {a} σ) ∘ weak {a}
comm-weak-bind σ t = trans (map-bind there σ t) (trans (bind-ext lem t) (bind-map (Mlift σ) there t))
  where
  lem : weak ∘ σ ≡◅ Mlift σ ∘ there
  lem here = refl
  lem (there i) = refl
  
id◅ : ∀ {Γ} → Γ ◁ Γ
id◅ = var

Mlift-id : ∀ {Γ a} →  id◅ {a ∷ Γ} ≡◅ Mlift {a} (id◅ {Γ})
Mlift-id here = refl
Mlift-id (there t) = refl

bind-id : ∀ {Γ} → id  ≡◄ bind {Γ} id◅
bind-id (var i) = refl
bind-id (app t t₁) = cong₂ app (bind-id t) (bind-id t₁)
bind-id (abs t) = cong abs (trans (bind-id t) (bind-ext Mlift-id t))

infix 9 _<=<_
_<=<_ : ∀ {Γ Δ Ξ} → Δ ◁ Ξ → Γ ◁ Δ → Γ ◁ Ξ
σ₂ <=< σ₁ = bind σ₂ ∘ σ₁

Mlift-comp : ∀ {a Γ Δ Ξ} (σ₂ : Δ ◁ Ξ) (σ₁ : Γ ◁ Δ) → Mlift {a} (σ₂ <=< σ₁) ≡◅ Mlift {a} σ₂ <=< Mlift {a} σ₁
Mlift-comp σ₂ σ₁ here = refl
Mlift-comp σ₂ σ₁ (there i) = trans (map-bind there σ₂ (σ₁ i)) (bind-map (Mlift σ₂) there (σ₁ i))

bind-comp : ∀ {Γ Δ Ξ} (σ₂ : Δ ◁ Ξ) (σ₁ : Γ ◁ Δ) → bind (σ₂ <=< σ₁) ≡◄ bind σ₂ ∘ bind σ₁
bind-comp σ₂ σ₁ (var i) = refl
bind-comp σ₂ σ₁ (app t t₁) = cong₂ app (bind-comp σ₂ σ₁ t) (bind-comp σ₂ σ₁ t₁)
bind-comp σ₂ σ₁ (abs t) = cong abs (trans (bind-ext (Mlift-comp σ₂ σ₁) t) (bind-comp (Mlift σ₂) (Mlift σ₁) t))

Mcons : ∀ {Γ Δ a} → Δ ⊢ a → Γ ◁ Δ → a ∷ Γ ◁ Δ
Mcons t σ here = t
Mcons t σ (there i) = σ i

Mcons-ext : ∀ {Γ Δ a} → (t : Δ ⊢ a) → {σ₁ σ₂ : Γ ◁ Δ} → σ₁ ≡◅ σ₂ → Mcons t σ₁ ≡◅ Mcons t σ₂
Mcons-ext t eq here = refl
Mcons-ext t eq (there i) = eq i

Mcons-lift : ∀ {Γ₁ Γ₂ Δ a} (t : Δ ⊢ a) (σ : Γ₂ ◁ Δ) (ρ : Γ₁ ⊆ Γ₂) → Mcons t (σ ∘ ρ) ≡◅ Mcons t σ ∘ lift ρ
Mcons-lift t σ ρ here = refl
Mcons-lift t σ ρ (there i) = refl

Mcons-lem : ∀ {Γ₁ Γ₂ Δ a} (t : Δ ⊢ a) (σ : Γ₂ ◁ Δ) (ρ : Γ₁ ⊆ Γ₂) → bind (Mcons t (σ ∘ ρ)) ≡◄ bind (Mcons t σ) ∘ map (lift ρ)
Mcons-lem t σ ρ s = trans (bind-ext (Mcons-lift t σ ρ) s) (bind-map (Mcons t σ) (lift ρ) s)

Mcons-here : ∀ {Γ Δ a} → (σ : Γ ◁ Δ) → Mlift {a} σ ≡◅  Mcons (var here) (weak {a} ∘ σ)
Mcons-here σ here = refl
Mcons-here σ (there i) = refl

Msub : ∀ {Γ a} → Γ ⊢ a → a ∷ Γ ◁ Γ
Msub t = Mcons t id◅

_⟦_⟧ : ∀ {Γ a b} → a ∷ Γ ⊢ b → Γ ⊢ a → Γ ⊢ b
s ⟦ t ⟧ = bind (Msub t) s

⟦⟧-weak : ∀ {Γ a b} → (t : Γ ⊢ a) → (s : Γ ⊢ b) → s ≡ weak s ⟦ t ⟧
⟦⟧-weak t s = trans (bind-id s) (bind-map (Msub t) there s)


distrib-map-⟦⟧ : ∀ {Γ Δ} → (ρ : Γ ⊆ Δ) → ∀ {a b} → (s : (a ∷ Γ) ⊢ b) → (t : Γ ⊢ a) → map ρ (s ⟦ t ⟧) ≡ map (lift ρ) s ⟦ map ρ t ⟧
distrib-map-⟦⟧ ρ s t = trans (map-bind ρ (Msub t) s) (trans (bind-ext lem s) (bind-map (Msub (map ρ t)) (lift ρ) s))
  where
  lem : map ρ ∘ Msub t ≡◅ Msub (map ρ t) ∘ (lift ρ)
  lem here = refl
  lem (there i) = refl
  
distrib-bind-⟦⟧ : ∀ {Γ Δ} → (σ : Γ ◁ Δ) → ∀ {a b} → (s : (a ∷ Γ) ⊢ b) → (t : Γ ⊢ a) → bind σ (s ⟦ t ⟧) ≡ bind (Mlift σ) s ⟦ bind σ t ⟧
distrib-bind-⟦⟧ σ s t = trans (sym (bind-comp σ (Msub t) s)) (trans (bind-ext lem s) (bind-comp (Msub (bind σ t)) (Mlift σ) s))
  where
  lem : σ <=< Msub t ≡◅ Msub (bind σ t) <=< Mlift σ
  lem here = refl
  lem (there i) = ⟦⟧-weak (bind σ t) (σ i)

⟦⟧-here : ∀ {Γ a b} → (t : a ∷ Γ ⊢ b) → t ≡ map (lift there) t ⟦ var here ⟧
⟦⟧-here t = trans (trans (bind-id t) (bind-ext Mlift-id t)) (trans (bind-ext (Mcons-here id◅) t) (Mcons-lem (var here) id◅ there t))
