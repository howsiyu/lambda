{-# OPTIONS --with-K #-}

module STSKI.Term (T : Set) where

open import STLC.Type T
open import Function using (_∘_; flip)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])
open import Data.Product using (∃; _×_; _,_; proj₂)

infix 4 _⊢_
data _⊢_ (Γ : Ctx) : Type → Set where
  I : ∀ {a} → Γ ⊢ a ⇒ a
  K : ∀ {a b} → Γ ⊢ a ⇒ (b ⇒ a)
  S : ∀ {a b c} → Γ ⊢ (a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))
  var : ∀ {a} → (i : Γ ∋ a) → Γ ⊢ a
  app : ∀ {a b} → (A : Γ ⊢ a ⇒ b) → (B : Γ ⊢ a) → Γ ⊢ b

infix 4 _◀_
_◀_ : Ctx → Ctx → Set
Γ ◀ Δ = ∀ {a} → Γ ⊢ a → Δ ⊢ a

infix 4 _≡◄_
_≡◄_ : ∀ {Γ Δ} (τ₁ τ₂ : Γ ◀ Δ) → Set
τ₁ ≡◄ τ₂ = ∀ {a} t → τ₁ {a} t ≡ τ₂ {a} t

map : ∀ {Γ₁ Γ₂} → Γ₁ ⊆ Γ₂ → Γ₁ ◀ Γ₂
map ρ I = I
map ρ K = K
map ρ S = S
map ρ (var i) = var (ρ i)
map ρ (app t t₁) = app (map ρ t) (map ρ t₁)

map-ext : ∀ {Γ₁ Γ₂} → {ρ₁ ρ₂ : Γ₁ ⊆ Γ₂} → ρ₁ ≡⊆ ρ₂ → map ρ₁ ≡◄ map ρ₂
map-ext eq I = refl
map-ext eq K = refl
map-ext eq S = refl
map-ext eq (var i) = cong var (eq i)
map-ext eq (app A B) = cong₂ app (map-ext eq A) (map-ext eq B)

map-comp : ∀ {Γ₁ Γ₂ Γ₃} (ρ₂ : Γ₂ ⊆ Γ₃) (ρ₁ : Γ₁ ⊆ Γ₂) → map (ρ₂ ∘ ρ₁) ≡◄ map ρ₂ ∘ map ρ₁
map-comp ρ₂ ρ₁ I = refl
map-comp ρ₂ ρ₁ K = refl
map-comp ρ₂ ρ₁ S = refl
map-comp ρ₂ ρ₁ (var i) = refl
map-comp ρ₂ ρ₁ (app A A₁) = cong₂ app (map-comp ρ₂ ρ₁ A) (map-comp ρ₂ ρ₁ A₁)

weak : ∀ {a Γ} → Γ ◀ a ∷ Γ
weak = map there

data Abs (Γ : Ctx) (a : Type) : Type → Set where
  Abs-I : Abs Γ a a 
  Abs-K : ∀ {b} → Γ ⊢ b → Abs Γ a b 
  Abs-S : ∀ {b c} → Abs Γ a (b ⇒ c) → Abs Γ a b → Abs Γ a c

abs-to-term : ∀ {Γ a b} → Abs Γ a b → Γ ⊢ a ⇒ b
abs-to-term Abs-I = I
abs-to-term (Abs-K A) = app K A
abs-to-term (Abs-S A B) = app (app S (abs-to-term A)) (abs-to-term B)

abs' : ∀ {Γ a b} → a ∷ Γ ⊢ b → Abs Γ a b
abs' I = Abs-K I
abs' K =  Abs-K K
abs' S = Abs-K S
abs' (var here) = Abs-I
abs' (var (there i)) = Abs-K (var i)
abs' (app A B) with abs' A | abs' B
... | Abs-K A' | Abs-K B' = Abs-K (app A' B')
... | A' | B' = Abs-S A' B'

abs : ∀ {Γ a b} → a ∷ Γ ⊢ b → Γ ⊢ a ⇒ b
abs = abs-to-term ∘ abs'

Abs-I-lemma : ∀ {Γ a} (A : a ∷ Γ ⊢ a) → abs' A ≡ Abs-I → A ≡ var here
Abs-I-lemma I ()
Abs-I-lemma K ()
Abs-I-lemma S ()
Abs-I-lemma (var here) eq = refl
Abs-I-lemma (var (there i)) ()
Abs-I-lemma (app A A₁) eq with abs' A | abs' A₁
Abs-I-lemma (app A A₁) () | Abs-K _ | Abs-I
Abs-I-lemma (app A A₁) () | Abs-K _ | Abs-K _
Abs-I-lemma (app A A₁) () | Abs-K _ | Abs-S _ _
Abs-I-lemma (app A A₁) () | Abs-S _ _ | Abs-I
Abs-I-lemma (app A A₁) () | Abs-S _ _ | Abs-K _
Abs-I-lemma (app A A₁) () | Abs-S _ _ | Abs-S _ _

Abs-K-inj : ∀ {Γ a b A A₁} → Abs-K {Γ} {a} {b} A ≡ Abs-K A₁ → A ≡ A₁
Abs-K-inj refl = refl

Abs-K-lemma : ∀ {Γ a b} (A : a ∷ Γ ⊢ b) {A'} → abs' A ≡ Abs-K A' → A ≡ weak A'
Abs-K-lemma I refl = refl
Abs-K-lemma K refl = refl
Abs-K-lemma S refl = refl
Abs-K-lemma (var here) ()
Abs-K-lemma (var (there i)) refl = refl
Abs-K-lemma (app A A₁) eq with abs' A | inspect abs' A
Abs-K-lemma (app A A₁) () | Abs-I | _
Abs-K-lemma (app A A₁) () | Abs-S _ _ | _
Abs-K-lemma (app A A₁) eq | Abs-K A' | [ eq0 ] with abs' A₁ | inspect abs' A₁
Abs-K-lemma (app A A₁) () | Abs-K A' | [ eq0 ] | Abs-I | _
Abs-K-lemma (app A A₁) () | Abs-K A' | [ eq0 ] | Abs-S _ _ | _
Abs-K-lemma (app A A₁) eq | Abs-K A' | [ eq0 ] | Abs-K A₁' | [ eq1 ] = trans (cong₂ app (Abs-K-lemma A eq0) (Abs-K-lemma A₁ eq1)) (cong weak (Abs-K-inj eq))


comm-weak-map : ∀ {a Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {b} (A' : Γ₁ ⊢ b) → map (lift ρ) (weak {a} A') ≡ weak {a} (map ρ A')
comm-weak-map ρ I = refl
comm-weak-map ρ K = refl
comm-weak-map ρ S = refl
comm-weak-map ρ (var i) = refl
comm-weak-map ρ (app A' B') = cong₂ app (comm-weak-map ρ A') (comm-weak-map ρ B')

Abs-map : ∀ {Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {a b} → Abs Γ₁ a b → Abs Γ₂ a b
Abs-map ρ Abs-I = Abs-I
Abs-map ρ (Abs-K A) = Abs-K (map ρ A)
Abs-map ρ (Abs-S A' B') = Abs-S (Abs-map ρ A') (Abs-map ρ B')

Abs-map-lemma : ∀ {Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {a b} (A' : Abs Γ₁ a b) → abs-to-term (Abs-map ρ A') ≡ map ρ (abs-to-term A')
Abs-map-lemma ρ Abs-I = refl
Abs-map-lemma ρ (Abs-K A') = refl
Abs-map-lemma ρ (Abs-S A' B') = cong₂ app (cong (app S) (Abs-map-lemma ρ A')) (Abs-map-lemma ρ B')

comm-map-abs' : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) {a b} (A : a ∷ Γ ⊢ b) → abs' (map (lift ρ) A) ≡ Abs-map ρ (abs' A)
comm-map-abs' ρ I = refl
comm-map-abs' ρ K = refl
comm-map-abs' ρ S = refl
comm-map-abs' ρ (var here) = refl
comm-map-abs' ρ (var (there i)) = refl
comm-map-abs' ρ (app A B) with comm-map-abs' ρ A | comm-map-abs' ρ B
... | prfA | prfB with abs' A
... | Abs-I rewrite prfA | prfB = refl
... | Abs-S _ _ rewrite prfA | prfB = refl
... | Abs-K A' rewrite prfA with abs' B
... | Abs-I rewrite prfB = refl
... | Abs-S _ _ rewrite prfB = refl
... | Abs-K B' rewrite prfB = refl

comm-map-abs : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) {a b} (A : a ∷ Γ ⊢ b) → abs (map (lift ρ) A) ≡ map ρ (abs A)
comm-map-abs ρ A = trans (cong abs-to-term (comm-map-abs' ρ A)) (Abs-map-lemma ρ (abs' A))


infix 4 _◁_
_◁_ : Ctx → Ctx → Set
Γ ◁ Δ = ∀ {a} → Γ ∋ a → Δ ⊢ a

infix 4 _≡◅_
_≡◅_ : ∀ {Γ Δ : Ctx} (σ₁ σ₂ : Γ ◁ Δ) → Set
σ₁ ≡◅ σ₂ = ∀ {a} i → σ₁ {a} i ≡ σ₂ {a} i

Mlift : ∀ {a Γ Δ} → Γ ◁ Δ → a ∷ Γ ◁ a ∷ Δ
Mlift σ here = var here
Mlift σ (there i) = weak (σ i)

bind : ∀ {Γ Δ} → Γ ◁ Δ → Γ ◀ Δ
bind σ I = I
bind σ K = K
bind σ S = S
bind σ (var i) = σ i
bind σ (app A A₁) = app (bind σ A) (bind σ A₁)

bind-ext : ∀ {Γ Δ} {σ₁ σ₂ : Γ ◁ Δ} → σ₁ ≡◅ σ₂ → bind σ₁ ≡◄ bind σ₂
bind-ext eq I = refl
bind-ext eq K = refl
bind-ext eq S = refl
bind-ext eq (var i) = eq i
bind-ext eq (app A B) = cong₂ app (bind-ext eq A) (bind-ext eq B)

id◅ : ∀ {Γ} → Γ ◁ Γ
id◅ = var

Mcons : ∀ {Γ Δ a} → Δ ⊢ a → Γ ◁ Δ → a ∷ Γ ◁ Δ
Mcons t σ here = t
Mcons t σ (there i) = σ i

Msub : ∀ {Γ a} → Γ ⊢ a → a ∷ Γ ◁ Γ
Msub t = Mcons t id◅

_⟦_⟧ : ∀ {Γ a b} → a ∷ Γ ⊢ b → Γ ⊢ a → Γ ⊢ b
s ⟦ t ⟧ = bind (Msub t) s

comm-weak-bind : ∀ {a Γ Δ} (σ : Γ ◁ Δ) → bind (Mlift {a} σ) ∘ weak {a} ≡◄ weak {a} ∘ bind σ
comm-weak-bind σ I = refl
comm-weak-bind σ K = refl
comm-weak-bind σ S = refl
comm-weak-bind σ (var i) = refl
comm-weak-bind σ (app A A₁) = cong₂ app (comm-weak-bind σ A) (comm-weak-bind σ A₁)

Abs-bind : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} → Abs Γ a b → Abs Δ a b
Abs-bind σ Abs-I = Abs-I
Abs-bind σ (Abs-K A) = Abs-K (bind σ A)
Abs-bind σ (Abs-S A' B') = Abs-S (Abs-bind σ A') (Abs-bind σ B')

Abs-bind-lemma : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} (A' : Abs Γ a b) → abs-to-term (Abs-bind σ A') ≡ bind σ (abs-to-term A')
Abs-bind-lemma σ Abs-I = refl
Abs-bind-lemma σ (Abs-K A) = refl
Abs-bind-lemma σ (Abs-S A' B') = cong₂ app (cong (app S) (Abs-bind-lemma σ A')) (Abs-bind-lemma σ B')

abs'-weak : ∀ {a Γ b} (A : Γ ⊢ b) → abs' (weak {a} A) ≡ Abs-K A
abs'-weak I = refl
abs'-weak K = refl
abs'-weak S = refl
abs'-weak (var i) = refl
abs'-weak {a} (app A B) rewrite abs'-weak {a} A | abs'-weak {a} B = refl

comm-bind-abs' : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} (A : a ∷ Γ ⊢ b) → abs' (bind (Mlift σ) A) ≡ Abs-bind σ (abs' A)
comm-bind-abs' σ I = refl
comm-bind-abs' σ K = refl
comm-bind-abs' σ S = refl
comm-bind-abs' σ (var here) = refl
comm-bind-abs' σ (var (there i)) = abs'-weak (σ i)
comm-bind-abs' σ (app A B) with comm-bind-abs' σ A | comm-bind-abs' σ B
... | prfA | prfB with abs' A
... | Abs-I rewrite prfA | prfB = refl
... | Abs-S _ _ rewrite prfA | prfB = refl
... | Abs-K A' rewrite prfA with abs' B
... | Abs-I rewrite prfB = refl
... | Abs-S _ _ rewrite prfB = refl
... | Abs-K B' rewrite prfB = refl

comm-bind-abs : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} (A : a ∷ Γ ⊢ b) → abs (bind (Mlift σ) A) ≡ bind σ (abs A)
comm-bind-abs σ A = trans (cong abs-to-term (comm-bind-abs' σ A)) (Abs-bind-lemma σ (abs' A))

⟦⟧-weak : ∀ {Γ a b} (B : Γ ⊢ a) (A : Γ ⊢ b) → A ≡ weak A ⟦ B ⟧
⟦⟧-weak t I = refl
⟦⟧-weak t K = refl
⟦⟧-weak t S = refl
⟦⟧-weak t (var i) = refl
⟦⟧-weak t (app A A₁) = cong₂ app (⟦⟧-weak t A) (⟦⟧-weak t A₁)

