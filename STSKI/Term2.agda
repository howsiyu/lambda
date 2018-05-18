{-# OPTIONS --without-K #-}

module STSKI.Term2 (T : Set) where

open import STLC.Type T
open import Function using (_∘_; flip)
open import Data.Star using (Star; ε; _◅_; _◅◅_)
open import Data.Star.Properties
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

data Abs {Γ a} : ∀ {b} (A : a ∷ Γ ⊢ b) → Set where
  Abs-I : Abs (var here)
  Abs-K : ∀ {b A} (A' : Γ ⊢ b) → A ≡ weak A' → Abs A
  Abs-S : ∀ {b c} {A : _ ⊢ b ⇒ c} {B : _ ⊢ b} → Abs A → Abs B → Abs (app A B)

abs-to-term : ∀ {Γ a b} {t : a ∷ Γ ⊢ b} → Abs t → Γ ⊢ a ⇒ b
abs-to-term Abs-I = I
abs-to-term (Abs-K A _) = app K A
abs-to-term (Abs-S A B) = app (app S (abs-to-term A)) (abs-to-term B)

abs' : ∀ {Γ a b} → (A : a ∷ Γ ⊢ b) → Abs A
abs' I = Abs-K I refl
abs' K = Abs-K K refl
abs' S = Abs-K S refl
abs' (var here) = Abs-I
abs' (var (there i)) = Abs-K (var i) refl
abs' (app A B) with abs' A | abs' B
... | Abs-K A' eqA | Abs-K B' eqB = Abs-K (app A' B') (cong₂ app eqA eqB)
... | A' | B' = Abs-S A' B'

abs : ∀ {Γ a b} → a ∷ Γ ⊢ b → Γ ⊢ a ⇒ b
abs = abs-to-term ∘ abs'

comm-weak-map : ∀ {a Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {b} (A' : Γ₁ ⊢ b) → map (lift ρ) (weak {a} A') ≡ weak {a} (map ρ A')
comm-weak-map ρ I = refl
comm-weak-map ρ K = refl
comm-weak-map ρ S = refl
comm-weak-map ρ (var i) = refl
comm-weak-map ρ (app A' B') = cong₂ app (comm-weak-map ρ A') (comm-weak-map ρ B')

Abs-map : ∀ {Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {a b} {A : a ∷ Γ₁ ⊢ b} → Abs A → Abs (map (lift ρ) A)
Abs-map ρ Abs-I = Abs-I
Abs-map ρ (Abs-K A' eq) = Abs-K (map ρ A') (trans (cong (map (lift ρ)) eq) (comm-weak-map ρ A'))
Abs-map ρ (Abs-S A' B') = Abs-S (Abs-map ρ A') (Abs-map ρ B')

Abs-map-lemma : ∀ {Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {a b} {A : a ∷ Γ₁  ⊢ b} (A' : Abs A) → abs-to-term (Abs-map ρ A') ≡ map ρ (abs-to-term A')
Abs-map-lemma ρ Abs-I = refl
Abs-map-lemma ρ (Abs-K A' eq) = refl
Abs-map-lemma ρ (Abs-S A' B') = cong₂ app (cong (app S) (Abs-map-lemma ρ A')) (Abs-map-lemma ρ B')

cong₂-trans : ∀ {A1 A2 B : Set} (f : A1 → A2 → B) {x1 y1 z1} (eq11 : x1 ≡ y1) (eq12 : y1 ≡ z1) {x2 y2 z2} (eq21 : x2 ≡ y2) (eq22 : y2 ≡ z2) → cong₂ f (trans eq11 eq12) (trans eq21 eq22) ≡ trans (cong₂ f eq11 eq21) (cong₂ f eq12 eq22)
cong₂-trans f refl refl refl refl = refl

comm-map-abs' : ∀ {Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {a b} (A : a ∷ Γ₁ ⊢ b) → abs' (map (lift ρ) A) ≡ Abs-map ρ (abs' A)
comm-map-abs' ρ I = refl
comm-map-abs' ρ K = refl
comm-map-abs' ρ S = refl
comm-map-abs' ρ (var here) = refl
comm-map-abs' ρ (var (there i)) = refl
comm-map-abs' ρ (app A B) with comm-map-abs' ρ A | comm-map-abs' ρ B
... | prfA | prfB with abs' A
... | Abs-I = cong (Abs-S Abs-I) prfB
... | Abs-S _ _ rewrite prfA = cong (Abs-S _) prfB
... | Abs-K A' eqA with abs' B
... | Abs-I rewrite prfA = refl
... | Abs-S _ _ rewrite prfA | prfB = refl
... | Abs-K B' eqB rewrite prfA | prfB = cong (Abs-K (map ρ (app A' B'))) (trans lem1 (cong (flip trans (cong₂ app (comm-weak-map ρ A') (comm-weak-map ρ B'))) (lem2 eqA eqB)))
  where
  ρ' = lift ρ
  
  lem1 = cong₂-trans app (cong (map ρ') eqA) (comm-weak-map ρ A') (cong (map ρ') eqB) (comm-weak-map ρ B')

  lem2 : ∀ {A' B'} (eqA : A ≡ A') (eqB : B ≡ B') → cong₂ app (cong (map ρ') eqA) (cong (map ρ') eqB) ≡ cong (map (lift ρ)) (cong₂ app eqA eqB)
  lem2 refl refl = refl

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

Abs-bind : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} {A : a ∷ Γ  ⊢ b} → Abs A → Abs (bind (Mlift σ) A)
Abs-bind σ Abs-I = Abs-I
Abs-bind σ {a} (Abs-K A' eqA) = Abs-K (bind σ A') (trans (cong (bind (Mlift σ)) eqA) (comm-weak-bind σ A'))
Abs-bind σ (Abs-S A B) = Abs-S (Abs-bind σ A) (Abs-bind σ B)

Abs-bind-lemma : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} {A : a ∷ Γ  ⊢ b} (A' : Abs A) → abs-to-term (Abs-bind σ A') ≡ bind σ (abs-to-term A')
Abs-bind-lemma σ Abs-I = refl
Abs-bind-lemma σ (Abs-K A' eq) = refl
Abs-bind-lemma σ (Abs-S A' B') = cong₂ app (cong (app S) (Abs-bind-lemma σ A')) (Abs-bind-lemma σ B')

abs'-weak : ∀ {a Γ b} (A' : Γ ⊢ b) → abs' (weak {a} A') ≡ Abs-K A' refl
abs'-weak I = refl
abs'-weak K = refl
abs'-weak S = refl
abs'-weak (var i) = refl
abs'-weak {a} (app A B) with abs'-weak {a} A | abs'-weak {a} B
... | eqA | eqB rewrite eqA | eqB = refl


comm-bind-abs' : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} (A : a ∷ Γ ⊢ b) → abs' (bind (Mlift σ) A) ≡ Abs-bind σ (abs' A)
comm-bind-abs' σ I = refl
comm-bind-abs' σ K = refl
comm-bind-abs' σ S = refl
comm-bind-abs' σ (var here) = refl
comm-bind-abs' σ (var (there i)) = abs'-weak (σ i)
comm-bind-abs' σ (app A B) with comm-bind-abs' σ A | comm-bind-abs' σ B
... | prfA | prfB with abs' A
... | Abs-I = cong (Abs-S Abs-I) (comm-bind-abs' σ B)
... | Abs-S _ _ rewrite prfA = cong (Abs-S _) prfB
... | Abs-K A' eqA with abs' B
... | Abs-I rewrite prfA = refl
... | Abs-S _ _ rewrite prfA | prfB = refl
... | Abs-K B' eqB rewrite prfA | prfB = cong (Abs-K _) (trans lem1 (cong (flip trans (cong₂ app (comm-weak-bind σ A') (comm-weak-bind σ B'))) (lem2 eqA eqB)))
  where
  σ' = Mlift σ
  
  lem1 = cong₂-trans app (cong (bind σ') eqA) (comm-weak-bind σ A') (cong (bind σ') eqB) (comm-weak-bind σ B')

  lem2 : ∀ {A' B'} (eqA : A ≡ A') (eqB : B ≡ B') → cong₂ app (cong (bind σ') eqA) (cong (bind σ') eqB) ≡ cong (bind σ') (cong₂ app eqA eqB)
  lem2 refl refl = refl

comm-bind-abs : ∀ {Γ Δ} (σ : Γ ◁ Δ) {a b} (A : a ∷ Γ ⊢ b) → abs (bind (Mlift σ) A) ≡ bind σ (abs A)
comm-bind-abs σ A = trans (cong abs-to-term (comm-bind-abs' σ A)) (Abs-bind-lemma σ (abs' A))


⟦⟧-weak : ∀ {Γ a b} → (B : Γ ⊢ a) → (A : Γ ⊢ b) → A ≡ weak A ⟦ B ⟧
⟦⟧-weak t I = refl
⟦⟧-weak t K = refl
⟦⟧-weak t S = refl
⟦⟧-weak t (var i) = refl
⟦⟧-weak t (app A A₁) = cong₂ app (⟦⟧-weak t A) (⟦⟧-weak t A₁)
