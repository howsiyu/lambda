module STSKI.STLC (T : Set) where

open import STLC.Type T
open import STSKI.Term T
import STLC.Term T as Lam
open import STLC.Beta T
open import STSKI.Combinators T
open import Function using (_∘_; flip)
open import Data.Star using (ε; _◅_; _◅◅_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; inspect; [_])

ski-map : ∀ {Γ a} → Γ Lam.⊢ a → Γ ⊢ a
ski-map (Lam.var i) = var i
ski-map (Lam.app s t) = app (ski-map s) (ski-map t)
ski-map (Lam.abs t) = abs (ski-map t)
 
lam-map : ∀ {Γ a} → Γ ⊢ a → Γ Lam.⊢ a
lam-map I = 𝒊
lam-map K = 𝒌
lam-map S = 𝒔
lam-map (var i) = Lam.var i
lam-map (app A B) = Lam.app (lam-map A) (lam-map B)

comm-map-lam : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) {a} (A : Γ ⊢ a) → lam-map (map ρ A) ≡ Lam.map ρ (lam-map A)
comm-map-lam ρ I = refl
comm-map-lam ρ K = refl
comm-map-lam ρ S = refl
comm-map-lam ρ (var i) = refl
comm-map-lam ρ (app A A₁) = cong₂ Lam.app (comm-map-lam ρ A) (comm-map-lam ρ A₁)

comm-weak-lam : ∀ {a Γ b} (A : Γ ⊢ b) → lam-map (weak {a} A) ≡ Lam.weak {a} (lam-map A)
comm-weak-lam = comm-map-lam there

comm-lam-abs : ∀ {Γ a b} (A : a ∷ Γ ⊢ b) → lam-map (abs A) →β* Lam.abs (lam-map A)
comm-lam-abs I = β-red ◅ ε
comm-lam-abs K = β-red ◅ ε
comm-lam-abs S = β-red ◅ ε
comm-lam-abs (var here) = ε
comm-lam-abs (var (there i)) = β-red ◅ ε
comm-lam-abs {a = a} (app A B) with comm-lam-abs A | comm-lam-abs B
... | prfA | prfB with abs' A | inspect abs' A
... | Abs-I | [ _ ] = β*-app (β*-app₂ prfA) prfB ◅◅ 𝒔-red'
... | Abs-S _ _ | [ eqA ] rewrite sym (cong (lam-map ∘ abs-to-term) eqA) = β*-app (β*-app₂ prfA) prfB ◅◅ 𝒔-red'
... | Abs-K A' | [ eqA ] rewrite comm-weak-lam {a} A' with abs' B | inspect abs' B 
... | Abs-I | [ _ ]  = β*-app (β*-app₂ prfA) prfB ◅◅ 𝒔-red'
... | Abs-S _ _ | [ eqB ] rewrite sym (cong (lam-map ∘ abs-to-term) eqB) = β*-app (β*-app₂ prfA) prfB  ◅◅ 𝒔-red'
... | Abs-K B' | [ eqB ] rewrite comm-weak-lam {a} B' = β-red ◅ β*-reflexive (cong Lam.abs (cong₂ Lam.app (sym (trans (cong lam-map (Abs-K-lemma A eqA)) (comm-weak-lam A'))) (sym (trans (cong lam-map (Abs-K-lemma B eqB)) (comm-weak-lam B')))))

id-lam-ski : ∀ {Γ a} (t : Γ Lam.⊢ a) → lam-map (ski-map t) →β* t
id-lam-ski (Lam.var i) = ε
id-lam-ski (Lam.app s t) = β*-app (id-lam-ski s) (id-lam-ski t)
id-lam-ski (Lam.abs t) = comm-lam-abs (ski-map t) ◅◅ β*-abs (id-lam-ski t)

comm-ski-map : ∀ {Γ₁ Γ₂} (ρ : Γ₁ ⊆ Γ₂) {b} (t : Γ₁ Lam.⊢ b) → ski-map (Lam.map ρ t) ≡ map ρ (ski-map t)
comm-ski-map ρ (Lam.var i) = refl
comm-ski-map ρ (Lam.app s t) = cong₂ app (comm-ski-map ρ s) (comm-ski-map ρ t)
comm-ski-map ρ (Lam.abs t) = trans (cong abs (comm-ski-map (lift ρ) t)) (comm-map-abs ρ (ski-map t))

comm-ski-weak : ∀ {a Γ b} (t : Γ Lam.⊢ b) → ski-map (Lam.weak {a} t) ≡ weak {a} (ski-map t)
comm-ski-weak = comm-ski-map there

ski-map◅ : ∀ {Γ Δ} → Γ Lam.◁ Δ → Γ ◁ Δ
ski-map◅ σ i = ski-map (σ i)

comm-ski-map◅-Mlift : ∀ {a Γ Δ} (σ : Γ Lam.◁ Δ) → ski-map◅ (Lam.Mlift {a} σ) ≡◅ Mlift {a} (ski-map◅ σ)
comm-ski-map◅-Mlift σ here = refl
comm-ski-map◅-Mlift σ (there i) = comm-ski-weak (σ i)

distrib-ski-bind : ∀ {Γ Δ} (σ : Γ Lam.◁ Δ) {a} (t : Γ Lam.⊢ a) → ski-map (Lam.bind σ t) ≡ bind (ski-map◅ σ) (ski-map t)
distrib-ski-bind σ (Lam.var i) = refl
distrib-ski-bind σ (Lam.app s t) = cong₂ app (distrib-ski-bind σ s) (distrib-ski-bind σ t)
distrib-ski-bind σ (Lam.abs t) = trans (cong abs (trans (distrib-ski-bind (Lam.Mlift σ) t) (bind-ext (comm-ski-map◅-Mlift σ) (ski-map t)))) (comm-bind-abs (ski-map◅ σ) (ski-map t))

comm-ski-Msub : ∀ {a Γ} (t : Γ Lam.⊢ a) → ski-map ∘ (Lam.Msub t) ≡◅ Msub (ski-map t)
comm-ski-Msub t here = refl
comm-ski-Msub t (there i) = refl

distrib-ski-⟦⟧ : ∀ {Γ a b} (s : a ∷ Γ Lam.⊢ b) t → ski-map (s Lam.⟦ t ⟧) ≡ ski-map s ⟦ ski-map t ⟧
distrib-ski-⟦⟧ s t = trans (distrib-ski-bind (Lam.Msub t) s) (bind-ext (comm-ski-Msub t) (ski-map s))
