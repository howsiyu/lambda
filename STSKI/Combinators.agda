module STSKI.Combinators (T : Set) where

open import STLC.Type T
open import STLC.Term T
open import STLC.Beta T
open import Data.Star using (ε; _◅_; _◅◅_)
open import Data.Star.Properties
open import Relation.Binary.PropositionalEquality
open import Function using (flip; _∘_)

𝒊 : ∀ {Γ a} → Γ ⊢ a ⇒ a
𝒊 = abs (var here)

𝒌 : ∀ {Γ a b} → Γ ⊢ a ⇒ (b ⇒ a)
𝒌 = abs (abs (var (there here)))

𝒔 : ∀ {Γ a b c} → Γ ⊢ (a ⇒ (b ⇒ c)) ⇒ ((a ⇒ b) ⇒ (a ⇒ c))
𝒔 = abs (abs (abs (app (app (var (there (there here))) (var here)) (app (var (there here)) (var here)))))

𝒊-red : ∀ {Γ a t} → app (𝒊 {Γ} {a}) t →β* t
𝒊-red = β-red ◅ ε

𝒌-red : ∀ {Γ a b s t} → app (app (𝒌 {Γ} {a} {b}) s) t →β* s
𝒌-red {s = s} {t = t} = β-app₁ β-red ◅ β-red ◅ β*-reflexive (sym (⟦⟧-weak t s))

app-weak : ∀ {Γ a b} (t : a ∷ Γ ⊢ b) → app (weak (abs t)) (var here) →β t
app-weak t = subst (_→β_ _) (sym (⟦⟧-here t)) β-red

𝒔-red2 : ∀ {Γ a b c s t} → app (app (𝒔 {Γ} {a} {b} {c}) s) t →β* abs (app (app (weak s) (var here)) (app (weak t) (var here)))
𝒔-red2 {s = s} {t = t} = let open StarReasoning (_→β_) in
  begin
    app (app 𝒔 s) t
      ⟶⟨ β-app₁ β-red ⟩
    app (abs (abs (app (app (weak (weak s)) (var here)) (app (var (there here)) (var here))))) t
      ⟶⟨ β-red ⟩
    abs (app (app (bind (Mlift (Msub t)) (weak (weak s))) (var here)) (app (weak t) (var here)))
      ≡⟨ cong abs (cong (flip app (app (weak t) (var here)) ∘ flip app (var here)) (sym (trans (cong weak (⟦⟧-weak t s)) (comm-weak-bind (Msub t) (weak s))))) ⟩
    abs (app (app (weak s) (var here)) (app (weak t) (var here)))
  ∎
  
𝒔-red' : ∀ {Γ a b c s t} → app (app (𝒔 {Γ} {a} {b} {c}) (abs s)) (abs t) →β* abs (app s t)
𝒔-red' {s = s} {t = t} = 𝒔-red2 ◅◅ β*-abs (β*-app (app-weak s ◅ ε) (app-weak t ◅ ε))

𝒔-red : ∀ {Γ a b c s t u} → app (app (app (𝒔 {Γ} {a} {b} {c}) s) t) u →β* app (app s u) (app t u)
𝒔-red {s = s} {t = t} {u = u} = let open StarReasoning (_→β_) in
  begin
    app (app (app 𝒔 s) t) u
      ⟶⋆⟨ β*-app₁ 𝒔-red2 ⟩
    app (abs (app (app (weak s) (var here)) (app (weak t) (var here)))) u
      ⟶⟨ β-red ⟩
    app (app (weak s ⟦ u ⟧) u) (app (weak t ⟦ u ⟧) u)
      ≡⟨ cong₂ app (cong (flip app u) (sym (⟦⟧-weak u s))) (cong (flip app u) (sym (⟦⟧-weak u t))) ⟩
    app (app s u) (app t u)
  ∎

𝒌-red' : ∀ {Γ a b t} → app (𝒌 {Γ} {a} {b}) t →β* abs (weak t)
𝒌-red' = β-red ◅ ε

𝒔𝒌-red : ∀ {Γ a b c t} → app (𝒔 {Γ} {a} {b} {c}) (app 𝒌 t) →β* app 𝒔 (abs (weak t))
𝒔𝒌-red = β*-app₂ 𝒌-red'

I-ext-lemma : ∀ {Γ a} → app (app 𝒔 (app 𝒌 𝒊)) 𝒊 →β* 𝒊 {Γ} {a}
I-ext-lemma = β*-app₁ 𝒔𝒌-red ◅◅ 𝒔-red' ◅◅ β*-abs (app-weak (var here) ◅ ε)

K-ext-lemma : ∀ {Γ a b} →
  app (app 𝒔
    (app (app 𝒔 (app 𝒌 𝒔))
      (app (app 𝒔 (app 𝒌 𝒌))
        (app (app 𝒔 (app 𝒌 𝒌)) 𝒊))))
    (app 𝒌 𝒊) →β* 𝒌 {Γ} {a} {b}
K-ext-lemma = (β*-app (β*-app₂ (β*-app 𝒔𝒌-red (β*-app 𝒔𝒌-red (β*-app₁ 𝒔𝒌-red ◅◅ 𝒔-red' ◅◅ β*-abs 𝒌-red') ◅◅ 𝒔-red' ◅◅ β*-abs 𝒌-red') ◅◅ 𝒔-red')) 𝒌-red') ◅◅ 𝒔-red' ◅◅ β*-abs (𝒔-red' ◅◅ β*-abs (β-red ◅ ε))

S-ext-lemma : ∀ {Γ a b c} →
  (app (app 𝒔
    (app (app 𝒔 (app 𝒌 𝒔))
      (app (app 𝒔 (app 𝒌 (app 𝒔 (app 𝒌 𝒔))))
        (app (app 𝒔 (app 𝒌 (app 𝒔 (app 𝒌 𝒌))))
          (app (app 𝒔
            (app (app 𝒔 (app 𝒌 𝒔))
              (app (app 𝒔 (app 𝒌 𝒌))
                (app (app 𝒔 (app 𝒌 𝒔)) 𝒊))))
            (app 𝒌 𝒊))))))
    (app 𝒌 (app 𝒌 𝒊)))
  →β* 𝒔 {Γ} {a} {b} {c}
S-ext-lemma = β*-app (β*-app₂ (β*-app 𝒔𝒌-red (β*-app (β*-app₂ (β*-app₂ 𝒔𝒌-red ◅◅ 𝒌-red')) (β*-app (β*-app₂ (β*-app₂ 𝒔𝒌-red ◅◅ 𝒌-red')) (β*-app (β*-app₂ (β*-app 𝒔𝒌-red (β*-app 𝒔𝒌-red (β*-app₁ 𝒔𝒌-red ◅◅ 𝒔-red') ◅◅ 𝒔-red' ◅◅ β*-abs 𝒌-red') ◅◅ 𝒔-red')) 𝒌-red' ◅◅ 𝒔-red' ◅◅ β*-abs 𝒔-red') ◅◅ 𝒔-red' ◅◅ β*-abs (𝒔-red' ◅◅ β*-abs 𝒌-red')) ◅◅ 𝒔-red' ◅◅ β*-abs 𝒔-red') ◅◅ 𝒔-red')) (β*-app₂ 𝒌-red' ◅◅ 𝒌-red') ◅◅ 𝒔-red' ◅◅ β*-abs (𝒔-red' ◅◅ β*-abs 𝒔-red' ◅◅ β*-abs (β*-abs 𝒔-red))
