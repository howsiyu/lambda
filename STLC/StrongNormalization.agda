module STLC.StrongNormalization (T : Set)  where

open import STLC.Type T
open import STLC.Term T
open import STLC.Beta T
open import Data.Star using (ε; _◅_)
open import Induction.WellFounded
open import Function using (id; _∘_)
open import Relation.Binary using (Rel)
open import Agda.Primitive using (lzero)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Unary using (_⊆′_; _∩_) renaming (_⇒_ to _⇒'_)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; inspect; [_]; cong; cong₂; subst)

strongly-normalizable : ∀ {Γ a} → Γ ⊢ a → Set
strongly-normalizable = Acc _β←_

reducible : ∀ {a Γ} → Γ ⊢ a → Set
reducible {base _} t = strongly-normalizable t
reducible {a ⇒ b} {Γ} t = ∀ {Δ} (ρ : Γ ⊆ Δ) → reducible ⊆′ reducible ∘ app (map ρ t)

data neutral {Γ a} : Γ ⊢ a → Set where
  nvar : ∀ {i} → neutral (var i)
  napp : ∀ {b s} {t : Γ ⊢ b} → neutral (app s t)

app₁-strong : ∀ {Γ a b} (t : Γ ⊢ a)  {s : Γ ⊢ a ⇒ b} → strongly-normalizable (app s t) → strongly-normalizable s
app₁-strong t {s} (acc f) = acc (λ s' p → app₁-strong t {s'} (f (app s' t) (β-app₁ p)))

inv-map-strong : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) {a} {t : Γ ⊢ a} → strongly-normalizable (map ρ t) → strongly-normalizable t
inv-map-strong ρ (acc f) = acc (λ t' p → inv-map-strong ρ (f (map ρ t') (map-β ρ p)))

CR2 : ∀ a {Γ} → reducible {a} {Γ} ⊆′ WfRec _β←_ reducible
CR2 (base _) t (acc f) t' p = f t' p
CR2 (a ⇒ b) t red t' le ρ u ured = CR2 b (app (map ρ t) u) (red ρ u ured) (app (map ρ t') u) (β-app₁ (map-β ρ le))

mutual
  CR1 : ∀ a {Γ} → reducible {a} {Γ} ⊆′ strongly-normalizable
  CR1 (base _) _ red = red
  CR1 (a ⇒ b) t red = inv-map-strong there (app₁-strong (var here) (CR1 b (app (weak t) (var here)) (red there (var here) (CR3 a (var here) (nvar , λ _ ())))))

  CR3 : ∀ a {Γ} → neutral ∩ WfRec _β←_ reducible ⊆′ reducible {a} {Γ}
  CR3 (base _) = λ { t (_ , f) → acc f}
  CR3 (a ⇒ b) {Γ} t nf ρ u ured = Some.wfRec (reducible ⇒' reducible ∘ app (map ρ t))
    (λ u1 g u1red → CR3 b (app (map ρ t) u1) (napp , goal t nf ρ u1 g u1red))
    u (CR1 a u ured) ured
    where
    goal :  ∀ (t : Γ ⊢ a ⇒ b) → neutral t × WfRec _β←_ reducible t →  ∀ {Δ} (ρ : Γ ⊆ Δ) →
      ∀ u → WfRec _β←_ (reducible ⇒' reducible ∘ app (map ρ t)) u → reducible u
      → WfRec _β←_ reducible (app (map ρ t) u)
    goal (abs _) (() , f) ρ u g ured _ β-red
    goal t (_ , f) ρ u _ ured (app t' .u) (β-app₁ p) with inv-map-β ρ t t' p
    ... | t1' , eq , q rewrite eq = f t1' q ρ u ured
    goal t (_ , f) ρ u g ured (app .(map ρ t) u') (β-app₂ p) = g u' p (CR2 a u ured u' p)


CR2* : ∀ a {Γ} → reducible {a} {Γ} ⊆′ WfRec _*β←_ reducible
CR2* a t red .t ε = red
CR2* a t red t' (p ◅ ps) = CR2* a _ (CR2 a t red _ p) t' ps

module Product {A B : Set} (RelA : Rel A lzero) (RelB : Rel B lzero) where
  data _<_ : Rel (A × B) lzero where
    left  : ∀ {x₁ x₂ y} (x₁<x₂ : RelA x₁ x₂) → (x₁ , y) < (x₂ , y)
    right : ∀ {x y₁ y₂} (y₁<y₂ : RelB y₁ y₂) → (x , y₁) < (x , y₂)

  mutual
    accessible : ∀ {x y} → Acc RelA x → Acc RelB y → Acc _<_ (x , y)
    accessible accA accB = acc (accessible' accA accB)
    
    accessible' : ∀ {x y} → Acc RelA x → Acc RelB y → WfRec _<_ (Acc _<_) (x , y)
    accessible' (acc rsA) accB ._ (left  x′<x) = accessible (rsA _ x′<x) accB
    accessible' accA (acc rsB) ._ (right y′<y) = accessible accA (rsB _ y′<y)

  wellFounded : Well-founded RelA → Well-founded RelB → Well-founded _<_
  wellFounded wfA wfB (x , y) = accessible (wfA x) (wfB y)

abs-lemma : ∀ {a b Γ} (t : a ∷ Γ ⊢ b) → (∀ {Δ} (ρ : Γ ⊆ Δ) (u : Δ ⊢ a) → reducible u → reducible (map (lift ρ) t ⟦ u ⟧)) → reducible (abs t)
abs-lemma {a} {b} {Γ} t0 f0 {Δ} ρ = λ u0 u0red → Some.wfRec P step (t0 , u0) (accessible (CR1 b t0 t0red) (CR1 a u0 u0red)) (t0red , u0red , f0 ρ u0 u0red)
  where
  open Product {a ∷ Γ ⊢ b} {Δ ⊢ a} _β←_ _β←_
  
  P : a ∷ Γ ⊢ b × Δ ⊢ a → Set
  P (t , u) = reducible t × reducible u × reducible (map (lift ρ) t ⟦ u ⟧) → reducible (app (map ρ (abs t)) u)
  
  t0red : reducible t0
  t0red = subst reducible (sym (⟦⟧-here t0)) (f0 there (var here) (CR3 a (var here) (nvar , λ _ ())))

  goal : ∀ t u → WfRec _<_ P (t , u) → reducible t × reducible u × reducible (map (lift ρ) t ⟦ u ⟧) → WfRec _β←_ reducible (app (map ρ (abs t)) u)
  goal t u g (_ , _ , tured) .(map (lift ρ) t ⟦ u ⟧) β-red = tured
  goal t u g (tred , ured , tured) (app (abs t2') .u) (β-app₁ (β-abs p)) =
    let
      t' , eq , q = inv-map-β (lift ρ) t t2' p
      t'red = CR2 b t tred t' q
      t'u = map (lift ρ) t' ⟦ u ⟧
      t'ured = CR2* b _ tured t'u (→βP⊂→β* (⟦⟧-βP (map-βP (lift ρ) (→β⊂→βP q)) βP-refl))
      ans = g (t' , u) (left q) (t'red , ured , t'ured)
    in subst (λ x → reducible (app (abs x) u)) (sym eq) ans
  goal t u g (tred , ured , tured) (app .(map ρ (abs t)) u') (β-app₂ p) =
    let
      u'red = CR2 a u ured u' p
      tu' = map (lift ρ) t ⟦ u' ⟧
      tu'red = CR2* b _ tured tu' (→βP⊂→β* (⟦⟧-βP (βP-refl {t = map (lift ρ) t}) (→β⊂→βP p)))
    in g (t , u') (right p) (tred , u'red , tu'red)
  
  step : WfRec _<_ P ⊆′ P
  step (t , u) g reds = CR3 b (app (map ρ (abs t)) u) (napp , goal t u g reds)

map-strong : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) {a} {t : Γ ⊢ a} → strongly-normalizable t → strongly-normalizable (map ρ t)
map-strong ρ {t = t} (acc f) = acc (λ t2' p →
  let
    t' , eq , q = inv-map-β ρ t _ p
  in subst strongly-normalizable (sym eq) (map-strong ρ (f t' q)))

map-reducible : ∀ {Γ Δ} (ρ : Γ ⊆ Δ) → ∀ {a} (t : Γ ⊢ a) → reducible t → reducible (map ρ t)
map-reducible ρ {base _} t red = map-strong ρ red
map-reducible ρ {a ⇒ b} t red ρ' u ured rewrite sym (map-comp ρ' ρ t) = red (ρ' ∘ ρ) u ured

bind-reducible : ∀ {Γ Δ} (σ : Γ ◁ Δ) → (∀ {a} (i : Γ ∋ a) → reducible (σ i)) →  (∀ {a} (t : Γ ⊢ a) → reducible (bind σ t))
bind-reducible σ reds (var i) = reds i
bind-reducible σ reds (app s t) =
  let ans = (bind-reducible σ reds s) id (bind σ t) (bind-reducible σ reds t)
  in subst (λ x → reducible (app x (bind σ t))) (sym (map-id (bind σ s))) ans
bind-reducible {Γ} {Δ₁} σ reds {a ⇒ b} (abs t) = abs-lemma (bind (Mlift σ) t) f
  where
  f : ∀ {Δ₂} (ρ : Δ₁ ⊆ Δ₂) (u : Δ₂ ⊢ a) → reducible u → reducible (map (lift ρ) (bind (Mlift σ) t) ⟦ u ⟧)
  f ρ u ured rewrite trans (map-bind (lift ρ) (Mlift σ) t) (sym (bind-ext (distrib-lift2 ρ σ) t))
    = subst reducible (bind-comp (Msub u) (Mlift (map ρ ∘ σ)) t) (bind-reducible (Msub u <=< Mlift (map ρ ∘ σ)) goal t)
    where
    goal : ∀ {b} (i : (a ∷ Γ) ∋ b) → reducible ((Msub u <=< Mlift (map ρ ∘ σ)) i)
    goal here = ured
    goal (there i) rewrite sym (⟦⟧-weak u (map ρ (σ i))) = map-reducible ρ (σ i) (reds i)
    
all-reducible : ∀ {Γ} {a} (t : Γ ⊢ a) → reducible t
all-reducible t rewrite bind-id t = bind-reducible id◅ (λ {a} i → CR3 a (var i) (nvar , λ _ ())) t

-- aka strong normalization theorem
β←-wf : ∀ {Γ a} → Well-founded (_β←_ {Γ} {a})
β←-wf {Γ} {a} t = CR1 a t (all-reducible t)
