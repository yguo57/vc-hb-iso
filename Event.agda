module Event (Pid : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-stepsˡ; ≤-stepsʳ; ≤-trans; <⇒≤; 1+n≰n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

private
  variable
    p q r : Pid

data Event : Pid → Set where
  init    : Event p

  send    : Event p
          → Event p

  receive : Event q
          → Event p
          → Event p

private
  variable
    e  : Event p
    e′ : Event q
    e″ : Event r

data _≺_ : Event p → Event q → Set where
  processOrder₁     : e ≺ send e
  processOrder₂     : e ≺ receive e′ e
  sendBeforeReceive : e ≺ receive e e′
  trans             : e ≺ e′ → e′ ≺ e″ → e ≺ e″

size : Event p → ℕ
size init           = zero
size (send e)       = suc (size e)
size (receive e e′) = suc (size e + size e′)

hb-monotonic : e ≺ e′ → size e < size e′
hb-monotonic processOrder₁     = s≤s ≤-refl
hb-monotonic processOrder₂     = s≤s (≤-stepsˡ _ ≤-refl)
hb-monotonic sendBeforeReceive = s≤s (≤-stepsʳ _ ≤-refl)
hb-monotonic (trans x y)       = ≤-trans (hb-monotonic x) (<⇒≤ (hb-monotonic y))

-----------------------------------
-- _≺_ is a strict partial order --
-----------------------------------

≺-irreflexive : ¬ e ≺ e
≺-irreflexive x = 1+n≰n (hb-monotonic x)

≺-transitive : e ≺ e′ → e′ ≺ e″ → e ≺ e″
≺-transitive = trans

≺-asymmetric : e ≺ e′ → ¬ e′ ≺ e
≺-asymmetric x y = ⊥-elim (≺-irreflexive (≺-transitive x y))

≺-antisymmetric : e ≺ e′ → e′ ≺ e → e ≡ e′
≺-antisymmetric x y = ⊥-elim (≺-irreflexive (≺-transitive x y))
