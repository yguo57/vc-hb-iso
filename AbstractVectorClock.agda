module AbstractVectorClock (Pid : Set) where

open import Event Pid
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

private
  variable
    p q r : Pid

data VC : Pid → Set where
  init  : VC p

  tick  : VC p
        → VC p

  merge : VC q
        → VC p
        → VC p

private
  variable
    vc  : VC p
    vc′ : VC q
    vc″ : VC r

data _<_ : VC p → VC q → Set where
  vc<tick[vc]      : vc < tick vc
  vc<merge[vc,vc′] : vc < merge vc  vc′
  vc<merge[vc′,vc] : vc < merge vc′ vc
  transitive       : vc < vc′ → vc′ < vc″ → vc < vc″

private
  variable
    e   : Event p
    e′  : Event q

vc[_] : Event p → VC p
vc[ init ]         = init
vc[ send e ]       = tick vc[ e ]
vc[ receive e′ e ] = merge vc[ e′ ] vc[ e ]

event[_] : VC p → Event p
event[ init ]         = init
event[ tick vc ]      = send event[ vc ]
event[ merge vc vc₁ ] = receive event[ vc ] event[ vc₁ ]

event∘vc : ∀ (e : Event p) → event[ vc[ e ] ] ≡ e
event∘vc init = refl
event∘vc (send e) rewrite event∘vc e = refl
event∘vc (receive e e₁) rewrite event∘vc e | event∘vc e₁ = refl

≺→< : e ≺ e′ → vc[ e ] < vc[ e′ ]
≺→< processOrder₁     = vc<tick[vc]
≺→< processOrder₂     = vc<merge[vc′,vc]
≺→< sendBeforeReceive = vc<merge[vc,vc′]
≺→< (trans x y)       = transitive (≺→< x) (≺→< y)

<→≺ : vc[ e ] < vc[ e′ ] → e ≺ e′
<→≺ {e = e} {e′ = e′} x = subst (_≺ e′) (event∘vc e) (subst (event[ vc[ e ] ] ≺_) (event∘vc e′) (foo x))
  where
    foo : vc < vc′ → event[ vc ] ≺ event[ vc′ ]
    foo vc<tick[vc] = processOrder₁
    foo vc<merge[vc,vc′] = sendBeforeReceive
    foo vc<merge[vc′,vc] = processOrder₂
    foo (transitive x x₁) = trans (foo x) (foo x₁)
