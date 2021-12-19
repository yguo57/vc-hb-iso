open import Data.Nat hiding (_<_;_≤_)
open import ConcreteVectorClock 2
open import Data.Fin hiding (_<_;_≤_)
open import Relation.Binary.PropositionalEquality using (_≡_;refl;_≢_)
open import VectorNat hiding (_<_;_≤_)
open import Data.Empty
open import Data.Product
open import Relation.Nullary using (¬_)
open import AbstractVectorClock Pid


-- D and E canno occur in the same execution

A : VC zero
A = init

B : VC (suc zero)
B = init


D : VC (suc zero)
D = tick B

E : VC (suc zero)
E = merge A B



¬vc<init : {p q : Pid} {vc : VC p } → ¬ vc < init {q}
¬vc<init  (transitive x y) = ¬vc<init y

vc≢init→¬vc<E : {p : Pid} {vc : VC p }  → vc ≢ init {p}→ (¬ vc < E) 
vc≢init→¬vc<E  vc≢init vc<merge[vc,vc′]  = vc≢init refl
vc≢init→¬vc<E  vc≢init vc<merge[vc′,vc] = vc≢init refl
vc≢init→¬vc<E  vc≢init (transitive {vc′ = init} x y) = ¬vc<init x
vc≢init→¬vc<E  vc≢init (transitive {vc′ = tick vc′} x y) = vc≢init→¬vc<E (λ ()) y
vc≢init→¬vc<E  lvc≢init (transitive {vc′ = merge vc′ vc′₁} x y) = vc≢init→¬vc<E (λ ()) y

¬D<E : ¬ D < E 
¬D<E (transitive {vc′ = init} x y ) = ¬vc<init x
¬D<E D<E@(transitive {vc′ = tick vc′ } _ _ ) = vc≢init→¬vc<E ((λ ())) D<E
¬D<E D<E@(transitive {vc′ = merge vc′ vc″} _ _ ) = vc≢init→¬vc<E ((λ ())) D<E

D<ᶜE : D <ᶜ E
D<ᶜE  = crt<crt (h<h (s≤s z≤n) (∷≤∷ (s≤s (s≤s z≤n)) (∷≤∷ z≤n []≤[])))


