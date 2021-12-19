module VectorNat where
open import Data.Vec hiding (init)
open import Data.Nat as Nat hiding (_<_;_≤_) 
open import Data.Nat.Properties as NatProp
open import Data.Fin  hiding (_≺_ ;_+_ ;_<_;_≤_;_≟_;pred;_≤?_)
open import Data.Bool hiding (_<_;_≤_;_≟_;_≤?_)
open import Data.Product using (_×_;∃-syntax;_,_;proj₁;proj₂)
open import Relation.Nullary using (¬_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_;_≢_;refl;inspect;[_];subst;sym;cong;cong₂)
open import Relation.Nullary using (Dec; _because_ ; ofⁿ; ofʸ;¬_ )


private
  variable
   a b c l : ℕ
   v v′ v″ : Vec ℕ l
   i i′ i″ : Fin l

data _≤_ : {l : ℕ } → (Vec ℕ l) → (Vec ℕ  l) →  Set where
    []≤[] : [] ≤ []
    ∷≤∷ : a Nat.≤ b → v ≤ v′ → (a ∷  v) ≤ ( b ∷  v′)

data _<_ : {l : ℕ } → (Vec ℕ l) → (Vec ℕ l) →  Set where
       t<t :  a Nat.≤ b → v < v′ → (a ∷ v) < ( b ∷ v′)
       h<h :  a Nat.< b  → v ≤ v′ → (a ∷ v) < ( b ∷ v′)


-- vector helper functions 
fillZero : (l : ℕ)  → Vec ℕ l 
fillZero zero = [] 
fillZero (suc m) =  0 ∷ (fillZero m)

incAt : Fin l →  Vec ℕ l → Vec ℕ l
incAt zero   (x ∷ xs)  = (suc x) ∷ xs
incAt (suc i) (x ∷ xs) = x ∷ (incAt i xs)

max : Vec ℕ  l → Vec ℕ l → Vec ℕ l 
max  (x ∷ xs)  (y ∷ ys)  with x ≤? y 
...                       | true because _  = y ∷ (max xs ys)
...                       | false because _   = x ∷ (max xs ys)
max [] [] = []


-- lemmas about _<_ and _≤_

v≤v : v ≤ v
v≤v {_} {[]} = []≤[]
v≤v {_} {(x ∷ xs)} = ∷≤∷ (≤-refl) v≤v


≤-transitive : v ≤ v′ → v′ ≤ v″  → v ≤ v″
≤-transitive ([]≤[]) ([]≤[]) = []≤[]
≤-transitive (∷≤∷ {a} {b} a≤b v≤v′) (∷≤∷ {b} {c} b≤c v′≤v″) =  ∷≤∷ (≤-trans  {a} {b} {c} a≤b  b≤c) (≤-transitive v≤v′ v′≤v″)

<→≤ : v < v′ → v ≤ v′
<→≤ (t<t x y) = ∷≤∷ x (<→≤  y)
<→≤ (h<h {a} {b}  x y) = ∷≤∷ (<⇒≤ {a} {b}  x) y

<-transitive : v < v′ → v′ < v″  → v < v″
<-transitive (t<t {a} {b} a≤b  v<v′) (t<t {b} {c} b≤c  v′<v″) = t<t ( ≤-trans {a} {b} {c} a≤b  b≤c ) ( <-transitive  v<v′ v′<v″)
<-transitive (t<t  {a} {b} a≤b  v<v′) (h<h  {b} {c}  b<c  v′≤v″) = h<h ( <-transʳ  {a} {b} {c}  a≤b  b<c ) (≤-transitive ( <→≤  v<v′)  v′≤v″)
<-transitive (h<h  {a} {b} a<b  v≤v′) (t<t {b} {c} b≤c  v′<v″) = h<h ( <-transˡ {a} {b} {c} a<b b≤c) (≤-transitive v≤v′ ( <→≤  v′<v″))
<-transitive (h<h  {a} {b} a<b  v≤v′) (h<h {b} {c} b<c  v′≤v″) = h<h (<-trans {a} {b} {c} a<b b<c) (≤-transitive v≤v′  v′≤v″)



≤,<→< : v ≤ v′ → v′ < v″  → v < v″
≤,<→< (∷≤∷ {a} {b} a≤b  v≤v′  ) (t<t {b} {c} b≤c  v′<v″) = t<t (≤-trans {a} {b} {c} a≤b  b≤c) ( ≤,<→< v≤v′ v′<v″)
≤,<→< (∷≤∷ {a} {b} a≤b  v≤v′) (h<h {b} {c} b<c  v′≤v″) = h<h (<-transʳ {a} {b} {c} a≤b b<c) ( ≤-transitive v≤v′ v′≤v″)

<→¬≤ :  v < v′ → ¬ v′ ≤ v 
<→¬≤ {v = x ∷ xs} {v′ = y ∷ ys}  (h<h x<y _) (∷≤∷ y≤x _ ) with () ← (≤⇒≯ {y}{x} y≤x) x<y 
<→¬≤ {v = x ∷ xs} {v′ = y ∷ ys}  (t<t _ xs<ys) (∷≤∷ _ ys≤xs ) = <→¬≤ xs<ys ys≤xs

<-asymmetric :  v < v′ → ¬ v′ < v 
<-asymmetric v<v′ v′<v =  <→¬≤ v′<v (<→≤ v<v′)


<→≢ : v < v′ → v ≢ v′
<→≢ {v = (a ∷ as)} {b ∷ bs} (t<t _ as<bs) = λ v≡v′ → (<→≢ as<bs )(cong tail v≡v′)
<→≢ {v = (a ∷ as)} {b ∷ bs} (h<h a<b _ ) = λ v≡v′ → <⇒≢ (a<b ) ( cong head v≡v′)
  where ≡→T : ∀ {b : Bool} → b ≡ true → T b
        ≡→T refl  =  tt


-- lemmas about fillZero

fillZero[l][i]≡0 :  lookup (fillZero l) i ≡ 0
fillZero[l][i]≡0 {suc l} {zero} = refl
fillZero[l][i]≡0 {suc l} {suc i} = fillZero[l][i]≡0 {l} {i}


--lemmas about incAt
v<incAt[i,v] : v < incAt i v
v<incAt[i,v] {_} {(x ∷ xs)} {zero} = h<h (n<1+n x) v≤v
v<incAt[i,v] {_} {(x ∷ xs)}{(suc n)} = t<t (≤-refl {x}) v<incAt[i,v]



-- lemmas about max

max-comm : max v v′ ≡ max v′ v
max-comm {v = []} {v′ = []} = refl
max-comm {v = x ∷ v} {v′ = y ∷ v′} 
    with x ≤? y | y ≤? x 
... | false because _ | true because _
      rewrite sym (max-comm {v = v} {v′ = v′}) = refl
... | true because ofʸ x≤y | true because ofʸ y≤x 
      rewrite ≤-antisym x≤y y≤x   
      rewrite sym (max-comm {v = v} {v′ = v′})
      = refl
... | true because _ | false because _   rewrite sym (max-comm {v = v} {v′ = v′}) = refl
... | false because ofⁿ x≰y  | false because ofⁿ y≰x 
     with () ← y≰x (<⇒≤ {y} {x} (≰⇒> {x} {y} x≰y ))
     

v≤max[v,v′] : v ≤ max v v′
v≤max[v,v′] {_} {[]} {[]} = []≤[]
v≤max[v,v′] {_} {x ∷ xs} {y ∷ ys}  with  x ≤? y 
...                                 | true because ofʸ x≤y   = ∷≤∷  x≤y  ( v≤max[v,v′] {v = xs } {v′ = ys})
...                                 | false because ofⁿ x≰y  = ∷≤∷ ( ≤-refl {x} ) (v≤max[v,v′] {v = xs } {v′ = ys})

v≤max[v′,v] : v ≤ max v′ v
v≤max[v′,v]  {v = v} {v′ = v′} rewrite sym (max-comm {v = v} {v′}) = v≤max[v,v′] {v = v} {v′ = v′}

-- lemmas about lookup
1+v[i]≡incAt[i,v][i] : 1 + (lookup v i)  ≡ (lookup (incAt i v ) i)
1+v[i]≡incAt[i,v][i] {v = v@(x ∷ xs) } {zero} with lookup v zero 
... | zero   = refl
... | suc x  =  refl
1+v[i]≡incAt[i,v][i] {v = v@(x ∷ xs) } {suc i} = 1+v[i]≡incAt[i,v][i] {v = xs} {i}


v[i]<incAt[i,v][i] : (lookup v i)  Nat.< (lookup (incAt i v ) i)
v[i]<incAt[i,v][i] {v = v} {i}
  rewrite sym (1+v[i]≡incAt[i,v][i] {v = v} {i})
  = s≤s (≤-reflexive refl)

0<incAt[i,v][i] : 0  Nat.< (lookup (incAt i v ) i)
0<incAt[i,v][i] {i = zero} {x ∷ xs} = s≤s z≤n
0<incAt[i,v][i] {i = suc i} {x ∷ xs} = 0<incAt[i,v][i] {i = i} {xs}


i≢i′→incAt[i′,v][i]≡v[i] : i ≢ i′ →  lookup (incAt i′ v) i ≡ lookup v i
i≢i′→incAt[i′,v][i]≡v[i]{suc l} {zero} {zero} p≢q with () ←  p≢q refl
i≢i′→incAt[i′,v][i]≡v[i] {suc l} {zero} {suc i′} {x ∷ xs} _ = refl
i≢i′→incAt[i′,v][i]≡v[i] {suc l} {suc i} {zero}  {x ∷ xs} _ =  refl
i≢i′→incAt[i′,v][i]≡v[i] {suc l} {suc i} {suc i′} {x ∷ v} si≢si′ = i≢i′→incAt[i′,v][i]≡v[i] {l} {i} {i′}  (λ i≡i′ →  si≢si′  (cong suc i≡i′))



v≤v′→v[i]≤v′[i] : v ≤ v′ → lookup v i Nat.≤ lookup v′ i
v≤v′→v[i]≤v′[i] {v = x ∷ xs} {y ∷ ys} {zero} (∷≤∷ x≤y _ ) =   x≤y
v≤v′→v[i]≤v′[i] {v = x ∷ xs} {y ∷ ys} {suc i} (∷≤∷ _  xs≤ys ) =  v≤v′→v[i]≤v′[i] {v = xs} {ys} {i} xs≤ys

v[i]≤max[v,v′][i] : (lookup v i) Nat.≤ (lookup (max v v′) i)
v[i]≤max[v,v′][i] {v = v} { v′ = v′} = v≤v′→v[i]≤v′[i] (v≤max[v,v′] {v = v} {v′ = v′} )

v[i]≤max[v′,v][i] : (lookup v i) Nat.≤ (lookup (max v′ v) i)
v[i]≤max[v′,v][i] {v = v} {v′ = v′} rewrite sym (max-comm {v = v} {v′}) = v[i]≤max[v,v′][i] {v = v} {v′ = v′}

v[i]≤v′[i]→max[v,v′][i]≡v′[i] : lookup v i  Nat.≤ lookup v′ i →  lookup (max v v′ ) i ≡ lookup v′ i
v[i]≤v′[i]→max[v,v′][i]≡v′[i]  {v = x ∷ xs} {zero} {y ∷ ys } x≤y 
    with x ≤? y
... | true because _  = refl 
... | false because ofⁿ x≰y  with () ← x≰y x≤y  
v[i]≤v′[i]→max[v,v′][i]≡v′[i]   {v = x ∷ xs} {suc i}  {y ∷ ys } v[i]≤v′[i] 
    with x ≤? y
... | false because _ = v[i]≤v′[i]→max[v,v′][i]≡v′[i]  {v = xs} {i} {ys} v[i]≤v′[i]
... | true  because _ = v[i]≤v′[i]→max[v,v′][i]≡v′[i]  {v = xs} {i} {ys} v[i]≤v′[i]


v[i]≰v′[i]→max[v,v′][i]≡v[i] : lookup v i  ≰ lookup v′ i →  lookup (max v v′ ) i ≡ lookup v i
v[i]≰v′[i]→max[v,v′][i]≡v[i]  {v = x ∷ xs} {zero} {y ∷ ys } x≰y 
    with x ≤? y
... | false because _  = refl 
... | true because ofʸ x≤y  with () ← x≰y x≤y  
v[i]≰v′[i]→max[v,v′][i]≡v[i]  {v = x ∷ xs} {suc i}  {y ∷ ys } v[i]≰v′[i] 
    with x ≤? y
... | false because _ = v[i]≰v′[i]→max[v,v′][i]≡v[i]  {v = xs} {i} {ys} v[i]≰v′[i] 
... | true  because _ = v[i]≰v′[i]→max[v,v′][i]≡v[i]  {v = xs} {i} {ys} v[i]≰v′[i] 

