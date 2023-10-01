open import Data.Rational renaming (_*_ to _*ℚ_ ; _+_ to _+ℚ_ ; _-_ to _-ℚ_ ; _÷_ to _÷ℚ'_ ;
                                    _≟_ to _≟ℚ_ ; 1/_ to invℚ)
open import Data.Rational.Properties renaming (<-cmp to <-cmpℚ)
open import Relation.Nullary
open import Data.Bool hiding (_<?_ ; _<_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; -[1+_])
open import Relation.Nullary.Decidable renaming (False to isFalse ; True to isTrue)
open import Relation.Unary renaming (Decidable to DecidableP)
open import Data.Nat.Base as ℕ hiding (_<_ ; _>_)
open import Data.Nat.Properties renaming (_≟_ to _≟ℕ_ ; _<?_ to _<ℕ?_)
open import Agda.Builtin.Unit
open import Relation.Binary.Definitions using (Trichotomous ; Tri ; tri< ; tri≈ ; tri> )
open import Function.Base
--open import Data.Integer
--open import Data.Nat




≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt


infixl 7 _÷ℚ_

_÷ℚ_ : (p q : ℚ) → {q≢0 : q ≢ 0ℚ} → ℚ
_÷ℚ_ p q {q≢0} = _÷ℚ'_ p q {n≢0 = ≢0⇒num≢0 q≢0}


--Define absolute Value of a rational Number

abs : ℚ → ℚ
abs x  with (<-cmpℚ 0ℚ x)
... | tri< _ _ _ = x
... | tri≈ _ _ _ = x
... | tri> _ _ _ = - x

-- -z ≡ 0  implies z ≡ 0
-z≡0⇒z≡0 : {z : ℚ} → - z ≡ 0ℚ → z ≡ 0ℚ
-z≡0⇒z≡0 {mkℚ (+_ zero) _ _} p = p

-- Kontraposition: z ≢ 0 implies -z ≢ 0
z≢0⇒-z≢0 : {z : ℚ} → z ≢ 0ℚ → - z ≢ 0ℚ
z≢0⇒-z≢0 p = λ -z≡0 → p (-z≡0⇒z≡0 -z≡0)

-- with z ≢ 0, also   abs z ≢ 0
z≢0⇒absz≢0  :  {z : ℚ} → z ≢ 0ℚ → abs z ≢ 0ℚ
z≢0⇒absz≢0 {z} z≢0 with (<-cmpℚ 0ℚ z)
... | tri< _ _ _ = z≢0
... | tri≈ _ _ _ = z≢0
... | tri> _ _ _ = z≢0⇒-z≢0 z≢0


-- whenever z ≢ 0,  abs z > 0
z<0⇒-z>0 : {z : ℚ} → z < 0ℚ → - z > 0ℚ
z<0⇒-z>0 p = neg-antimono-< p

abs>0 : {z : ℚ} → z ≢ 0ℚ → abs z > 0ℚ
abs>0 {z} z≢0 with (<-cmpℚ 0ℚ z)
... | tri< a _   _   = a
... | tri≈ _ 0≡z _   = ⊥-elim (z≢0 (sym 0≡z))
... | tri> _ _   z<0 = z<0⇒-z>0 z<0


-- whenever z ≢ 0,  1 / abs z  > 0
invabs>0 : {z : ℚ} → (z≢0 : z ≢ 0ℚ) → invℚ (abs z) > 0ℚ
invabs>0 {z} z≢0 = positive⁻¹ (pos⇒1/pos (abs z) (positive (abs>0 z≢0)))


-- z > 0 implies z ≢ 0
z>0⇒z≢0 : {z : ℚ} → z > 0ℚ → z ≢ 0ℚ
z>0⇒z≢0 {z} p with (<-cmpℚ 0ℚ z)
... | tri< _ ¬b _ = ¬b ∘ sym
... | tri≈ ¬a _ _ = ⊥-elim (¬a p)
... | tri> ¬a _ _ = ⊥-elim (¬a p)

-- z < 0 implies z ≢ 0
z<0⇒z≢0 : {z : ℚ} → z < 0ℚ → z ≢ 0ℚ
z<0⇒z≢0 {z} p with (<-cmpℚ 0ℚ z)
... | tri< _ _ ¬c = ⊥-elim (¬c p)
... | tri≈ _ _ ¬c = ⊥-elim (¬c p)
... | tri> _ ¬b _ = ¬b ∘ sym


-- this is a mess... we should use our _÷ℚ_ and show that 1 ÷ℚ z  is a multipl. inverse of z...

-- when z > 0, (1/ abs z) * z ≡ 1  -- z≢0⇒absz≢0 (z>0⇒z≢0 z>0)
z>0=⇒1 : {z : ℚ} → (z>0 : z > 0ℚ) → (invℚ (abs z) {≢0⇒num≢0(z≢0⇒absz≢0 (z>0⇒z≢0 z>0))}) *ℚ z ≡ 1ℚ -- ) ≡ 1ℚ
z>0=⇒1 {z} z>0 with (<-cmpℚ 0ℚ z)
... | tri< _ _ _ =  {!!}
{-
  (_÷ℚ_ 1ℚ z {z>0⇒z≢0 z>0} ) *ℚ z
    ≡⟨ {!!} ⟩
  1ℚ
    ∎   where open ≡-Reasoning
    -}
... | tri≈ ¬z>0 _ _ = ⊥-elim (¬z>0 z>0)
... | tri> ¬z>0 _ _ = ⊥-elim (¬z>0 z>0)

-- when z < 0, (1/ abs z) * z ≡ - 1
