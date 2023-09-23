open import Data.Rational renaming (_*_ to _*ℚ_ ; _+_ to _+ℚ_ ; _-_ to _-ℚ_ ; _÷_ to _÷ℚ'_ ;
                                    _≟_ to _≟ℚ_)
open import Data.Rational.Properties renaming (<-cmp to <-cmpℚ)
open import Relation.Nullary
open import Data.Bool hiding (_<?_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Integer.Base as ℤ using (ℤ; +_; +0; -[1+_])
open import Relation.Nullary.Decidable renaming (False to isFalse ; True to isTrue)
open import Relation.Unary renaming (Decidable to DecidableP)
open import Data.Nat.Base as ℕ
open import Data.Nat.Properties renaming (_≟_ to _≟ℕ_ ; _<?_ to _<ℕ?_)
open import Agda.Builtin.Unit
open import Relation.Binary.Definitions using (Trichotomous ; Tri ; tri< ; tri≈ ; tri> )
--open import Data.Integer
--open import Data.Nat






infixl 7 _÷ℚ_

_÷ℚ_ : (p q : ℚ) → {q≢0 : q ≢ 0ℚ} → ℚ
_÷ℚ_ p q {q≢0} = _÷ℚ'_ p q {n≢0 = ≢0⇒num≢0 q≢0}  where
  ≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
  ≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
  ≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
  ≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt


--Define absolute Value of a rational Number

abs : ℚ → ℚ
abs x  with (x <? 0ℚ)
... | no _ = x
... | yes  _ = - x


-- Proof that

-z≡0⇒z≡0 : {z : ℚ} → - z ≡ 0ℚ → z ≡ 0ℚ
-z≡0⇒z≡0 {mkℚ (+_ zero) _ _} p = p

z≢0⇒-z≢0 : {z : ℚ} → z ≢ 0ℚ → - z ≢ 0ℚ
z≢0⇒-z≢0 p = λ -z≡0 → p (-z≡0⇒z≡0 -z≡0)

z≢0⇒absz≢0  :  {z : ℚ} → z ≢ 0ℚ → abs z  ≢ 0ℚ
z≢0⇒absz≢0 {z} z≢0 with ( z <? 0ℚ)
... | no _ = z≢0
... | yes _ = z≢0⇒-z≢0 z≢0


