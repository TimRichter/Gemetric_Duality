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

--open import Data.Integer
--open import Data.Nat






infixl 7 _÷ℚ_

_÷ℚ_ : (p q : ℚ) → {q≢0 : q ≢ 0ℚ} → ℚ
_÷ℚ_ p q {q≢0} = _÷ℚ'_ p q {n≢0 = ≢0⇒num≢0 q≢0}  where
  ≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
  ≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
  ≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
  ≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt




-- Viele der folgenden Funktionen und Datentypen sind outdated, da sie auf dreidimensionalen Punkten und nicht auf 2SP bassieren
-- Da einige von ihnen später eventuell noch nützlich sind, lass ich sie erst einmal bestehen

-- Define 3D representation of 2DPoints
data Point : Set where
  mkPoint :   ℚ  →  ℚ  →  ℚ   → Point

-- get X value from Point
getXValP : Point →   ℚ
getXValP (mkPoint x y z) = x

-- get Y value from Point
getYValP : Point →   ℚ
getYValP (mkPoint x y z) = y

-- get Z value from Point
getZValP : Point →   ℚ
getZValP (mkPoint x y z) = z


-- Define 2D Line (Idea: basically same structure as Points but verry different interpretation)
data Line : Set where
  _x+_y+1=0 :   ℚ  →  ℚ   → Line

-- Get a-value of Line
getAValL : Line → ℚ
getAValL (a x+ b y+1=0) = a

-- Get b-value of Line
getBValL : Line → ℚ
getBValL (a x+ b y+1=0) = b



---

data z≢0 : Point → Set where
  mkz≢0 : ∀ {x y z} → (z ≢ 0ℚ) → z≢0 (mkPoint x y z)

≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt


----dualPL : (p : Point) → z≢0 p → Line
----dualPL (mkPoint x y z) (mkz≢0 zNot0) =
----    let
----      num≢0 : isFalse ( ℤ.∣ ↥ z ∣ ≟ℕ 0)
----      num≢0 = ≢0⇒num≢0 zNot0
----    in
----      (_÷ℚ_  x z {n≢0 = num≢0}) x+  _÷ℚ_  y z {n≢0 = num≢0} y+1=0


testz≢0 : z≢0 (mkPoint  0ℚ  1ℚ  1ℚ)
testz≢0 = mkz≢0 λ ()
 

---



--Dual functions

--Point to Line
-- Tim: Cannot work like this. You need an additional argument of type z ≢ 0 
--dualPL : (p : Point) →  (z≢0 p) → Line
--dualPL (mkPoint a b z) ( mkz≢0 λ ()) = (a ÷ℚ z) x+ (b ÷ℚ z) y+1=0

--Line to Point
dualLP : Line  → Point
dualLP (a x+ b y+1=0) =  mkPoint a b (normalize 1 1)



-- Note: Construct Rationals with normalize m n
-- Results in mkℚ (+ m) n-1 _
-- or  mkℚ (Agda.Builtin.Int.Int.pos m) n-1 _  if I don't import integers and Naturals and only rationals
-- The n +1 likely because denominator can't be 0
-- There are a few constants like 0 which is just mkℚ + 0 0 _

-- Note: Division requires Proof that denominator is not zero
-- Good example for division:
-- _÷_ : (p q : ℚ) → .{n≢0 : ∣ ↥ q ∣ ≢0} → ℚ
-- (p ÷ q) {n≢0} = p * (1/ q) {n≢0}


-- Calculate Intersection Point between two Lines

-- Get X Value of Intersection Point
-- Problem1: How do you prove, that b1, b2 and (b1 * b2 * (a1 ÷ b2 - a1 ÷ b1)) are not 0?
-- Tim: You just cannot prove this! As of now, intersecXVal takes two arbitrary lines as arguments.
--      e.g. the lines (1 x+ 0 y+1=0) and (2 x+ 0 y+1=0) are perfectly fine arguments!
--      You have to require additional arguments that ensure
-- Problem2: Proof that these Lines have an intersection
--intersecXVal : Line  → Line  →  ℚ
--intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) = {!!} -- - (b1 - b2) ÷ ((b1 * b2) * ((a1 ÷ b2) - (a1 ÷ b1))) 

data b≢0 : Line → Set where
  mkb≢0 : ∀ {a b} → (b ≢ 0ℚ) → b≢0 ( a x+ b y+1=0 )

----intersecXVal : (l1 : Line) → (b≢0 l1)  → (l2 : Line) → (b≢0 l2)  →  ℚ
----intersecXVal (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0)  (mkb≢0 b2Not0) =
----    let
----      numb1≢0 : isFalse ( ℤ.∣ ↥ b1 ∣ ≟ℕ 0)
----      numb1≢0 = ≢0⇒num≢0 b1Not0
      
----      numb2≢0 : isFalse ( ℤ.∣ ↥ b2 ∣ ≟ℕ 0)
----      numb2≢0 = ≢0⇒num≢0 b2Not0
      
----   in
      --(b1 - b2) ÷ℚ ((b1 * b2) * ((a1 ÷ b2) - (a1 ÷ b1)))
----      _÷ℚ_ (b1 -ℚ b2) ((b1 *ℚ b2) *ℚ ((_÷ℚ_ a1 b2 {n≢0 = numb2≢0}) -ℚ ( _÷ℚ_ a1 b1 {n≢0 = numb1≢0})))  



--dualPL : (p : Point) → z≢0 p → Line
--dualPL (mkPoint x y z) (mkz≢0 zNot0) =
--    let
--      num≢0 : isFalse ( ℤ.∣ ↥ z ∣ ≟ℕ 0)
--      num≢0 = ≢0⇒num≢0 zNot0
--    in
--      (_÷ℚ_  x z {n≢0 = num≢0}) x+  _÷ℚ_  y z {n≢0 = num≢0} y+1=0

-- Idea to solve Problem1: Add a isNotZero function or Type:
-- data isNotZero : ℚ → Set  where
-- base : (a : ℚ) → isNotZero a


--  base : (a : ℚ) -> isNotZero a
--NonZero : Pred ℚ 0ℓ
--NonZero p = ℚᵘ.NonZero (toℚᵘ p)

--ℕ⁺ : Set
--ℕ⁺ = Σ ℕ (λ n → iszero n ≡ ff)

-- Idea to solve Problem2: Two Lines have no intersection Points, if they are parallel, which also means, that their dual Points have the same angle to the origin
-- Note: Equality in Rationals is already defined with the ≃ operator
--data haveIntersection : Line  → Line  →  Set where
--  base : {a1 b1 a2 b2 : ℚ} → haveIntersection  (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) --need additional constraint for a1,b1,a2,b2 {(a1 ÷ b1) ≃ (a2 ÷ b2) OR b1 ≃ b2 ≃ normalize 0 0} 

-- Get Y Value of Intersection Point out of the X Value
-- Problem1: Prove that b is not 0
-- Tim: Again, for an arbitrary line this simply isn't true, so you cannot prove it!
----XtoYVal : (l : Line) → (b≢0 l) →  ℚ →  ℚ
----XtoYVal (a x+ b y+1=0) (mkb≢0 bNot0) val = 
----    let
----      numb≢0 : isFalse ( ℤ.∣ ↥ b ∣ ≟ℕ 0)
----      numb≢0 = ≢0⇒num≢0 bNot0
----    in
----        _÷ℚ_  ((a *ℚ val) +ℚ (normalize 1 1)) b {n≢0 = numb≢0}



----intersecPoint :  (l1 : Line) → (b≢0 l1)  → (l2 : Line) → (b≢0 l2) → Point
----intersecPoint (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0)  (mkb≢0 b2Not0) = mkPoint (intersecXVal (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0) (mkb≢0 b2Not0)) (XtoYVal  (a1 x+ b1 y+1=0)  (mkb≢0 b1Not0)   (intersecXVal (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0) (mkb≢0 b2Not0)) ) (normalize 1 1)


-- Question: can you save parts of the code into variables to make it more readable?
-- If I could put (intersecXVal (a x+ b y+1=0) (a x+ b y+1=0)) into a variable xVal, I could simply write:
-- intersecPoint (a x+ b y+1=0) (a x+ b y+1=0) = mkPoint xVal (XtoYVal  (a x+ b y+1=0) xVal ) (normalize 1 1)


-- Calculate if Point is on Line
--data isOnLine : Point → Line → Set where
--  base : {a1 b1 a2 b2 : ℚ} → isOnLine (mkPoint a1 b1 (normalize 1 1))  (a2 x+ b2 y+1=0)  --needs additional constraint for a1,b1,a2,b2 {(a1* a2)+(b1*b2)+normalize 1 1 ≃ normalize 0 0} 

--onLineHelp :  Point → Line → Set
--onLineHelp (mkPoint a1 b1 c) (a2 x+ b2 y+1=0) = ((a1 *ℚ a2) +ℚ (b1 *ℚ b2) +ℚ (normalize 1 1) ≡ (normalize 0 0) ) 

--data onLineMath : Point → Line → Set → Set where
--  mkOnLineMath : ∀ {a1 b1 a2 b2 c}→ (mkPoint a1 b1 c) → (a2 x+ b2 y+1=0) → ((a1 *ℚ a2) +ℚ (b1 *ℚ b2) +ℚ (normalize 1 1) ≡ (normalize 0 0) ) → onLineMath (mkPoint a1 b1 c) → (a2 x+ b2 y+1=0)

--data isOnLine : (p : Point) → (l : Line) → (onLineMath p l) → Set where
  --mkOnLine : ∀ {a1 b1 a2 b2} (mkPoint a1 b1 (normalize 1 1)) → (a2 x+ b2 y+1=0) → ((a1 *ℚ a2) +ℚ (b1 *ℚ b2) +ℚ (normalize 1 1) ≃ (normalize 0 0) ) → isOnLine (mkPoint a1 b1 (normalize 1 1))  (a2 x+ b2 y+1=0)
--  mkOnLine : (p : Point) → (l : Line) → (onLineMath p l) → isOnLine p l

--needs additional constraint for a1,b1,a2,b2 {(a1* a2)+(b1*b2)+normalize 1 1 ≃ normalize 0 0} 


--Tests
-- XtoYVal ((normalize 1 1) x+ (normalize 2 1) y+1=0) (normalize 3 1)

-- Lemmas
-- Prove that the dual of a dual returns the original Line/Point

-- dualLP o dual PL = ID_L

--prove1 : getAValL dualPL(dualLP (a x+ b y+1=0)) ≃ getAValL (a x+ b y+1=0) 
--prove1 = ?  



-- First three lemmata of the paper:

-- Lemma 1: If a point p lies on a line L, then the dual of that line dL lies on the dual of that point dp

-- Lemma 2: If two points p1 and p2 lie on a line L, then the intersection of the dual of p1 and p2, is the dual point of line L

-- Lemma 3: If you move a point p on a line L, then the dual of that point rotates arround the dual of L




------- Zu den Implementierungen von der projektive Ebene P^2 und den homogene Koordinaten:


data True : Set where
  true : True

-- Tim: let's use  ⊥  (defined in Data.Empty) instead of False
-- data False : Set  where

-- Tim: comes with Relation.Nullary
-- ¬_ : Set → Set
-- ¬ A = A → False


--data Bool : Set where
--  BTrue : Bool
--  BFalse : Bool

--not : Bool → Bool
--not BTrue = BFalse
--not BFalse = BTrue

----_=b_ : ℚ → ℚ → Bool
----x =b x = True



-- Define a proof that a given Point is not (0,0,0)
data not0 : Point → Set  where
  xNotZero : {x y z : ℚ} → (x ≢ 0ℚ) → not0 (mkPoint x y z)
  yNotZero : {x y z : ℚ} → (y ≢ 0ℚ) → not0 (mkPoint x y z)
  zNotZero : {x y z : ℚ} → (z ≢ 0ℚ) → not0 (mkPoint x y z)

--Test proof
testProof : not0 (mkPoint (normalize 1 2) 0ℚ 0ℚ)
testProof = xNotZero ProofNot0 
  where
    ProofNot0 : ((normalize 1 2) ≢ 0ℚ)
    ProofNot0 = λ ()


-- Definiere PointNot0
data PointNot0 : Set where
  mkPointNot0 : (x y z : ℚ) → not0 (mkPoint x y z) → PointNot0

--Test proof
testProof2 : PointNot0
testProof2 =  mkPointNot0 (normalize 4 2) 1ℚ 0ℚ (yNotZero  ( λ () ))


data P2 : Set where
  3point : ℚ → ℚ → P2  -- (x,y,1)
  2point : ℚ → P2         -- (x,1,0)
  1point : P2                -- (1,0,0)


data _or_ (A B : Set) : Set where 
  inl : A → A or B
  inr : B → A or B

{-
dec≡ : (x : ℚ) → (x ≡ 0ℚ)  or  (¬(x  ≡ 0ℚ))
dec≡ x with (x ≡ 0ℚ)
... | refl = inl (x ≡ 0ℚ) 
... | _ = inr  (¬(x  ≡ 0ℚ))
-}

test : 0ℚ ≡ 0ℚ
test = refl

{-
pointToP2 : PointNot0 → P2
pointToP2 (mkPointNot0 x y z p) with ( dec≡ z )
...      | (inl (z ≡ 0ℚ) ) true = 3point (x ÷ℚ z) (y ÷ℚ z)  -- (x,y,1)
...      | (inr (¬(z  ≡ 0ℚ))  with ( dec≡ y )
         | (inr (¬(z  ≡ 0ℚ)) | (inl (z ≡ 0ℚ) )  = 2point (x ÷ℚ y)  -- (x,1,0)
         | (inr (¬(z  ≡ 0ℚ)) | (inr (¬(z  ≡ 0ℚ)) = 1point                           -- (1,0,0)
-}



ProofTrue :  1ℚ  ≢ 0ℚ
ProofTrue = λ ()


P2toPoint : P2 → Point
P2toPoint (3point x y) = mkPoint x y 0ℚ
P2toPoint (2point x) = mkPoint x 1ℚ 0ℚ
P2toPoint 1point = mkPoint 1ℚ 0ℚ 0ℚ



--Definition von Betrag für rationale Zahlen
abs : ℚ → ℚ
-- Tim: this only works for x ≢ 0 !
-- abs x = (x * x) ÷ x
--Oder (yes, much better!)
abs x  with (x <? 0ℚ)
... | false because _ = x
... | true because  _ = - x


-- example for nondecidable (unary) predicate

everywhereFalse : (f : ℕ → Bool) → Set
everywhereFalse f = ∀ n → (f n ≡ false)

decEverywhereFalse : DecidableP everywhereFalse
decEverywhereFalse f = {!!}  -- this is not implementable!


data 2SP : Set where
  3point+ : ℚ → ℚ → 2SP  -- (x,y,1)
  3point- : ℚ → ℚ → 2SP  -- (x,y,-1)
  
  2point+ : ℚ → 2SP         -- (x,1,0)
  2point- : ℚ → 2SP         -- (x,-1,0)
  
  1point+ : 2SP                -- (1,0,0)
  1point- : 2SP                -- (-1,0,0)


{-
pointTo2SP : Point → 2SP
pointTo2SP (mkPoint x y z) with (<-cmp z 0ℚ)

...      | tri> ?  = 3point+ (x ÷ℚ z) (y ÷ℚ z)                     -- (x,y,+1)
...      | tri< ?  = 3point- (x ÷ℚ (abs z)) (y ÷ℚ (abs z))      -- (x,y,-1)

...      | tri≈ ? with (<-cmp y 0ℚ)        
...      | tri≈ ? | tri> ?  =  2point+ (x ÷ℚ y)                     -- (x,+1,0)
...      | tri≈ ? | tri< ?  = 2point- (x ÷ℚ (abs y))               -- (x,-1,0)

...      | tri≈ ? | tri≈ ? with (<-cmp x 0ℚ)                        -- (+/-1,0,0)
...      | tri≈ ? | tri≈ ? | tri> ?  = 1point+                      -- (+/-1,0,0)
...      | tri≈ ? | tri≈ ? | tri< ?  = 1point-                        -- (+/-1,0,0)
 -}

{-
Erinnerung : Aufbau von <-cmp

<-cmp : Trichotomous _≡_ _<_
<-cmp p q with ℤ.<-cmp (↥ p ℤ.* ↧ q) (↥ q ℤ.* ↧ p)
... | tri< < ≢ ≯ = tri< (*<* <)        (≢ ∘ ≡⇒≃) (≯ ∘ drop-*<*)
... | tri≈ ≮ ≡ ≯ = tri≈ (≮ ∘ drop-*<*) (≃⇒≡ ≡)   (≯ ∘ drop-*<*)
... | tri> ≮ ≢ > = tri> (≮ ∘ drop-*<*) (≢ ∘ ≡⇒≃) (*<* >)
-}


2SPtoPoint : 2SP → Point
2SPtoPoint 1point+ = mkPoint 1ℚ 0ℚ 0ℚ
2SPtoPoint 1point- = mkPoint (- 1ℚ) 0ℚ 0ℚ

2SPtoPoint (2point+ x) = mkPoint x 1ℚ 0ℚ
2SPtoPoint (2point- x) = mkPoint x (- 1ℚ) 0ℚ

2SPtoPoint (3point+ x y) = mkPoint x y 1ℚ
2SPtoPoint (3point- x y) = mkPoint x y (- 1ℚ)



-- Line to 2SP
-- Problem?: Bis jetzt stellen wir geraden nur durch die 2 endlichen Werte a und b da.
-- Allerdings kann man damit das dual von Punkten die unendlich weit weg zum Ursprung sind nicht bilde.
-- Das wären also Geraden die durch den Ursprung wandern. Dies könnte ein Problem sein.
-- Idee vieleicht Geraden auch im 2SP Koordinatensystem darstellen?
-- dual von (a,b,c) also nicht mehr als ((a÷c) x+ (b÷c) y +1=0) darstellen sondern als, zum Beispiel, 1line+, 1line-, 2line+ ...
-- Dann wären Geraden und 2Sp Punkte aber auch fast identisch..
dualL2SP : Line  → 2SP
dualL2SP (a x+ b y+1=0) = 3point+ a b


--2SP to Line
-- Wegen dem selben Grund können wir im Moment  auch nur die 3point Version 2SP zu Geraden umwandeln 
dual2SPL : 2SP  → Line
--dual2SPL 1point+ = (1ℚ) x+ (0ℚ) y+1=0
--dual2SPL 1point- = (- 1ℚ) x+ (0ℚ) y+1=0

--dual2SPL (2point+ a) = (a) x+ (1ℚ) y+1=0
--dual2SPL (2point- a) = (a) x+ (- 1ℚ) y+1=0

dual2SPL (3point+ a b) = (a) x+ (b) y+1=0
dual2SPL (3point- a b) = (- a) x+ (- b) y+1=0


-- Intersection
-- Ich versuche die Intersection zwischen zwei Geraden ähnlich zu machen wie ich das vorher definiert hatte
-- Der Vorteil ist dass zwei Geraden sich in 2SP immer schneiden und man jetzt keinen "haveIntersection" Proof aufstellen muss

-- Problem: Geraden die sich im Unendlichen schneiden nicht behandelt.
-- Idee: Eventuell Fallunterscheidung:

--Fall1: Geraden haben einen Schnittpunkt in ℚ^2
--Hier eventuell soetwas ähnliches wie:
--intersec2SP (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) = Point3point+ (intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0)) (XtoYVal  (a1 x+ b1 y+1=0) (intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0)) )
--Fall2: Geraden schneiden sich nicht in ℚ^2 => Schnittpunkt im unendlichen
--Fall3: Geraden sind identisch: Da bin ich mir nicht sicher wie man vorgehen sollte: Einen beliebigen Schnittpunkt wählen? Diesen Fall gar nicht betrachten?

{-
intersec2SP : Line → Line → 2SP
intersec2SP (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) with (a1 ≃ a2)
...                                                                           | true
...                                                                           | true  with (b1 ≃ b2)
...                                                                           | true | true  -- Fall3
...                                                                           | true | false -- Fall1

...                                                                           | false
...                                                                           | false with (b1 ≃ b2)
...                                                                           | false | true  --Fall1
...                                                                           | false | false --Fall1 oder Fall2 falls (a1÷a2)≃(b1÷b2) also falls die entsprechenden Richtungsvektoren in die selbe richtung zeigen
-}
--Ich glaube diesen Aufbau habe ich etwas unnötig komplex gemacht


--Beweis ob ein 2SP-Punkt auf einer Gerade liegt
--Idee: ähnlicher Aufbau wie bei ℚ^2 Punkt auf einer Gerade
--Problem würe nicht bei Punkten funktionieren, die unendlich weit weg vom Ursprung liegen.

-- Calculate if Point is on Line
--data isOnLine : Point → Line → Set where
--...



--Todo:
--Fallunterscheidung richtig machen (true und false durch etwas passendes ersetzen)
--Beweis, dass x nicht 0 ist richtig aufstellen
--Eventuell Geraden neu definieren im homogenen im 2SP Koordinatensystem?
--...
