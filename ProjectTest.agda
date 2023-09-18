open import Data.Rational
open import Data.Rational.Properties
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


--Dual functions

--Point to Line
-- Tim: Cannot work like this. You need an additional argument of type z ≢ 0 
dualPL : Point  → Line
dualPL (mkPoint a b z) = {!!} -- (a ÷ z) x+ (b ÷ z) y+1=0

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
intersecXVal : Line  → Line  →  ℚ
intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) = {!!} -- - (b1 - b2) ÷ ((b1 * b2) * ((a1 ÷ b2) - (a1 ÷ b1))) 

-- Idea to solve Problem1: Add a isNotZero function or Type:
-- data isNotZero : ℚ → Set  where
-- base : 

-- Idea to solve Problem2: Two Lines have no intersection Points, if they are parallel, which also means, that their dual Points have the same angle to the origin
-- Note: Equality in Rationals is already defined with the ≃ operator
data haveIntersection : Line  → Line  →  Set where
  base : {a1 b1 a2 b2 : ℚ} → haveIntersection  (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) --need additional constraint for a1,b1,a2,b2 {(a1 ÷ b1) ≃ (a2 ÷ b2) OR b1 ≃ b2 ≃ normalize 0 0} 

-- Get Y Value of Intersection Point out of the X Value
-- Problem1: Prove that b is not 0
-- Tim: Again, for an arbitrary line this simply isn't true, so you cannot prove it!
XtoYVal : Line →  ℚ →  ℚ
XtoYVal (a x+ b y+1=0) val = {!!} -- ((a * val) + (normalize 1 1)) ÷ b


intersecPoint : Line → Line → Point
intersecPoint (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) = mkPoint (intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0)) (XtoYVal  (a1 x+ b1 y+1=0) (intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0)) ) (normalize 1 1)
-- Question: can you save parts of the code into variables to make it more readable?
-- If I could put (intersecXVal (a x+ b y+1=0) (a x+ b y+1=0)) into a variable xVal, I could simply write:
-- intersecPoint (a x+ b y+1=0) (a x+ b y+1=0) = mkPoint xVal (XtoYVal  (a x+ b y+1=0) xVal ) (normalize 1 1)


-- Calculate if Point is on Line
data isOnLine : Point → Line → Set where
  base : {a1 b1 a2 b2 : ℚ} → isOnLine (mkPoint a1 b1 (normalize 1 1))  (a2 x+ b2 y+1=0)  --needs additional constraint for a1,b1,a2,b2 {(a1* a2)+(b1*b2)+normalize 1 1 ≃ normalize 0 0} 

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


data z≢0 : Point → Set where
  mkz≢0 : ∀ {x y z} → (z ≢ 0ℚ) → z≢0 (mkPoint x y z)

≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt


dualPL' : (p : Point) → z≢0 p → Line
dualPL' (mkPoint x y z) (mkz≢0 zNot0) =
    let
      num≢0 : isFalse ( ℤ.∣ ↥ z ∣ ≟ℕ 0)
      num≢0 = ≢0⇒num≢0 zNot0
    in
      dualPL (mkPoint (_÷_  x z {n≢0 = num≢0}) (_÷_  y z {n≢0 = num≢0}) 1ℚ)

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
  xNotZero : (x : ℚ) → (¬(x  ≃ 0ℚ)) → (y : ℚ) → (z : ℚ) → not0 (mkPoint x y z)
  yNotZero : (x : ℚ) → (y : ℚ)  → (¬(y  ≃ 0ℚ)) → (z : ℚ) → not0 (mkPoint x y z)
  zNotZero : (x : ℚ) → (y : ℚ) → (z : ℚ) → (¬(z  ≃ 0ℚ))  → not0 (mkPoint x y z)

--Test prove:
--Prove still does not work. I don't know why
----prove1 : not0 (mkPoint (normalize 1 2) 0ℚ 0ℚ)
----prove1 = xNotZero (normalize 1 2) (¬( normalize 1 2  ≃ 0ℚ)) 0ℚ 0ℚ

--Maybe more like this:?
proof1 : not0 (mkPoint (normalize 1 2) 0ℚ 0ℚ)
proof1 = xNotZero (normalize 1 2) ProofNot0 0ℚ 0ℚ
  where
    ProofNot0 : (normalize 1 2)  ≃ 0ℚ → ⊥
    ProofNot0 ()


--Weiter ohne proof:

data P2 : Set where
  3point : ℚ → ℚ → P2  -- (x,y,1)
  2point : ℚ → P2         -- (x,1,0)
  1point : P2                -- (1,0,0)

--Problem: (...  ≃ 0ℚ) bzw. ¬ (...  ≃ 0ℚ) sind keine Funktionen,
--die zum Beispiel true oder false oder ähnliches zurückgeben woran man eine Fallunterscheidung machen kann 
--Idee: Vieleicht neue ≃b und ¬b erstellen, die man zwar weniger Gut für beweise, aber dafür für Fallunterscheidungen nutzen kann?
--true und false müsste man hier auf jeden Fall durch etwas passenderes ersetzen

----pointToP2 : Point → P2
----pointToP2 (mkPoint x y z) with (¬(z  ≃ 0ℚ))
----...      | true = 3point (x ÷ z) (y ÷ z)  -- (x,y,1)
----...      | false with (¬(y  ≃ 0ℚ))
----         | false | true  = 2point (x ÷ y)  -- (x,1,0)
----         | false | false                            -- (1,0,0)

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


--pointTo2SP : Point → 2SP
--pointTo2SP (mkPoint x y z) with (¬(z  ≃ 0ℚ))
--...      | true with (z ≥ 0ℚ)                                                 -- (x,y,+/-1)
--...      | true | true = 3point+ (x ÷ z) (y ÷ z)                     -- (x,y,+1)
--...      | true | false = 3point- (x ÷ (abs z)) (y ÷ (abs z))   -- (x,y,-1)

--...      | false with (¬(y  ≃ 0ℚ))                      
--...      | false | true  with (y ≥ 0ℚ)                              -- (x,+/-1,0)
--...      | false | true | true =  2point+ (x ÷ y)             -- (x,+1,0)
--...      | false | true | false = 2point- (x ÷ (abs y))      -- (x,-1,0)

--...      | false | false with (x ≥ 0ℚ)                       -- (+/-1,0,0)
--...      | false | false | true = 1point+                   -- (+/-1,0,0)
--...      | false | false | false = 1point-                    -- (+/-1,0,0)



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
