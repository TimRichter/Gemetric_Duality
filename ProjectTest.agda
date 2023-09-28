open import Data.Rational renaming (_*_ to _*ℚ_ ; _+_ to _+ℚ_ ; _-_ to _-ℚ_ ; _÷_ to _÷ℚ'_ ;
                                    _≟_ to _≟ℚ_ ; _>_ to _>ℚ_)
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
open import Function.Base
--open import Data.Integer
--open import Data.Nat





-- Division in the rational numbers
infixl 7 _÷ℚ_
_÷ℚ_ : (p q : ℚ) → {q≢0 : q ≢ 0ℚ} → ℚ
_÷ℚ_ p q {q≢0} = _÷ℚ'_ p q {n≢0 = ≢0⇒num≢0 q≢0}  where
  ≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
  ≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
  ≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
  ≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt

-- Define absolut value for rational Numbers
abs : ℚ → ℚ
abs x  with (x <? 0ℚ)
... | false because _ = x
... | true because  _ = - x

-- Naive 3D representation of 2DPoints
data Point : Set where
  mkPoint :   ℚ  →  ℚ  →  ℚ   → Point

-- get X value from Point
X : Point →   ℚ
X (mkPoint x y z) = x

-- get Y value from Point
Y : Point →   ℚ
Y (mkPoint x y z) = y

-- get Z value from Point
Z : Point →   ℚ
Z (mkPoint x y z) = z


-- Define 2D Line (Idea: basically same structure as Points but verry different interpretation)
data Line : Set where
  _x+_y+1=0 :   ℚ  →  ℚ   → Line

-- Get a-value of Line
A : Line → ℚ
A (a x+ b y+1=0) = a

-- Get b-value of Line
B : Line → ℚ
B (a x+ b y+1=0) = b





------- projective plane P^2 and two-sided plane 2SP 



-- check if z-value of a Point is not 0
data z≢0 : Point → Set where
  mkz≢0 : ∀ {x y z} → (z ≢ 0ℚ) → z≢0 (mkPoint x y z)

testProofz≢0 : z≢0 (mkPoint  0ℚ  1ℚ  1ℚ)
testProofz≢0 = mkz≢0 λ ()


-- Define a proof that a given Point is not (0,0,0)
data not0 : Point → Set  where
  xNotZero : {p : Point} → (X p ≢ 0ℚ) → not0 p
  yNotZero : {p : Point} → (Y p ≢ 0ℚ) → not0 p
  zNotZero : {p : Point} → (Z p ≢ 0ℚ) → not0 p

--Test proof Not0
testProofNot0 : not0 (mkPoint (normalize 1 2) 0ℚ 0ℚ)
testProofNot0 = xNotZero ProofNot0 
  where
    ProofNot0 : ((normalize 1 2) ≢ 0ℚ)
    ProofNot0 = λ ()


-- Define PointNot0 which acts similar to normal Points but excludes (0,0,0)
data PointNot0 : Set where
  mkPointNot0 : (p  : Point) → (not0 p) → PointNot0

-- Test proof PointNot0
testProofPointNot0 : PointNot0
testProofPointNot0 =  mkPointNot0 (mkPoint (normalize 4 2) 1ℚ 0ℚ) (yNotZero  ( λ () ))

-- PointNot0 to Point
P : PointNot0 → Point
P (mkPointNot0  (mkPoint x y z) p) = mkPoint x y z

-- Point to PointNot0
pToNot0 : (p : Point) → (not0 p)  → PointNot0
pToNot0 (mkPoint x y z) proof = mkPointNot0  (mkPoint x y z) proof
--does not work yet--pToNot0 p proof = mkPointNot0 (mkPoint (X p) (Y p) (Z p)) proof

-- Define P2 Points
-- Here every point has exactly one notation
-- Problem: P2 is not orientable
data P2 : Set where
  3point : ℚ → ℚ → P2  -- (x,y,1)
  2point : ℚ → P2         -- (x,1,0)
  1point : P2                -- (1,0,0)


-- Transform PointNot0 into P2
pointToP2 : PointNot0 → P2
pointToP2 (mkPointNot0 (mkPoint  x y z) p) with ( z ≟ℚ 0ℚ )
... | no z≢0 = 3point (_÷ℚ_ x z {z≢0}) (_÷ℚ_ y z {z≢0})  -- (x,y,1)
... | yes z≡0 with ( y ≟ℚ 0ℚ )
...    | no y≢0 = 2point (_÷ℚ_ x y {y≢0})                            -- (x,1,0)
...    | yes y≡0 with (x ≟ℚ 0ℚ)
...      | no x≢0 = 1point                                                       -- (1,0,0)
...      | yes x≡0 with p                                                         -- (0,0,0) p proves that this case does not occur
...        | xNotZero x≢0 = ⊥-elim (x≢0 x≡0)
...        | yNotZero y≢0 = ⊥-elim (y≢0 y≡0)
...        | zNotZero z≢0 = ⊥-elim (z≢0 z≡0)


-- Transform P2 into PointsNot0
P2toPoint : P2 → PointNot0
P2toPoint (3point x y) = mkPointNot0  (mkPoint x y 1ℚ) (zNotZero  ( λ () ))
P2toPoint (2point x) = mkPointNot0  (mkPoint x 1ℚ 0ℚ) (yNotZero  ( λ () ))
P2toPoint 1point = mkPointNot0  (mkPoint 1ℚ 0ℚ 0ℚ) (xNotZero  ( λ () ))


-- example for nondecidable (unary) predicate
everywhereFalse : (f : ℕ → Bool) → Set
everywhereFalse f = ∀ n → (f n ≡ false)

--decEverywhereFalse : DecidableP everywhereFalse
--decEverywhereFalse f = {!!}  -- this is not implementable!


-- Define 2SP (two-sided plane)
-- Simillar to P2, but is orientalbe becaue we desitingisch between
-- npoint+ and npoint- (if a Point is "above" or "below" the plane)
data 2SP : Set where
  3point+ : ℚ → ℚ → 2SP  -- (x,y,1)
  3point- : ℚ → ℚ → 2SP  -- (x,y,-1)
  
  2point+ : ℚ → 2SP         -- (x,1,0)
  2point- : ℚ → 2SP         -- (x,-1,0)
  
  1point+ : 2SP                -- (1,0,0)
  1point- : 2SP                -- (-1,0,0)


-- Prove that if x is not 0, then |x| is also not 0
--absLemma : {x : ℚ} → (x ≢ 0ℚ) → ((abs x) ≢ 0ℚ)
--absLemma  =  {!!}


-- Transform (Not0) points into 2SP points
pointTo2SP : PointNot0 → 2SP
pointTo2SP (mkPointNot0  (mkPoint x y z) p) with (<-cmpℚ z 0ℚ )

...      | (tri> _ z≢0 _)  = 3point+ (_÷ℚ_ x z {z≢0} ) (_÷ℚ_ y z {z≢0} )                     -- (x,y,+1)
...      | (tri< _ z≢0 _)  = 3point- ( _÷ℚ_ (- x) z {z≢0}  ) (_÷ℚ_ (- y)  z {z≢0})      -- (x,y,-1)

...      | (tri≈ _ z≡0 _) with (<-cmpℚ y 0ℚ)        
...            | (tri> _ y≢0 _)  =  2point+ (_÷ℚ_ x y {y≢0})                     -- (x,+1,0)
...            | (tri< _ y≢0 _)  = 2point- ( _÷ℚ_ (- x)  y {y≢0})               -- (x,-1,0)

...            | (tri≈ _ y≡0 _) with (<-cmpℚ x 0ℚ)                        -- (+/-1,0,0)
...                   | (tri> _ x≢0 _)  = 1point+                      -- (+/-1,0,0)
...                   | (tri< _ x≢0 _)  = 1point-                        -- (+/-1,0,0)

...                   | (tri≈ _ x≡0 _)  with p                             -- (0,0,0) p beweist, dass dieser Fall nicht eintritt
...                          | xNotZero x≢0  = ⊥-elim (x≢0 x≡0)
...                          | yNotZero y≢0  = ⊥-elim (y≢0 y≡0)
...                          | zNotZero z≢0  = ⊥-elim (z≢0 z≡0)


-- Transform 2SP points into (Not0) points
2SPtoPoint : 2SP → PointNot0
2SPtoPoint 1point+ = mkPointNot0  (mkPoint 1ℚ 0ℚ 0ℚ) (xNotZero  ( λ () ))
2SPtoPoint 1point- = mkPointNot0  (mkPoint (- 1ℚ) 0ℚ 0ℚ) (xNotZero  ( λ () ))

2SPtoPoint (2point+ x) = mkPointNot0  (mkPoint x 1ℚ 0ℚ) (yNotZero  ( λ () ))
2SPtoPoint (2point- x) = mkPointNot0  (mkPoint x (- 1ℚ) 0ℚ) (yNotZero  ( λ () ))

2SPtoPoint (3point+ x y) = mkPointNot0  (mkPoint x y 1ℚ) (zNotZero  ( λ () ))
2SPtoPoint (3point- x y) = mkPointNot0  (mkPoint x y (- 1ℚ)) (zNotZero  ( λ () ))


--2SP lines
data 2SPLine : Set where
  3line+ : ℚ → ℚ → 2SPLine  -- (a,b,1)
  3line- : ℚ → ℚ → 2SPLine  -- (a,b,-1)
  
  2line+ : ℚ → 2SPLine         -- (a,1,0)
  2line- : ℚ → 2SPLine         -- (a,-1,0)
  
  1line+ : 2SPLine                -- (1,0,0)
  1line- : 2SPLine                -- (-1,0,0)


-- Transform 2SP Lines into (Not0) points
2SPLinetoPoint : 2SPLine → PointNot0
2SPLinetoPoint 1line+ = mkPointNot0  (mkPoint 1ℚ 0ℚ 0ℚ) (xNotZero  ( λ () ))
2SPLinetoPoint 1line- = mkPointNot0  (mkPoint (- 1ℚ) 0ℚ 0ℚ) (xNotZero  ( λ () ))

2SPLinetoPoint (2line+ x) = mkPointNot0  (mkPoint x 1ℚ 0ℚ) (yNotZero  ( λ () ))
2SPLinetoPoint (2line- x) = mkPointNot0  (mkPoint x (- 1ℚ) 0ℚ) (yNotZero  ( λ () ))

2SPLinetoPoint (3line+ x y) = mkPointNot0  (mkPoint x y 1ℚ) (zNotZero  ( λ () ))
2SPLinetoPoint (3line- x y) = mkPointNot0  (mkPoint x y (- 1ℚ)) (zNotZero  ( λ () ))

-- Transform (Not0) points into 2SP pointslines
pointTo2SPLine : PointNot0 → 2SPLine
pointTo2SPLine (mkPointNot0  (mkPoint x y z) p) with (<-cmpℚ z 0ℚ )

...      | (tri> _ z≢0 _)  = 3line+ (_÷ℚ_ x z {z≢0} ) (_÷ℚ_ y z {z≢0} )                     -- (x,y,+1)
...      | (tri< _ z≢0 _)  = 3line- ( _÷ℚ_ (- x) z {z≢0}  ) (_÷ℚ_ (- y)  z {z≢0})      -- (x,y,-1)

...      | (tri≈ _ z≡0 _) with (<-cmpℚ y 0ℚ)        
...            | (tri> _ y≢0 _)  =  2line+ (_÷ℚ_ x y {y≢0})                     -- (x,+1,0)
...            | (tri< _ y≢0 _)  = 2line- ( _÷ℚ_ (- x)  y {y≢0})               -- (x,-1,0)

...            | (tri≈ _ y≡0 _) with (<-cmpℚ x 0ℚ)                        -- (+/-1,0,0)
...                   | (tri> _ x≢0 _)  = 1line+                      -- (+/-1,0,0)
...                   | (tri< _ x≢0 _)  = 1line-                        -- (+/-1,0,0)

...                   | (tri≈ _ x≡0 _)  with p                             -- (0,0,0) p beweist, dass dieser Fall nicht eintritt
...                          | xNotZero x≢0  = ⊥-elim (x≢0 x≡0)
...                          | yNotZero y≢0  = ⊥-elim (y≢0 y≡0)
...                          | zNotZero z≢0  = ⊥-elim (z≢0 z≡0)



-------Geometric duality


-- Dual functions

dual2SPto2SPLine : 2SP → 2SPLine

dual2SPto2SPLine (3point+ a b) = 3line+ a b
dual2SPto2SPLine (3point- a b) = 3line- a b

dual2SPto2SPLine (2point+ a ) = 2line+ a 
dual2SPto2SPLine (2point- a ) = 2line- a 

dual2SPto2SPLine (1point+ ) = 1line+ 
dual2SPto2SPLine (1point- ) = 1line- 


dual2SPLineto2SP : 2SPLine → 2SP

dual2SPLineto2SP (3line+ a b) = 3point+ a b
dual2SPLineto2SP (3line- a b) = 3point- a b

dual2SPLineto2SP (2line+ a) = 2point+ a
dual2SPLineto2SP (2line- a) = 2point- a

dual2SPLineto2SP (1line+ ) = 1point+
dual2SPLineto2SP (1line- ) = 1point- 


-- Dual Lines to 2SP
{-
dualL2SP : Line  → 2SP
dualL2SP (a x+ b y+1=0) = 3point+ a b

-- Dual 2SP to Line
-- Note: in the current representation for lines, we can only transform 2SP points with z≢0 into lines
-- Probably need to represent lines with 2SP coordinates

dual2SPL : 2SP  → Line
dual2SPL (3point+ a b) = (a) x+ (b) y+1=0
dual2SPL (3point- a b) = (- a) x+ (- b) y+1=0
-}

-- Helper function
≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt



-- Dual points to lines
{-
dualPL : (p : Point) → z≢0 p → Line
dualPL (mkPoint x y z) (mkz≢0 zNot0) =
    let
      num≢0 : isFalse ( ℤ.∣ ↥ z ∣ ≟ℕ 0)
      num≢0 = ≢0⇒num≢0 zNot0
    in
      (_÷ℚ_ x z {n≢0 = num≢0}) x+  _÷ℚ_  y z {n≢0 = num≢0} y+1=0
-}

-- Dual line to points 
dualLP : Line  → Point
dualLP (a x+ b y+1=0) =  mkPoint a b (normalize 1 1) 


-- Dot product
_∙_ : Point -> Point -> ℚ               
p1 ∙ p2 = ( (X p1 *ℚ X p2) +ℚ (Y p1 *ℚ Y p2) +ℚ (Z p1 *ℚ Z p2) )

-- Cross product
_×_ : Point -> Point -> Point 
p1 × p2 = mkPoint (Y p1 *ℚ Z p2 -ℚ Z p1 *ℚ Y p2) (Z p1 *ℚ X p2 -ℚ X p1 *ℚ Z p2) (X p1 *ℚ Y p2 -ℚ Y p1 *ℚ X p2)


-- Check if Point is on Line
checkOnLine :  2SP → 2SPLine → Bool
checkOnLine 2sp 2spLine with 2SPtoPoint 2sp 
...     | p1 with 2SPLinetoPoint 2spLine
...          | p2 with ( (P p1) ∙ (P p2) ) ≟ℚ 0ℚ 
...                         | yes proof1 = true
...                         | no proof2 = false

-- point(4,-3,1) line(2,3,1) +1
testProofOnLine1 : checkOnLine (3point+ (normalize 4 1)  (- (normalize 3 1) )) (3line+ (normalize 2 1)  (normalize 3 1) ) ≡  true
testProofOnLine1 = refl

-- point(0,1,0) line(1,0,0) +0
testProofOnLine2 : checkOnLine (2point+ 0ℚ ) (1line+ ) ≡  true
testProofOnLine2 = refl

-- point(-3/2,1,0) line(2,3,1) +1
testProofOnLine3 : checkOnLine (2point+ (- (normalize 3 2) )) (3line+  (normalize 2 1) (normalize 3 1)) ≡  true
testProofOnLine3 = refl

-- point(6,-4,1) line(2/3,1,0) +0
testProofOnLine4 : checkOnLine (3point+ (normalize 6 1) (- (normalize 4 1))) (2line+ (normalize 2 3) ) ≡  true
testProofOnLine4 = refl

-- point(0,1,0) line(0,0,1) +0
testProofOnLine5 : checkOnLine (2point+ 0ℚ ) (3line+ 0ℚ 0ℚ) ≡  true
testProofOnLine5 = refl



-- PointNot0 equalities

-- Stronger equality
infix 4 _==_
_==_ : PointNot0 → PointNot0 → Set
p == q  = P p ≡ P q

--Testproof (2,1,0) == (2,1,0)
testProof1== : (mkPointNot0  (mkPoint (normalize 2 1) 1ℚ 0ℚ) (xNotZero λ ()) ) == (mkPointNot0  (mkPoint (normalize 2 1) 1ℚ 0ℚ) (xNotZero λ ()) )
testProof1== = refl

--Testproof (2,1,0) == (6,3,0)
testProof2== : ( (mkPointNot0  (mkPoint (normalize 2 1) 1ℚ 0ℚ) (xNotZero λ ()) ) == (mkPointNot0  (mkPoint (normalize 6 1) (normalize 3 1) 0ℚ) (xNotZero λ ()) ) ) → ⊥
testProof2== = λ ()

-- Scalar multiplication
_⋆_  : ℚ → Point → Point
q  ⋆  p =  mkPoint  (q *ℚ X p) (q *ℚ Y p) (q *ℚ Z p)

-- Weaker equality
infix 4 _~_
data _~_ :  (p1 : PointNot0) → (p2 : PointNot0) → Set where
  mk~ : {p1 p2 : Point} → {proof1 :  not0 p1} → {proof2 :  not0 p2} → (lamb : ℚ) → (lamb >ℚ 0ℚ) → ( (lamb ⋆ p1) ≡ p2 ) → ( (pToNot0 p1 proof1) ~ (pToNot0 p2 proof2) )

--Testproof (2,1,0) ~ (2,1,0)
testProof1~ : (mkPointNot0  (mkPoint (normalize 2 1) 1ℚ 0ℚ) (xNotZero λ ()) ) ~ (mkPointNot0  (mkPoint (normalize 2 1) 1ℚ 0ℚ) (xNotZero λ ()) )
testProof1~ = mk~ 1ℚ (*<* (ℤ.+<+ (s≤s z≤n))) refl 

--Testproof (2,1,0) ~ (6,3,0)
testProof2~ : ( (mkPointNot0  (mkPoint (normalize 2 1) 1ℚ 0ℚ) (xNotZero λ ()) ) ~ (mkPointNot0  (mkPoint (normalize 6 1) (normalize 3 1) 0ℚ) (xNotZero λ ()) ) )
testProof2~ = mk~ (normalize 3 1) (*<* (ℤ.+<+ (s≤s z≤n))) refl 



-- Intersection between lines:


-- Cross product


-- Proof that two Points don't have a crossProduct of (0,0,0)
data xProductNot0 : PointNot0 →  PointNot0 → Set where
  mkxProductNot0 : {x1 y1 z1 x2 y2 z2 : ℚ} → {proof1 :  not0 (mkPoint x1 y1 z1)} → {proof2 :  not0 (mkPoint x2 y2 z2)} →  not0 (mkPoint (y1 *ℚ z2 -ℚ z1 *ℚ y2) (z1 *ℚ x2 -ℚ x1 *ℚ z2) (x1 *ℚ y2 -ℚ y1 *ℚ x2) ) → xProductNot0 (mkPointNot0  (mkPoint x1 y1 z1) proof1) (mkPointNot0  (mkPoint x2 y2 z2) proof2)
--does not work yet--  mkxProductNot0 : {p1 p2 : Point} → {proof1 :  not0 p1} → {proof2 :  not0 p2} →  not0 (p1 × p2  ) → xProductNot0 (pToNot0 p1 proof1) (pToNot0 p2 proof2)


xProduct : (p1 : PointNot0) → (p2 : PointNot0) → (xProductNot0 p1 p2) → PointNot0
xProduct p1 p2 xPNot0 with xPNot0
...     | (mkxProductNot0 proof ) = pToNot0 ( (P p1) × (P p2) ) proof


-- testProof cross product of (2,2,1) and (-2,0,1) is (2, -4, 4)
testProofxProduct :  ( xProduct (mkPointNot0  (mkPoint (normalize 2 1) (normalize 2 1) 1ℚ) (xNotZero  ( λ () )) )  (mkPointNot0  (mkPoint (- (normalize 2 1)) 0ℚ 1ℚ) (xNotZero  ( λ () )) )  (mkxProductNot0 (xNotZero  ( λ () )  )) ) ==  ( mkPointNot0  (mkPoint (normalize 2 1) (- (normalize 4 1))  (normalize 4 1)) (xNotZero  ( λ () )) )
testProofxProduct = refl


-- Calculate Intersection between lines:
intersection : (l1 : 2SPLine) → (l2 : 2SPLine) → (xProductNot0 (2SPLinetoPoint l1) (2SPLinetoPoint l2)) → 2SP
intersection L1 L2 p with (2SPLinetoPoint L1)
...   | mkPointNot0  (mkPoint x1 y1 z1) p1 with (2SPLinetoPoint L2)
...          | mkPointNot0  (mkPoint x2 y2 z2) p2 = pointTo2SP (xProduct (mkPointNot0  (mkPoint x1 y1 z1) p1) (mkPointNot0  (mkPoint x2 y2 z2) p2) p )


-- testProof line(- 1, 0, 1) line(0, -1/2, 1) point(1, 2, 1)
testProofIntersection1 : (  intersection (3line+ (- normalize 1 1) 0ℚ ) (3line+ 0ℚ (- normalize 1 2)) (mkxProductNot0 (xNotZero ( λ () )) )  ) ≡ (  3point+ (normalize 1 1) (normalize 2 1)  )
testProofIntersection1 = refl 

-- testProof line(- 1/5, 1/10, 1) line(0, 1/2, 1) Point(4, -2, 1)
-- Problem:  (3point-  -4 2) ≡ (3point+  4 -2) is not true
-- Solution? transform both 2SP points to PointNot0 and compare with ~?
-- This does not work anymore, since ~ uses only positive lambda. intersection line(- 1/5, 1/10, 1) line(0, 1/2, 1) = Point(-2/5, 1/5, 1)
-- But Point(-2/5, 1/5, 1) ~ (4, -2, 1) is only true for negative lambdas
--testProofIntersection2 : 2SPtoPoint (  intersection (3line+ (- normalize 1 5) (normalize 1 10)) (3line+ 0ℚ (normalize 1 2)) (mkxProductNot0 (xNotZero ( λ () )) )  ) ~ 2SPtoPoint (  3point+ (normalize 4 1) (- (normalize 2 1))  )
--testProofIntersection2 = mk~ (- 1ℚ) (*<* {!!})  refl



--testProof
testProof~ : {x : PointNot0} → ( (2SPtoPoint ∘ pointTo2SP)  x) ~ x
testProof~ = {!!}

------------
-- Reminder: First three lemmata of the paper


-- Lemma 1: If a point p lies on a line L, then the dual of that line dL lies on the dual of that point dp
lemma1 : {x1 y1 z1 x2 y2 z2 : ℚ} → {p1 :  not0 (mkPoint x1 y1 z1)} → {p2 :  not0 (mkPoint x2 y2 z2)} → ((checkOnLine (pointTo2SP (mkPointNot0  (mkPoint x1 y1 z1) p1)) (pointTo2SPLine (mkPointNot0  (mkPoint x2 y2 z2) p2)) ) ≡ true) -> ((checkOnLine (dual2SPLineto2SP (pointTo2SPLine (mkPointNot0  (mkPoint x2 y2 z2) p2)) ) (dual2SPto2SPLine (pointTo2SP (mkPointNot0  (mkPoint x1 y1 z1) p1)) ) ) ≡ true)
lemma1 x = {!!}


-- Lemma 2: If two points p1 and p2 lie on a line L, then the intersection of the dual of p1 and p2, is the dual point of line L



-- Lemma 3: If you move a point p on a line L, then the dual of that point rotates arround the dual of L


