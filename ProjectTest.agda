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





-- Division in the rational numbers
infixl 7 _÷ℚ_
_÷ℚ_ : (p q : ℚ) → {q≢0 : q ≢ 0ℚ} → ℚ
_÷ℚ_ p q {q≢0} = _÷ℚ'_ p q {n≢0 = ≢0⇒num≢0 q≢0}  where
  ≢0⇒num≢0 : {q : ℚ} → q ≢ 0ℚ → isFalse ( ℤ.∣ ↥ q ∣ ≟ℕ 0)
  ≢0⇒num≢0 {mkℚ (+_ zero)  denominator-1 isCoprime} proof = proof (≃⇒≡ refl)
  ≢0⇒num≢0 {mkℚ +[1+ n ]   denominator-1 isCoprime} proof = tt
  ≢0⇒num≢0 {mkℚ (-[1+_] n) denominator-1 isCoprime} proof = tt


-- Naive 3D representation of 2DPoints
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





------- projective plane P^2 and two-sided plane 2SP 



-- check if z-value of a Point is not 0
data z≢0 : Point → Set where
  mkz≢0 : ∀ {x y z} → (z ≢ 0ℚ) → z≢0 (mkPoint x y z)

testProofz≢0 : z≢0 (mkPoint  0ℚ  1ℚ  1ℚ)
testProofz≢0 = mkz≢0 λ ()


-- Define a proof that a given Point is not (0,0,0)
data not0 : Point → Set  where
  xNotZero : {x y z : ℚ} → (x ≢ 0ℚ) → not0 (mkPoint x y z)
  yNotZero : {x y z : ℚ} → (y ≢ 0ℚ) → not0 (mkPoint x y z)
  zNotZero : {x y z : ℚ} → (z ≢ 0ℚ) → not0 (mkPoint x y z)

--Test proof Not0
testProofNot0 : not0 (mkPoint (normalize 1 2) 0ℚ 0ℚ)
testProofNot0 = xNotZero ProofNot0 
  where
    ProofNot0 : ((normalize 1 2) ≢ 0ℚ)
    ProofNot0 = λ ()


-- Define PointNot0 which acts similar to normal Points but excludes (0,0,0)
data PointNot0 : Set where
  mkPointNot0 : (x y z : ℚ) → not0 (mkPoint x y z) → PointNot0

-- Test proof PointNot0
testProofPointNot0 : PointNot0
testProofPointNot0 =  mkPointNot0 (normalize 4 2) 1ℚ 0ℚ (yNotZero  ( λ () ))


-- Define P2 Points
-- Here every point has exactly one notation
-- Problem: P2 is not orientable
data P2 : Set where
  3point : ℚ → ℚ → P2  -- (x,y,1)
  2point : ℚ → P2         -- (x,1,0)
  1point : P2                -- (1,0,0)


-- Transform PointNot0 into P2
pointToP2 : PointNot0 → P2
pointToP2 (mkPointNot0 x y z p) with ( z ≟ℚ 0ℚ )
... | no z≢0 = 3point (_÷ℚ_ x z {z≢0}) (_÷ℚ_ y z {z≢0})  -- (x,y,1)
... | yes z≡0 with ( y ≟ℚ 0ℚ )
...    | no y≢0 = 2point (_÷ℚ_ x y {y≢0})                            -- (x,1,0)
...    | yes y≡0 with (x ≟ℚ 0ℚ)
...      | no x≢0 = 1point                                                       -- (1,0,0)
...      | yes x≡0 with p                                                         -- (0,0,0) p proves that this case does not occur
...        | xNotZero x≢0 = ⊥-elim (x≢0 x≡0)
...        | yNotZero y≢0 = ⊥-elim (y≢0 y≡0)
...        | zNotZero z≢0 = ⊥-elim (z≢0 z≡0)


-- Transform P2 into Points
P2toPoint : P2 → PointNot0
P2toPoint (3point x y) = mkPointNot0 x y 1ℚ (zNotZero  ( λ () ))
P2toPoint (2point x) = mkPointNot0 x 1ℚ 0ℚ (yNotZero  ( λ () ))
P2toPoint 1point = mkPointNot0 1ℚ 0ℚ 0ℚ (xNotZero  ( λ () ))


-- Define absolut value for rational Numbers
abs : ℚ → ℚ
abs x  with (x <? 0ℚ)
... | false because _ = x
... | true because  _ = - x


-- example for nondecidable (unary) predicate
everywhereFalse : (f : ℕ → Bool) → Set
everywhereFalse f = ∀ n → (f n ≡ false)

decEverywhereFalse : DecidableP everywhereFalse
decEverywhereFalse f = {!!}  -- this is not implementable!


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
absLemma : {x : ℚ} → (x ≢ 0ℚ) → ((abs x) ≢ 0ℚ)
absLemma  =  {!!}


-- Transform (Not0) points into 2SP points
pointTo2SP : PointNot0 → 2SP
pointTo2SP (mkPointNot0 x y z p) with (<-cmpℚ z 0ℚ )

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
2SPtoPoint : 2SP → Point
2SPtoPoint 1point+ = mkPoint 1ℚ 0ℚ 0ℚ
2SPtoPoint 1point- = mkPoint (- 1ℚ) 0ℚ 0ℚ

2SPtoPoint (2point+ x) = mkPoint x 1ℚ 0ℚ
2SPtoPoint (2point- x) = mkPoint x (- 1ℚ) 0ℚ

2SPtoPoint (3point+ x y) = mkPoint x y 1ℚ
2SPtoPoint (3point- x y) = mkPoint x y (- 1ℚ)




-------Geometric duality

-- Reminder: First three lemmata of the paper

-- Lemma 1: If a point p lies on a line L, then the dual of that line dL lies on the dual of that point dp
-- Lemma 2: If two points p1 and p2 lie on a line L, then the intersection of the dual of p1 and p2, is the dual point of line L
-- Lemma 3: If you move a point p on a line L, then the dual of that point rotates arround the dual of L


-- Dual functions

-- Dual Lines to 2SP
dualL2SP : Line  → 2SP
dualL2SP (a x+ b y+1=0) = 3point+ a b


-- Dual 2SP to Line
-- Note: in the current representation for lines, we can only transform 2SP points with z≢0 into lines
-- Probably need to represent lines with 2SP coordinates
dual2SPL : 2SP  → Line
--dual2SPL 1point+ = (1ℚ) x+ (0ℚ) y+1=0
--dual2SPL 1point- = (- 1ℚ) x+ (0ℚ) y+1=0

--dual2SPL (2point+ a) = (a) x+ (1ℚ) y+1=0
--dual2SPL (2point- a) = (a) x+ (- 1ℚ) y+1=0

dual2SPL (3point+ a b) = (a) x+ (b) y+1=0
dual2SPL (3point- a b) = (- a) x+ (- b) y+1=0


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

-- Show that b-value of a line ist not 0
data b≢0 : Line → Set where
  mkb≢0 : ∀ {a b} → (b ≢ 0ℚ) → b≢0 ( a x+ b y+1=0 )



-- Calculate Intersection between lines

{-
intersecXVal : (l1 : Line) → (b≢0 l1)  → (l2 : Line) → (b≢0 l2)  →  ℚ
intersecXVal (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0)  (mkb≢0 b2Not0) =
    let
      numb1≢0 : isFalse ( ℤ.∣ ↥ b1 ∣ ≟ℕ 0)
      numb1≢0 = ≢0⇒num≢0 b1Not0
      
      numb2≢0 : isFalse ( ℤ.∣ ↥ b2 ∣ ≟ℕ 0)
      numb2≢0 = ≢0⇒num≢0 b2Not0
      
   in
      --(b1 - b2) ÷ℚ ((b1 * b2) * ((a1 ÷ b2) - (a1 ÷ b1)))
      _÷ℚ_ (b1 -ℚ b2) ((b1 *ℚ b2) *ℚ ((_÷ℚ_ a1 b2 {n≢0 = numb2≢0}) -ℚ ( _÷ℚ_ a1 b1 {n≢0 = numb1≢0})))  
-}

{-
data haveIntersection : Line  → Line  →  Set where
  base : {a1 b1 a2 b2 : ℚ} → haveIntersection  (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) --need additional constraint for a1,b1,a2,b2 {(a1 ÷ b1) ≃ (a2 ÷ b2) OR b1 ≃ b2 ≃ normalize 0 0} 
-}

{-
XtoYVal : (l : Line) → (b≢0 l) →  ℚ →  ℚ
XtoYVal (a x+ b y+1=0) (mkb≢0 bNot0) val = 
    let
      numb≢0 : isFalse ( ℤ.∣ ↥ b ∣ ≟ℕ 0)
      numb≢0 = ≢0⇒num≢0 bNot0
    in
        _÷ℚ_  ((a *ℚ val) +ℚ (normalize 1 1)) b {n≢0 = numb≢0}
-}

{-
intersecPoint :  (l1 : Line) → (b≢0 l1)  → (l2 : Line) → (b≢0 l2) → Point
intersecPoint (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0)  (mkb≢0 b2Not0) = mkPoint (intersecXVal (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0) (mkb≢0 b2Not0)) (XtoYVal  (a1 x+ b1 y+1=0)  (mkb≢0 b1Not0)   (intersecXVal (a1 x+ b1 y+1=0) (mkb≢0 b1Not0) (a2 x+ b2 y+1=0) (mkb≢0 b2Not0)) ) (normalize 1 1)
-}


-- Find intersection between two lines
-- Case 1: Lines have intersection in ℚ^2
-- Case 2: Lines intersection at infinity 
-- Case 3: Lines are identical : Return any point on the lines as intersection point?
{-
intersec2SP : Line → Line → 2SP
intersec2SP (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) with (a1 ≃ a2)
...                                                                           | true
...                                                                           | true  with (b1 ≃ b2)
...                                                                           | true | true                     -- Case 3
...                                                                           | true | false                     -- Case 1

...                                                                           | false
...                                                                           | false with (b1 ≃ b2)
...                                                                           | false | true                     -- Case1
...                                                                           | false | false                     -- Case 1 or Case 2 if (a1÷a2)≃(b1÷b2) (if directional vectors point in same direction)
-}


-- Calculate if Point is on Line
{-
onLineHelp :  Point → Line → Set
onLineHelp (mkPoint a1 b1 c) (a2 x+ b2 y+1=0) = ((a1 *ℚ a2) +ℚ (b1 *ℚ b2) +ℚ (normalize 1 1) ≡ (normalize 0 0) ) 
-}

{-
data onLineMath : Point → Line → Set → Set where
  mkOnLineMath : ∀ {a1 b1 a2 b2 c}→ (mkPoint a1 b1 c) → (a2 x+ b2 y+1=0) → ((a1 *ℚ a2) +ℚ (b1 *ℚ b2) +ℚ (normalize 1 1) ≡ (normalize 0 0) ) → onLineMath (mkPoint a1 b1 c) → (a2 x+ b2 y+1=0)
-}

{-
data isOnLine : (p : Point) → (l : Line) → (onLineMath p l) → Set where
  --mkOnLine : ∀ {a1 b1 a2 b2} (mkPoint a1 b1 (normalize 1 1)) → (a2 x+ b2 y+1=0) → ((a1 *ℚ a2) +ℚ (b1 *ℚ b2) +ℚ (normalize 1 1) ≃ (normalize 0 0) ) → isOnLine (mkPoint a1 b1 (normalize 1 1))  (a2 x+ b2 y+1=0)
-}



