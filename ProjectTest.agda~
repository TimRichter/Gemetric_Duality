{-
  Welcome to Agda! :-)

  If you are new to Agda, you could play The HoTT Game, a tutorial for learning
  Agda and homotopy type theory. You can start the game using the "Help" menu
  and then navigating to a file such as 1FundamentalGroup/Quest0.agda. You
  will also need to open the accompanying guide in your browser:
  https://thehottgameguide.readthedocs.io/

  This editor runs on agdapad.quasicoherent.io. Your Agda code is stored on
  this server and should be available when you revisit the same Agdapad session.
  However, absolutely no guarantees are made. You should make backups by
  downloading (see the clipboard icon in the lower right corner).

  C-c C-l          check file
  C-c C-SPC        check hole
  C-c C-,          display goal and context
  C-c C-c          split cases
  C-c C-r          fill in boilerplate from goal
  C-c C-d          display type of expression
  C-c C-v          evaluate expression (normally this is C-c C-n)
  C-c C-a          try to find proof automatically
  C-z              enable Vi keybindings
  C-x C-+          increase font size
  \bN \alpha \to   math symbols

  "C-c" means "<Ctrl key> + c". In case your browser is intercepting C-c,
  you can also use C-o. In case your browser in intercepting C-SPC, you can
  also use C-p. For pasting code into the Agdapad, see the clipboard
  icon in the lower right corner.

  In text mode, use <F10> to access the menu bar, not the mouse.
-}

open import Data.Rational
--open import Data.Integer
--open import Data.Nat


 
-- Define 2D Points
data Point : Set where
  mkPoint :   ℚ  →  ℚ   → Point

-- get X value from Point
getXValP : Point →   ℚ
getXValP (mkPoint x y) = x

-- get Y value from Point
getYValP : Point →   ℚ
getYValP (mkPoint x y) = y


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
dualPL : Point  → Line
dualPL (mkPoint a b) = a x+ b y+1=0

--Line to Point
dualLP : Line  → Point
dualLP (a x+ b y+1=0) =  mkPoint a b



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
-- Problem2: Proof that these Lines have an intersection
intersecXVal : Line  → Line  →  ℚ
intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) = - (b1 - b2) ÷ ((b1 * b2) * ((a1 ÷ b2) - (a1 ÷ b1))) 

-- Idea to solve Problem1: Add a isNotZero function or Type:
-- data isNotZero : ℚ → Set  where
-- base : 

-- Idea to solve Problem2: Two Lines have no intersection Points, if they are parallel, which also means, that their dual Points have the same angle to the origin
-- Note: Equality in Rationals is already defined with the ≃ operator
data haveIntersection : Line  → Line  →  Set where
  base : {a1 b1 a2 b2 : ℚ} → haveIntersection  (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) --need additional constraint for a1,b1,a2,b2 {(a1 ÷ b1) ≃ (a2 ÷ b2) OR b1 ≃ b2 ≃ normalize 0 0} 

-- Get Y Value of Intersection Point out of the X Value
-- Problem1: Prove that b is not 0
XtoYVal : Line →  ℚ →  ℚ
XtoYVal (a x+ b y+1=0) val = ((a * val) + (normalize 1 1)) ÷ b


intersecPoint : Line → Line → Point
intersecPoint (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0) = mkPoint (intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0)) (XtoYVal  (a1 x+ b1 y+1=0) (intersecXVal (a1 x+ b1 y+1=0) (a2 x+ b2 y+1=0)) )
-- Question: can you save parts of the code into variables to make it more readable?
-- If I could put (intersecXVal (a x+ b y+1=0) (a x+ b y+1=0)) into a variable xVal, I could simply write:
-- intersecPoint (a x+ b y+1=0) (a x+ b y+1=0) = mkPoint xVal  (XtoYVal  (a x+ b y+1=0) xVal )


-- Calculate if Point is on Line
data isOnLine : Point → Line → Set where
  base : {a1 b1 a2 b2 : ℚ} → isOnLine (mkPoint a1 b1)  (a2 x+ b2 y+1=0)  --needs additional constraint for a1,b1,a2,b2 {(a1* a2)+(b1*b2)+normalize 1 1 ≃ normalize 0 0} 












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
