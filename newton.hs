-- Lab Group A2 4
-- Members:
-- Albin Bergh
-- Erik Larsson
-- Ludvig Hammarstedt

import DSLsofMath.Algebra
import DSLsofMath.FunExp
import Prelude hiding
  ( cos,
    exp,
    fromInteger,
    fromRational,
    negate,
    pi,
    recip,
    sin,
    (*),
    (+),
    (-),
    (/),
    (^),
  )

-- PART 1
-- A
-- P(h) = h is a homomorphism from FunExp to FunSem = R -> R
-- P(h) = h is a homomorphism from FunExp to (R -> R)
-- a homomorphism h: FunExp -> R -> R would preserve structure,
-- since we know all the operations on FunSem (R -> R) and all their corresponding operators on FunExp,
-- P(h) can be rewritten as: Every constructor op called on the argument/arguments args in FunExp should have a corresponding semantic operator
-- in FunSem such that h(op(args)) = op_sem(h(args))
--
--  Expressed in logic this would be
--  P(h) = ∀c ∈ ℝ.     h(Const c) = ConstSem(c)
--       ∧ h(Var)      = VarSem
--       ∧ ∀e1 e2.     h(Add e1 e2) = AddSem(h(e1), h(e2))
--       ∧ ∀e1 e2.     h(Mul e1 e2) = MulSem(h(e1), h(e2))
--       ∧ ∀e.         h(Recip e)  = RecipSem(h(e))
--       ∧ ∀e.         h(Sin e)    = SinSem(h(e))
--       ∧ ∀e.         h(Cos e)    = CosSem(h(e))
--       ∧ ∀e.         h(Exp e)    = ExpSem(h(e))
--      (maybe some operator was forgotten but the idea is still valid, and it doesn't matter for our end result)
--
-- Less abstractly this can also be written as
--  P(h) = ∀c ∈ ℝ.     h(Const c) = Const c     # confusing but the right Const is \_ -> c while the left is a constructor
--       ∧ h(X)      = x
--       ∧ ∀e1 e2.     h(Add e1 e2) = h(e1) + h(e2)
--       ∧ ∀e1 e2.     h(Mul e1 e2) = h(e1) * h(e2)
--       ∧ ∀e.         h(Recip e)  = 1/h(e)
--       ∧ ∀e.         h(Sin e)    = Sin(h(e))
--       ∧ ∀e.         h(Cos e)    = Cos(h(e))
--       ∧ ∀e.         h(Exp e)    = Exp(h(e))   # or alternatively e^(h(e))
--
--
-- Now to proving that not P(eval'') is true.
-- Since P(h) can be interpreted as an AND between all the homomorphisms for the different operators,
-- P(h) becomes false if we can find any operator for which the homomorphism doesn't hold, thus
-- making ¬P(h) true.
-- Let's check for the Mul operator
-- eval'' is a homomorphism for Mul and * iff ∀e1. ∀e2. eval''(Mul e1 e2) = eval''(e1) * eval''(e2)
-- We'll try eval''(Mul X X)  # or more colloquially written x*x
-- eval''(Mul X X) = eval''(X) * eval''(X)
-- Left hand side:
-- eval''(Mul X X) = eval(deriv(deriv(Mul X X))) = eval(deriv(Mul (Const 2) X)) =
-- = eval(Const 2) = 2
-- Right hand side:
-- eval''(X) * eval''(X) = eval(deriv(deriv(X))) * eval(deriv(deriv(X))) =
-- = eval(deriv(Const 1)) * eval(deriv(Const 1)) =
-- = eval(Const 0) * eval(Const 0) = 0
-- Thus eval'' is not a homomorphism from FunExp to FunSem and ¬P(h) is valid
--

-- B
type Tri a = (a, a, a)

instance (Additive a) => Additive (Tri a) where
  (+) = addTri
  zero = (zero, zero, zero)

addTri :: (Additive a) => Tri a -> Tri a -> Tri a
addTri (a, b, c) (x, y, z) = (a + x, b + y, c + z)

instance (AddGroup a) => AddGroup (Tri a) where
  negate (a, b, c) = (negate a, negate b, negate c)

instance (Additive a, Multiplicative a) => Multiplicative (Tri a) where
  (*) = mulTri
  one = (one, zero, zero)

mulTri :: (Multiplicative a, Additive a) => Tri a -> Tri a -> Tri a
mulTri (f, f', f'') (g, g', g'') = (f * g, f' * g + f * g', f'' * g + f' * g' + f' * g' + f * g'')

-- (fg)' = f'g+fg'
-- (fg)'' = (f'g+fg')' = (f'g)' + (fg') = (f''g) + (f'g') + (f'g') + (fg'')

instance (AddGroup a, MulGroup a) => MulGroup (Tri a) where
  recip (f, f', f'') =
    let rf = recip f
     in (rf, negate f' * rf * rf, (f' * f' + f' * f' - f * f'') * rf * rf * rf)

-- (1/f, -f'/f^2, (2f'^2 - f*f'')/f^3)

instance (Transcendental a) => Transcendental (Tri a) where
  pi = (pi, zero, zero)
  sin (f, f', f'') = (sin f, f' * cos f, f'' * cos f + negate f' * f' * sin f)
  cos (f, f', f'') = (cos f, negate f' * sin f, negate (cos f) * f' * f' + negate (sin f) * f'')
  exp (f, f', f'') = (exp f, f' * exp f, f'' * exp f + f' * f' * exp f)

cossintest x = (cos x) ^ 2 + (sin x) ^ 2

type FunTri a = (a -> Tri a)

evalDD :: (Transcendental a) => FunExp -> FunTri a
evalDD (Const c) = \_ -> (fromRational (toRational c), zero, zero)
evalDD X = \x -> (x, one, zero)
evalDD (f :+: g) = \x -> (evalDD f x) + (evalDD g x)
evalDD (f :*: g) = \x -> (evalDD f x) * (evalDD g x)
evalDD (Recip f) = \x -> recip $ evalDD f x
evalDD (Negate f) = \x -> negate $ evalDD f x
evalDD (Sin f) = \x -> sin $ evalDD f x
evalDD (Cos f) = \x -> cos $ evalDD f x
evalDD (Exp f) = \x -> exp $ evalDD f x

-- test2 :: Transcendental a => FunExp -> FunExp -> a -> Bool
-- test2 f g x = evalDD (f * g) x == evalDD (f) x * evalDD (g) x

-- Part 1 D
-- evalDD(f) returns the tuple of functions (f,f',f'') of x
-- let's say we have evalDD(f * g). We want to prove that evalDD(f * g) = evalDD (f) * evalDD (g)
-- through the product rule we can get
-- evalDD(f * g) = (f * g, f'*g + f*g', f''*g + 2*f'*g' + f*g'')
--
-- evalDD(f) * evalDD (g), intuitively this would become (f*g, f'*g', f''*g'')
-- However this does not happen due to how Tri multiplication is defined!
-- Instead it becomes (f,f',f'') * (g,g',g'') =
-- = (f * g, f'*g + f*g', f''*g + 2*f'*g' + f*g'')
-- which is equal to evalDD(f * g)
-- evalDD is thus a homomorphism for multiplication
--
-- Alternatively you could say that evalDD is inherently a homomorphism due to
-- how we defined it.
-- Since our definition of evalDD says that evalDD (f * g) = evalDD(f) * evalDD(g).
-- Which is the requirement for being a homomorphism for multiplication

-- Part 2
type R = Double

newton :: (Tri R -> Tri R) -> R -> R -> R
newton f e x = iNewton 100 f e x

-- terminate after n iterations
iNewton :: Int -> (Tri R -> Tri R) -> R -> R -> R
iNewton 0 _ _ x = error ("didn't reach anything, ended at " ++ show x)
iNewton n f e x
  | abs fx < e = x
  | fx' /= 0 = iNewton (n - 1) f e next
  | otherwise = iNewton (n - 1) f e (x + e)
  where
    (fx, fx', _) = f (x, 1, 0) -- apply f to the identity function at x
    next = x - (fx / fx')

test0 x = x ^ 2

test1 x = x ^ 2 + one

test2 x = sin x

test3 n x y = y ^ n - (x, 0, 0)

test4 x = x ^ 3 + x

test5 x = negate (x ^ 2)

-- PART 3
data Result a = Maximum a | Minimum a | Dunno a deriving (Show, Eq)

optim :: (Tri R -> Tri R) -> R -> R -> Result R
optim f e x
  | abs fy' < e && fy'' < 0 = Maximum y
  | abs fy' < e && fy'' > 0 = Minimum y
  | otherwise = Dunno x
  where
    f' = derTrip f
    y = newton f' e x
    (_, fy', fy'') = f (y, 1, 0)

derTrip :: (Tri R -> Tri R) -> (Tri R -> Tri R)
derTrip f = \t -> let (a, a', a'') = f t in (a', a'', error "Do not touch!")
