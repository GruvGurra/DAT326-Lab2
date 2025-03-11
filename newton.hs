-- Lab Group A2 4
-- Members:
-- Albin Bergh
-- Erik Larsson
-- Ludvig Hammarstedt

import DSLsofMath.Algebra
import DSLsofMath.FunExp
import Prelude hiding (  (+), (-), (*), (/), negate, recip, (^),
                         pi, sin, cos, exp, fromInteger, fromRational)
-- PART 1
-- A
-- P(h) = h is a homomorphism from FunExp to FunSem = R -> R
-- P(h) = h is a homomorphism from FunExp to (R -> R)
-- a homomorphism h: FunExp -> R -> R would preserve structure,
-- meaning that h(op(args)) = op_sem(h(args))
-- since we know all the operations on R, we can rewrite P(h) to 
-- P(h) = all of these are true:  h(a * b) = Mul h(a) h(b)
--                                h(a + b) = Add h(a) h(b)
--                                h(1/a) =   Recip h(a)
--                                h(sin(a))= Sin(h(a))
--                                h(cos(a))= Cos(h(a))
--                                h(e^a)   = Exp h(a)
--  (maybe some operations were forgotten but it doesn't matter in the end)
--
-- So, for h to be a homomorphism, it must satisfy h(op(args)) = op_sem(h(args)) for each constructor in funexp
-- 
-- Now to proving that not P(eval'') is true.
-- If any of the operators don't support the homomorphism, the claim P(eval'') fails and 
-- not P(eval'') becomes true
-- So we just need to show a counterexample
-- eval''= eval (deriv (deriv))
-- So for eval'' to be a homomorphism for multiplication we need the following to be true
-- eval''(a*b) = eval (deriv(deriv(a*b))) = eval(deriv(deriv(a))) * eval(deriv(deriv(b)))
-- let's try eval''(x * x^2)
-- Left hand side: deriv(deriv(x * x^2)) = x^2 + x*2x = x^2+2x^2=3x^2
-- So it becomes: eval(3x^2)
-- Right hand side: deriv(x) = 1. deriv(x^2) = 2x
-- So it becomes eval(1) + eval(2x), which is trivially not equivalent to eval(3x^2) because 
-- it contains a constant 1


-- B
type Tri a = (a, a, a)

instance Additive a => Additive (Tri a) where
        (+) = addTri
        zero = (zero, zero, zero)
addTri :: Additive a => Tri a -> Tri a -> Tri a
addTri (a,b,c) (x,y,z) = (a+x,b+y,c+z)

instance AddGroup a => AddGroup (Tri a) where
        negate (a,b,c) = (negate a, negate b, negate c)

instance (Additive a, Multiplicative a) => Multiplicative (Tri a) where
        (*) = mulTri
        one = (one, zero, zero)
mulTri :: (Multiplicative a, Additive a) => Tri a -> Tri a -> Tri a
mulTri (f,f',f'') (g,g',g'') = (f*g, f'*g+f*g', f''*g + f'*g' + f'*g' + f*g'')
-- (fg)' = f'g+fg'
-- (fg)'' = (f'g+fg')' = (f'g)' + (fg') = (f''g) + (f'g') + (f'g') + (fg'')

instance (AddGroup a, MulGroup a) => MulGroup (Tri a) where
        recip (f,f',f'') = 
                let rf = recip f 
                in (recip f, negate f' * rf*rf, (f'*f'+f'*f' - f * f'') * rf*rf*rf)
                -- (1/f, -f'/f^2, (2f'^2 - f*f'')/f^3)

instance Transcendental a => Transcendental (Tri a) where
        pi = (pi, zero, zero)
        sin (f,f',f'') = (sin f, f' * cos f, f'' * cos f + negate f' * f' * sin f)
        cos (f,f',f'') = (cos f, negate f' * sin f, negate (cos f) * f' * f' + negate (sin f) * f'')
        exp (f,f',f'') = (exp f, f' * exp f, f''*exp f + f' * f' * exp f)

cossintest x = (cos x)^2 + (sin x)^2

type FunTri a = (a  -> Tri a)
evalDD :: Transcendental a => FunExp -> FunTri a
evalDD (Const c) = \_ -> (fromRational(toRational c),zero,zero)
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

-- Part 2
type R = Double
newton :: (Tri R -> Tri R) -> R -> R -> R
newton f e x = iNewton 100 f e x

-- terminate after n iterations
iNewton :: Int -> (Tri R -> Tri R) -> R -> R -> R
iNewton 0 _ _ x = error ("didn't reach anything, ended at " ++ (show x));
iNewton n f e x | abs fx < e = x
                | fx' /= 0 = iNewton (n-1) f e next
                | otherwise = iNewton (n-1) f e (x+e)
                where
                 (fx, fx', _) = f (x,1,0) -- apply f to the identity function at x
                 next = x - (fx / fx')
        
test0 x = x^2
test1 x = x^2 + one
test2 x = sin x
test3 n x y = y^n - (x,0,0)
test4 x = x^3 + x
test5 x = negate (x^2)

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
         (_,fy',fy'') = f (y,1,0)

derTrip :: (Tri R -> Tri R) -> (Tri R -> Tri R)
derTrip f = \t -> let (a,a',a'') = f t in (a', a'', error "Do not touch!")


-- Debug variant of newton that returns a list instead
dnewton :: (Tri R -> Tri R) -> R -> R -> [R]
dnewton f e x = diNewton 100 f e x

-- terminate after n iterations
diNewton :: Int -> (Tri R -> Tri R) -> R -> R -> [R]
diNewton 0 _ _ x = [x];
diNewton n f e x | abs fx < e = [x]
                | fx' /= 0 = x : diNewton (n-1) f e next
                | otherwise = x : diNewton (n-1) f e (x+e)
                where
                 (fx, fx', _) = f (x,1,0)
                 next = x - (fx / fx')
