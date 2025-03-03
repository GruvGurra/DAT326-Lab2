import DSLsofMath.Algebra
import DSLsofMath.FunExp
import Prelude hiding (  (+), (-), (*), (/), negate, recip, (^),
                         pi, sin, cos, exp, fromInteger, fromRational)
-- PART 1
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
        recip (a,b,c) = (recip a, recip b, recip c)

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
-- through the product rule we can get evalDD(f * g) = 
-- = (f * g, f'*g + f*g', f''*g + 2*f'*g' + f*g'')
--
-- evalDD(f) * evalDD (g), intuitively this would become (f*g, f'*g', f''*g'')
-- However this does not happen due to how Tri multiplication is defined!
-- Instead it becomes (f,f',f'') * (g,g',g'') =
-- = (f * g, f'*g + f*g', f''*g + 2*f'*g' + f*g'')
-- evalDD is thus a homomorphism for multiplication

-- Part 2
type R = Double
newton :: (Tri R -> Tri R) -> R -> R -> [R]
newton f e x = iNewton 100 f e x

-- terminate after n iterations
iNewton :: Int -> (Tri R -> Tri R) -> R -> R -> [R]
iNewton 0 _ _ x = [x];
iNewton n f e x | abs fx < e = [x]
                | fx' /= 0 = x : iNewton (n-1) f e next
                | otherwise = x : iNewton (n-1) f e (x+e)
                where
                 (fx, fx', _) = f (x,1,0)
                 next = x - (fx / fx')
        
test0 x = x^2
test1 x = x^2 - one
test2 x = sin x
test3 n x y = y^n - (x,0,0)

data Result a = Maximum a | Minimum a | Inflection a | Dunno a deriving (Show, Eq)
-- PART 3, THE FINAL BOSS
optim :: (Tri R -> Tri R) -> R -> R -> Result R
optim f e x
        | abs y < e && abs fy'' < e && (fyL'' * fyR'') < 0 = Inflection y
        | fy'' < 0 = Maximum y
        | fy'' > 0 = Minimum y
        | otherwise = Dunno x
        where
         woo = derTrip f
         y = last $ newton woo e x
         (_,_,fy'') = f (y,1,0)
         (_,_,fyL'') = f (y-e,1,0)
         (_,_,fyR'') = f(y+e,1,0)

derTrip :: (Tri R -> Tri R) -> (Tri R -> Tri R)
derTrip f = \t -> let (a,a',a'') = f t in (a', a'', error "!!!")
