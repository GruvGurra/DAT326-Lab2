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
        (*) = mulTri -- TODO: Maybe not how we're supposed to multiply triples
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

test1 x = (cos x)^2 + (sin x)^2

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
