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
        pi = (pi, pi, pi)
        sin (f,f',f'') = (sin f, f' * cos f, f''') -- WRONG
        cos (f,f',f'') = (cos f, f' * negate sin f, f' * f' * negate cos f) -- WRONG
        exp (f,f',f'') = (exp f, f' * exp f, f''*exp f + f' * f' * exp f)

test1 x = (cos x)^2 + (sin x)^2

-- Part 2
type FunTri a = (Tri a -> Tri a)
-- evalDD is a homomorphism
evalDD :: Transcendental a => FunExp -> FunTri a
evalDD (Const c) = \_ -> (fromRational(toRational c),zero,zero)
evalDD X = \(x, x', x'') -> (x, x', x'')
evalDD (f :+: g) = \t -> (evalDD f t) + (evalDD g t)
evalDD (f :*: g) = \t -> (evalDD f t) * (evalDD g t)
evalDD (Recip f) = \t -> recip t
evalDD (Negate f) = \t -> negate t
evalDD (Sin f) = \t -> sin t
evalDD (Cos f) = \t -> cos t
evalDD (Exp f) = \t -> exp t

waov = (Const 2) :*: X
-- evalDD(e1 * e2) === evalDD(d1) * evalDD(e2)
