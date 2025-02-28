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
        one = (one, one, one)
mulTri :: (Multiplicative a, Additive a) => Tri a -> Tri a -> Tri a
mulTri (a,b,c) (x,y,z) = (a*x,b*y,c*z)

instance (AddGroup a, MulGroup a) => MulGroup (Tri a) where
        recip (a,b,c) = (recip a, recip b, recip c)

instance Transcendental a => Transcendental (Tri a) where
        pi = (pi, pi, pi)
        sin (a,b,c) = (sin a, sin b, sin c)
        cos (a,b,c) = (cos a, cos b, cos c)
        exp (a,b,c) = (exp a, exp b, exp c)

test1 x = (cos x)^2 + (sin x)^2
-- C
evalDD :: Transcendental a => FunExp -> Tri a
evalDD (Const n) = (pain, pain, pain)
        where pain = fromRational (toRational n)-- i hate this
evalDD (e1 :+: e2) = evalDD e1 + evalDD e2
evalDD (e1 :*: e2) = evalDD e1 * evalDD e2
evalDD (Recip e)      =  recip (evalDD e)
evalDD (Negate e)     =  negate (evalDD e)
evalDD (Exp e)        =  exp (evalDD e)      -- = exp . (eval e) !
evalDD (Sin e)        =  sin (evalDD e)
evalDD (Cos e)        =  cos (evalDD e)

-- PART 2
type R = Double
newton :: (Tri R -> Tri R) -> R -> R -> R
newton  f e x = error "TODO"

