import DSLsofMath.Algebra
import DSLsofMath.FunExp
import Prelude hiding (  (+), (-), (*), (/), negate, recip, (^),
                         pi, sin, cos, exp, fromInteger, fromRational)
-- PART 1
-- B
type Tri a = (a, a, a)

instance Additive a => Additive (Tri a) where
        (+) = error "TODO"
        zero = error "TODO"
instance Additive a => AddGroup (Tri a) where
        negate = error "TODO"
instance Multiplicative a => Multiplicative (Tri a) where
        (*) = error "TODO"
        one = error "TODO"
instance (Additive a, Multiplicative a) => MulGroup (Tri a) where
        recip = error "TODO"

instance Transcendental a => Transcendental (Tri a) where
        pi = error "TODO"
        sin = error "TODO"
        cos = error "TODO"
        exp = error "TODO"

