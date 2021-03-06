{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Rank2Types          #-}

{- |
   Copyright  : Copyright (C) 2008-2009 Barak A. Pearlmutter and Jeffrey Mark Siskind
   License    : BSD3

   Maintainer : bjorn.buckwalter@gmail.com
   Stability  : experimental
   Portability: GHC only?

Forward Automatic Differentiation via overloading to perform
nonstandard interpretation that replaces original numeric type with
corresponding generalized dual number type.

Credits:

Authors: Copyright 2008,
Barak A. Pearlmutter (<barak@cs.nuim.ie>) &
Jeffrey Mark Siskind (<qobi@purdue.edu>)

Work started as stripped-down version of higher-order tower code
published by Jerzy Karczmarczuk (<jerzy.karczmarczuk@info.unicaen.fr>)
which used a non-standard standard prelude.

Initial perturbation-confusing code is a modified version of
<http://cdsmith.wordpress.com/2007/11/29/some-playing-with-derivatives/>

Tag trick, called \"branding\" in the Haskell community, from
Bj&#246;rn Buckwalter (<bjorn.buckwalter@gmail.com>)
<http://thread.gmane.org/gmane.comp.lang.haskell.cafe/22308/>

Notes:

Each invocation of the differentiation function introduces a distinct
perturbation, which requires a distinct derivative-carrying number
type.  In order to prevent these from being confused, tagging, called
branding in the Haskell community, is used.  This seems to prevent
perturbation confusion, although it would be nice to have an actual
proof of this.  The technique does require adding invocations of lift
at appropriate places when nesting is present, and degrades modularity
by exposing "forall" types in type signatures.

-}

{-

The \"pass in a lifter\" approach, discussed in the HOSC paper, was
rediscovered and implemented by David Roundy (<droundy@darcs.net>)
<http://thread.gmane.org/gmane.comp.lang.haskell.cafe/22308>
Unfortunately this would preclude writing in a natural style, and
is therefore not used here.  It however could be combined with
tagging to allow dynamic nesting, if the type system would allow.

-}


-- Forward Automatic Differentiation
module Numeric.FAD (
            -- * Derivative Towers: Higher-Order Generalized Dual Numbers
            Tower, lift, primal,

            -- * First-Order Differentiation Operators
            -- $fodo
            diffUU, diffUF, diffMU, diffMF,
            diff2UU, diff2UF, diff2MU, diff2MF,
            
            -- * Higher-Order Differentiation Operators
            -- $hodo
            diffsUU, diffsUF, diffsMU, diffsMF,
            diffs0UU, diffs0UF, diffs0MU, diffs0MF,
            
            -- * Common access patterns
            diff, diff2, diffs, diffs0, grad, jacobian,

            -- * Optimization Routines
            zeroNewton, inverseNewton, fixedPointNewton, extremumNewton,
            argminNaiveGradient,

            -- * unlift lifted functions
            primalUU, primalUF, primalFU, primalFF,

            -- * Miscellaneous
            taylor, taylor2)
where

import Data.List (transpose)
import Data.Foldable (Foldable)
import qualified Data.Foldable (all)
import List.Util (zipWithDefaults, indexDefault)
import Data.Function (on)

-- To Do:

--  Add some more optimization routines
--  Add some examples
--  Add pointers into literature
--  Fix complex number issues (requires changes to standard prelude)
--  Optimize for efficiency
--  Address [x..] bug, see below

-- Notes:

-- This package implements forward automatic differentiation,
-- generalized to produce not only first derivatives, but a tower of
-- all higher-order derivatives.  This is done by replacing a base (or
-- "primal") numberic type by a numeric type that holds the primal value
-- but also carries along the derivative(s).  If we produced only
-- first derivatives, the augmented type would be a "Dual Number".
-- And Dual Numbers are tangent-vector bundles, in the terminology of
-- differential geometry.  For the this reason, we call the accessor
-- for the first derivative "tangent".  We also sometimes refer to the
-- augmented numbers as "bundles", since they bundle together a primal
-- value and some derivative information.

-- The multivariate case is handled as a list on inputs, but an
-- arbitrary functor on outputs.  This asymmetry is because Haskell
-- provides fmap but not fzipWith.

-- The derivative towers can be truncated.  Care is taken to preserve
-- said trunction whenever possible.


-- Other quirks:

--  would need diffUFF for f:R->[[R]] and diffUFFF for f:R->[Maybe [R]], etc.

--  type signature of diff stuff contaminates diff-using stuff, ick


-- Some care has been taken to ensure that correct interoperation with
-- complex numbers.  Particular care must be taken with the
-- non-analytic functions, namely abs and signum.  These are not
-- properly differentiable over the complex domain, but they do admit
-- directional derivatives (push-forwards) where both the primal and
-- tangents are complex.  Unfortunately the Haskell numeric system is
-- modularized in a fashion that appears to make this impossible to
-- express.  Instead, we detect the situation and handle it
-- appropriately.

-- Digression: the reason for this difficulty.

-- The relationship of interest, valid for both real and complex
-- valued x, is:

--   x = (abs x) * (signum x)

-- This gives rise to division in the formulas for abs and signum when
-- x is complex.  For real x, (signum x) = 1/(signum x), so the
-- division can be replaced by multiplication.  But not in the complex
-- case.  And unfortunately, abs & signum are defined for Num, which
-- does not have division.

-- The "right" solution would be to have signumRecip defined for Num,
-- where (signumRecip x) * (signum x) = 1.  This would allow things to
-- be defined so as to be correct in the case of complex numbers
-- without using division, and would be trivial in the real case where
-- signum x = signumRecip x.  Moreover (magnitude (signum z)) == 1, so
-- we could use signumRecip = conjugate . signum for complex numbers.
-- Except that conjugate is defined only for complex numbers, which is
-- strange since it would just be the identity for real numbers.


-- | The 'Tower' type is a concrete representation of a higher-order
-- Dual number, meaning a number augmented with a tower of
-- derivatives.  These generalize the Dual numbers of Clifford (1873),
-- which hold only a first derivative.  They can be converted to
-- formal power series via division by the sequence of factorials.
newtype Tower tag a = Tower [a] deriving Show

-- Injectors and accessors for derivative towers

-- | The 'lift' function injects a primal number into the domain of
-- derivative towers, with a zero tower.  If generalized dual numbers
-- were a monad, 'lift' would be 'return'.
lift :: (Eq a, Num a) => a -> Tower tag a
lift = (`bundle` zero)

-- | The 'bundle' function takes a primal number and a derivative
-- tower and returns a derivative tower with the given tower shifted
-- up one and the new primal inserted.
--
-- Property: @x = bundle (primal x) (tangentTower x)@
bundle :: (Eq a, Num a) => a -> Tower tag a -> Tower tag a
bundle x0 x' = toTower (x0:fromTower x')
-- The following forces its second argument's structure, which is very bad:
-- bundle x0 (Tower xs) = toTower (x0:xs)

-- | The zero element of a Tower Number tower algebra
zero :: (Eq a, Num a) => Tower tag a
zero = toTower []

-- | The 'apply' function applies a function to a number lifted from
-- the primal domain to the derivative tower domain, with unit
-- derivative, thus calculating the generalized push-forward, in the
-- differential geometric sense, of the given function at the given
-- point.
apply :: (Eq a, Num a) => (Tower tag a -> b) -> a -> b
apply = (. (`bundle` 1))

-- | The 'towerElt' function finds the i-th element of a derivative
-- | tower, where the 0-th element is the primal value, the 1-st
-- | element is the first derivative, etc.
towerElt :: (Eq a, Num a) => Int -> Tower tag a -> a
towerElt i (Tower xs) = xs !!!! i
    where (!!!!) = indexDefault (Just 0)

-- | The 'fromTower' function converts a derivative tower to a list of
-- values with the i-th derivatives, i=0,1,..., possibly truncated
-- when all remaining values in the tower are zero.
fromTower :: Tower tag a -> [a]
fromTower (Tower xs) = xs

-- | The 'toTower' function converts a list of numbers into a
-- | derivative tower.
toTower :: [a] -> Tower tag a
toTower = Tower

-- | The 'primal' function finds the primal value from a derivative
-- | tower.  The inverse of 'lift'.
primal :: (Eq a, Num a) => Tower tag a -> a
primal = towerElt 0

-- | The 'tangent' function finds the tangent value of a derivative
-- | tower, i.e., the first-order derivative.
tangent :: (Eq a, Num a) => Tower tag a -> a
tangent = towerElt 1

-- | The 'tangentTower' function finds the entire tower of tangent
-- values of a derivative tower, starting at the 1st derivative.  This
-- is equivalent, in an appropriate sense, to taking the first
-- derivative.
tangentTower :: (Eq a, Num a) => Tower tag a -> Tower tag a
tangentTower (Tower []) = zero
tangentTower (Tower (_ : x')) = toTower x'

-- | The 'liftA1' function lifts a scalar numeric function from a base
-- numeric type to a function over derivative towers.  Takes the
-- primal function and the derivative function as arguments.  The
-- derivative function should return a scalar.
--
-- EXAMPLE: @liftA1 sin cos@
liftA1 :: (Eq a, Num a) =>
         (a -> a)
             -> (Tower tag a -> Tower tag a)
             -> Tower tag a -> Tower tag a

liftA1 f = (liftA1_ f) . const

-- | The 'liftA2' function lifts a binary numeric function from a base
-- numeric type to a function over derivative towers.  Takes the
-- primal function and the derivative function as arguments.  The
-- derivative function should return the Jacobian matrix,
-- representated as a pair.
--
-- EXAMPLE: @liftA2 (*) (\\x y -> (y,x))@
liftA2 :: (Eq a, Num a) =>
         (a -> a -> a)
             -> (Tower tag a -> Tower tag a -> (Tower tag a, Tower tag a))
             -> Tower tag a -> Tower tag a -> Tower tag a

liftA2 f = (liftA2_ f) . const

-- | The 'liftA1_' function lifts a scalar numeric function, like
-- 'liftA1', except the the derivative function is given access to the
-- output value.  This eases recursion and reuse.
--
-- EXAMPLE: @liftA1_ exp const@
liftA1_ :: (Eq a, Num a) =>
         (a -> a)
             -> (Tower tag a -> Tower tag a -> Tower tag a)
             -> Tower tag a -> Tower tag a

liftA1_ f df x = z
    where z = bundle (f (primal x)) (tangentTower x * df z x)

-- | The 'liftA2_' function lifts a binary numeric function, like
-- 'liftA2', except the the derivative function is given access to the
-- output value.  This eases recursion and reuse.
--
-- EXAMPLE: @liftA2_ (**) (\z x y -> (y*z\/x, z*log x))@
liftA2_ :: (Eq a, Num a) =>
         (a -> a -> a)
             -> (Tower tag a
                     -> Tower tag a
                     -> Tower tag a
                     -> (Tower tag a, Tower tag a))
             -> Tower tag a -> Tower tag a -> Tower tag a

liftA2_ f df x y = z
    where z = bundle z0 z'
          z0 = f (primal x) (primal y)
          z' = tangentTower x * dfdx + tangentTower y * dfdy
          (dfdx, dfdy) = df z x y

-- | The 'liftA1disc' function lifts a scalar function with numeric
-- input and discrete output from the primal domain into the
-- derivative tower domain.
liftA1disc :: (Eq a, Num a) => (a -> c) -> Tower tag a -> c
liftA1disc = (. primal)

-- | The 'liftA2disc' function lifts a binary function with numeric
-- inputs and discrete output from into the derivative tower domain.
liftA2disc :: (Eq a, Num a) => (a -> a -> b) -> Tower tag a -> Tower tag a -> b
liftA2disc = (`on` primal)

-- | The 'liftLin' function lifts a scalar linear function from the
-- primal domain into the derivative tower domain.  WARNING: The
-- restriction to linear functions is not enforced by the type system.
liftLin :: (a -> b) -> Tower tag a -> Tower tag b
liftLin f = toTower . map f . fromTower

-- | The 'liftLin2' function lifts a binary linear function from the
-- primal domain into the derivative tower domain.  WARNING 1:  The
-- restriction to linear functions is not enforced by the type system.
-- WARNING 2:  Binary linear means linear in both arguments together,
-- not bilinear.
liftLin2 :: (Eq a, Num a, Eq b, Num b) =>
            (a -> a -> b) -> Tower tag a -> Tower tag a -> Tower tag b
liftLin2 f = (toTower.) . (zipWithDefaults f 0 0 `on` fromTower)

-- Numeric operations on derivative towers.

instance (Eq a, Num a) => Num (Tower tag a) where
    (+)			= liftLin2 (+)
    (-)			= liftLin2 (-)
    (*) (Tower []) _	= zero
    (*) _ (Tower [])	= zero
    (*) x y		= liftA2 (*) (flip (,)) x y
    negate		= liftLin negate
    abs = liftA1 abs
          (\x->let x0 = primal x
               in
                 if x0==0
                 then error "not differentiable: abs(0)"
                 else if notComplex x0 -- would be good to verify nonComplex tower
                      then lift (signum x0)
                      else error "not differentiable: abs(complex)")
    signum = liftA1 signum
             (\x->let x0 = primal x
                  in
                    if x0==0
                    then error "not differentiable: signum(0)"
                    else if notComplex x0 -- would be good to verify nonComplex tower
                         then zero
                         else error "not differentiable: signum(complex)")
    fromInteger	= lift . fromInteger

notComplex x = s == 0 || s == 1 || s == -1
    where s = signum x

-- Here is another problem with supporting complex numbers.  This is a
-- show stopper for doing transparent forward AD on functions that are
-- explicitly over complex numbers.

-- The following will not work:

-- instance Complex a => Complex (Tower tag a) where
--     realPart   = liftLin realPart
--     imagPart   = liftLin imagPart
--     conjugate  = liftLin conjugate
--     ...

-- This fails because Complex in the standard prelude is not abstract
-- enough.  It is impossible to make (Tower (Complex a)) a complex
-- number; the system can only do (Complex (Tower a)).  This makes it
-- impossible to take derivatives of complex functions, i.e., analytic
-- functions, using the same API as non-complex functions.

instance (Eq a, Fractional a) => Fractional (Tower tag a) where
    recip		= liftA1_ recip (const . negate . (^2))
    fromRational	= lift . fromRational

instance (Eq a, Floating a) => Floating (Tower tag a) where
    pi		= lift pi
    exp		= liftA1_ exp const
    sqrt	= liftA1_ sqrt (const . recip . (2*))
    log		= liftA1 log recip
    -- Bug on zero base, e.g., diffUU (**2) 0 = NaN, which is wrong.
    -- Need special cases to bypass avoidable division by 0 and log 0.
    -- Here are some untested ideas:
    --  (**) x (Tower []) = 1
    --  (**) x y@(Tower [y0]) = liftA1 (**y0) ((y*) . (**(y-1))) x
    (**)	= liftA2_ (**) (\z x y -> (y*z/x, z*log x))
    sin		= liftA1 sin cos
    cos		= liftA1 cos (negate . sin)
    tan         = liftA1 tan (recip . (^2) . cos)
    asin	= liftA1 asin (recip . sqrt . (1-) . (^2))
    acos	= liftA1 acos (negate . recip . sqrt . (1-) . (^2))
    atan	= liftA1 atan (recip . (1+) . (^2))
    sinh	= liftA1 sinh cosh
    cosh	= liftA1 cosh sinh
    asinh	= liftA1 asinh (recip . sqrt . (1+) . (^2))
    acosh	= liftA1 acosh (recip . sqrt . (-1+) . (^2))
    atanh	= liftA1 atanh (recip . (1-) . (^2))

-- The RealFloat instance which follows is mainly to get atan2 to
-- work, which is by inheritance.

-- Note that atan2 is important in numeric code: to a first
-- approximation, no program should ever use atan, but always atan2
-- instead.  In particular it is virtually impossible for "atan (y/x)"
-- to be correct; "atan2 y x" is almost certainly what is really meant.

{-

 Warning!  If we do not give a special definition of atan2 below,
 instead allowing it to default, there are errors at branch points, in
 particular at (atan2 1 0).  These occur with "probability zero"
 around the unit circule, so you might not notice them with random
 testing.

 *Numeric.FAD> let shouldBeOne a = diff (\a->atan2 (sin a) (cos a)) a

 *Numeric.FAD> shouldBeOne (pi/2-1e-12)
 1.0

 *Numeric.FAD> shouldBeOne (pi/2)
 1.0

 *Numeric.FAD> shouldBeOne (pi/2+1e-12)
 1.0

 *Numeric.FAD> diff shouldBeOne (pi/2-1e-12)
 0.0

 *Numeric.FAD> diff shouldBeOne (pi/2)
 -4.0                          -- <<<<<<<<<<<<<<<< BUG IS HERE

 *Numeric.FAD> diff shouldBeOne (pi/2+1e-12)
 0.0

-}

instance (RealFloat a, RealFrac a) => RealFloat (Tower tag a) where
    floatRadix		= liftA1disc floatRadix
    floatDigits		= liftA1disc floatDigits
    floatRange	 	= liftA1disc floatRange
    decodeFloat		= liftA1disc decodeFloat
    encodeFloat n i	= bundle (encodeFloat n i)
                          (error "not differentiable: encodeFloat")
    scaleFloat i	= liftA1_ (scaleFloat i) (/)
    isNaN		= liftA1disc isNaN
    isInfinite		= liftA1disc isInfinite
    isDenormalized	= liftA1disc isDenormalized
    isNegativeZero	= liftA1disc isNegativeZero
    isIEEE		= liftA1disc isIEEE
    atan2		= liftA2 atan2 (\x y->let r = recip (x^2+y^2) in (y*r, -x*r))

instance RealFrac a => RealFrac (Tower tag a) where
    properFraction x = (z1, (bundle z2 (tangentTower x)))
        where (z1,z2) = properFraction (primal x)
    truncate	= liftA1disc truncate
    round	= liftA1disc round
    ceiling	= liftA1disc ceiling
    floor	= liftA1disc floor

instance Real a => Real (Tower tag a) where
    -- this would be a bug, as it would discard the tower:
    --  toRational	= liftA1disc toRational
    toRational (Tower [])   = 0
    toRational (Tower [x0]) = toRational x0
    toRational _            = error "toRational of Dual number with tower"

instance (Eq a, Num a) => Eq (Tower tag a) where
    (==)	= liftA2disc (==)

instance (Ord a, Eq a, Num a) => Ord (Tower tag a) where
    compare	= liftA2disc compare



{-
  The [x..] bug:

  > diff (\x->[x]   !! 0) 7
  1                                   -- Correct

  > diff (\x->[x..] !! 0) 7
  0                                   -- Incorrect!
-}

instance (Enum a, Eq a, Num a, Ord a) => Enum (Tower tag a) where
    succ	= liftA1 succ (const 1)
    pred	= liftA1 pred (const 1)
    -- this would be a bug, as it would discard the tower:
    --  fromEnum	= liftA1disc fromEnum
    fromEnum (Tower [])   = 0
    fromEnum (Tower [x0]) = fromEnum x0
    fromEnum _		  = error "fromEnum of Dual number with tower"
    toEnum		  = lift . toEnum
    enumFrom		  = iterate succ			-- [n..]
    enumFromThen n n'	  = iterate (+(n'-n)) n			-- [n,n'..]
    enumFromTo n m	  = takeWhile (<=m) (enumFrom n)	-- [n..m]
    enumFromThenTo n n' m					-- [n,n'..m]
        = takeWhile (if n' >= n then (<= m) else (>= m)) (enumFromThen n n')

instance Integral a => Integral (Tower tag a) where
    -- this would be a bug, as it would discard the tower:
    --  toInteger	= liftA1disc toInteger
    toInteger (Tower [])   = 0
    toInteger (Tower [x0]) = toInteger x0
    toInteger _		   = error "toInteger of Dual number with tower"
    -- div, mod, etc., not implemented: not in general differentiable
    quotRem a b = error "quotRem of Dual number"

-- First-Order Differentiation Operators

{- $fodo
These have two-letter suffices for the arity of the input and
output of the passed functions: U for univariate, meaning a number,
M for multivariate, meaning a list of numbers.

When the input is multivariate a directional derivative is
calculated; this requires an additional \"direction\" parameter.  The
multivariate case is treated as a list (on input) and as a functor
of arbitrary shape, which includes lists as a special case, on
output.

Naming convention:

[@diff{U\/M}{U\/F}@] Derivative-taking operators that return a
    primal/first-derivative pair, for all combinations of
    scalar/nonscalar input & output

[@diff2{U\/M}{U\/F}@] Derivative-taking operators that calculate a
    (primal, first-derivative) pair, for all combinations of
    scalar/nonscalar input & output

-}

-- Perhaps these should be named things like
--   AD.Forward.D.uu
--   AD.Forward.D.um
--   AD.Forward.grad
--   AD.Forward.jacobian


-- | The 'diffUU' function calculates the first derivative of a
-- scalar-to-scalar function.
diffUU :: (Eq a, Num a, Eq b, Num b) => (forall tag. Tower tag a -> Tower tag b) -> a -> b
diffUU f = tangent . apply f

-- | The 'diffUF' function calculates the first derivative of
-- scalar-to-nonscalar function.
diffUF :: (Eq a, Num a, Eq b, Num b, Functor f) =>
          (forall tag. Tower tag a -> f (Tower tag b)) -> a -> f b
diffUF f = fmap tangent . apply f

-- | The 'diffMU' function calculate the product of the Jacobian of a
-- nonscalar-to-scalar function with a given vector.  Aka: directional
-- derivative.
diffMU :: (Eq a, Num a, Eq b, Num b) =>
          (forall tag. [Tower tag a] -> Tower tag b) -> [a] -> [a] -> b
diffMU f xs = tangent . f . zipWithBundle xs

-- | The 'diffMF' function calculates the product of the Jacobian of a
-- nonscalar-to-nonscalar function with a given vector.  Aka:
-- directional derivative.
diffMF :: (Eq a, Num a, Eq b, Num b, Functor f) =>
          (forall tag. [Tower tag a] -> f (Tower tag b)) -> [a] -> [a] -> f b
diffMF f xs = fmap tangent . f . zipWithBundle xs


-- | The 'diff2UU' function calculates the value and derivative, as a
-- pair, of a scalar-to-scalar function.
diff2UU :: (Eq a, Num a, Eq b, Num b) => (forall tag. Tower tag a -> Tower tag b) -> a -> (b,b)
diff2UU f = dualToPair . apply f

-- | The 'diffUF2' function calculates the value and derivative, as a
-- pair, of a scalar-to-nonscalar function.
diff2UF :: (Eq a, Num a, Eq b, Num b, Functor f) =>
           (forall tag. Tower tag a -> f (Tower tag b)) -> a -> (f b, f b)
diff2UF f = fdualsToPair . apply f

-- | The 'diffMU2' function calculates the value and directional
-- derivative, as a pair, of a nonscalar-to-scalar function.
diff2MU :: (Eq a, Num a, Eq b, Num b) =>
           (forall tag. [Tower tag a] -> Tower tag b) -> [a] -> [a] -> (b,b)
diff2MU f xs = dualToPair . f . zipWithBundle xs

-- | The 'diffMF2' function calculates the value and directional
-- derivative, as a pair, of a nonscalar-to-nonscalar function.
diff2MF :: (Eq a, Num a, Eq b, Num b, Functor f) =>
           (forall tag. [Tower tag a] -> f (Tower tag b))
               -> [a] -> [a] -> (f b, f b)
diff2MF f xs = fdualsToPair . f . zipWithBundle xs

-- Some utility functions and classes for doing transposes and padding
-- of outputs.  Variants handle things that are not shaped like lists,
-- but are pretty close.

zeroPad :: (Eq a, Num a) => [a] -> [a]
zeroPad = (++ repeat 0)

zeroPadF :: (Eq a, Num a, Functor f) => [f a] -> [f a]
zeroPadF fxs@(fx:_) = fxs ++ repeat (fmap (const 0) fx)

-- | The 'transposePad' function is like Data.List.transpose except
-- that it fills in missing elements with 0 rather than skipping them.
-- It can give a ragged output to a ragged input, but the lengths in
-- the output are nonincreasing.

transposePad :: (Eq a, Num a) => [[a]] -> [[a]]
transposePad = foldr (zipWithDefaults (:) 0 []) []

-- | The 'transposePadF' function is like Data.List.transpose except
-- that it fills in missing elements with 0 rather than skipping them,
-- and is generalized to Foldable Functors.  Unlike transposePad, it
-- gives a "square" output to a ragged input.

transposePadF :: (Eq a, Num a, Foldable f, Functor f) => f [a] -> [f a]
transposePadF fx =
    if Data.Foldable.all null fx
    then []
    else (fmap (!!!!0) fx) : (transposePadF (fmap (drop 1) fx))
    where (!!!!) = indexDefault (Just 0)

-- The 'transposeF' function transposes w/ infinite zero row padding.

-- transposeF :: (Eq a, Num a, Functor f) => f [a] -> [f a]
-- transposeF = transF . fmap zeroPad
--     where transF x = (fmap (!!0) x) : (transF $ fmap (drop 1) x)


{- $hodo

Naming convention:

[@diffs{U\/M}{U\/F}@]: Derivative-taking operators that return a list
    [primal, first-derivative, 2nd-derivative, ...], for all
    combinations of scalar/nonscalar input & output.

-}

-- | The 'diffsUU' function calculates a list of derivatives of a
-- scalar-to-scalar function. The 0-th element of the list is the
-- primal value, the 1-st element is the first derivative, etc.
diffsUU :: (Eq a, Num a, Eq b, Num b) => (forall tag. Tower tag a -> Tower tag b) -> a -> [b]
diffsUU f = fromTower . apply f

-- | The 'diffsUF' function calculates an infinite list of derivatives
-- of a scalar-to-nonscalar function.  The 0-th element of the list is
-- the primal value, the 1-st element is the first derivative, etc.
diffsUF :: (Eq a, Num a, Eq b, Num b, Functor f, Foldable f) =>
           (forall tag. Tower tag a -> f (Tower tag b))
               -> a -> [f b]
diffsUF f = transposePadF . fmap fromTower . apply f

-- | The 'diffsMU' function calculates an infinite list of derivatives
-- of a nonscalar-to-scalar function.  The 0-th element of the list is
-- the primal value, the 1-st element is the first derivative, etc.
-- The input is a (possibly truncated) list of the primal, first
-- derivative, etc, of the input.
diffsMU :: (Eq a, Num a, Eq b, Num b) =>
           (forall tag. [Tower tag a] -> Tower tag b)
               -> [[a]] -> [b]
diffsMU f = fromTower . f . map toTower . transposePad

-- | The 'diffsMF' function calculates an infinite list of derivatives
-- of a nonscalar-to-nonscalar function.  The 0-th element of the list
-- is the primal value, the 1-st element is the first derivative, etc.
-- The input is a (possibly truncated) list of the primal, first
-- derivative, etc, of the input.
diffsMF :: (Eq a, Num a, Eq b, Num b, Functor f, Foldable f) =>
           (forall tag. [Tower tag a] -> f (Tower tag b))
               -> [[a]] -> [f b]
diffsMF f = transposePadF . fmap fromTower . f . map toTower . transposePad

-- Variants of diffsXX names diffs0XX, which zero-pad the output list

-- | The 'diffs0UU' function is like 'diffsUU' except the output is zero padded.
diffs0UU :: (Eq a, Num a, Eq b, Num b) =>
            (forall tag. Tower tag a -> Tower tag b)
                -> a -> [b]
diffs0UU f = zeroPad . diffsUU f

-- | The 'diffs0UF' function is like 'diffsUF' except the output is zero padded.
diffs0UF :: (Eq a, Num a, Eq b, Num b, Functor f, Foldable f) =>
            (forall tag. Tower tag a -> f (Tower tag b))
                -> a -> [f b]
diffs0UF f = zeroPadF . diffsUF f

-- | The 'diffs0MU' function is like 'diffsMU' except the output is zero padded.
diffs0MU :: (Eq a, Num a, Eq b, Num b) =>
            (forall tag. [Tower tag a] -> Tower tag b)
                -> [[a]] -> [b]
diffs0MU f = zeroPad . diffsMU f

-- | The 'diffs0MF' function is like 'diffsMF' except the output is zero padded.
diffs0MF :: (Eq a, Num a, Eq b, Num b, Functor f, Foldable f) =>
            (forall tag. [Tower tag a] -> f (Tower tag b))
                -> [[a]] -> [f b]
diffs0MF f = zeroPadF . diffsMF f

-- Common access patterns

-- | The 'diff' function is a synonym for 'diffUU'.
diff :: (Eq a, Num a, Eq b, Num b) =>
        (forall tag. Tower tag a -> Tower tag b)
            -> a -> b
diff = diffUU

-- | The 'diff2' function is a synonym for 'diff2UU'.
diff2 :: (Eq a, Num a, Eq b, Num b) =>
         (forall tag. Tower tag a -> Tower tag b)
             -> a -> (b, b)
diff2 = diff2UU

-- | The 'diffs' function is a synonym for 'diffsUU'.
diffs :: (Eq a, Num a, Eq b, Num b) =>
         (forall tag. Tower tag a -> Tower tag b)
             -> a -> [b]
diffs = diffsUU

-- | The 'diffs0' function is a synonym for 'diffs0UU'.
diffs0 :: (Eq a, Num a, Eq b, Num b) =>
          (forall tag. Tower tag a -> Tower tag b)
              -> a -> [b]
diffs0 = diffs0UU

-- | The 'grad' function calculates the gradient of a
-- nonscalar-to-scalar function, using n invocations of forward AD,
-- where n is the input dimmensionality.  NOTE: this is O(n)
-- inefficient as compared to reverse AD.
grad :: (Eq a, Num a, Eq b, Num b) =>
        (forall tag. [Tower tag a] -> Tower tag b)
            -> [a] -> [b]
-- grad f = head . jacobian ((:[]) . f) -- Robot face, robot claw!
grad f xs = map (diffMU f xs) (identity xs)

-- | The 'jacobian' function calcualtes the Jacobian of a
-- nonscalar-to-nonscalar function, using n invocations of forward AD,
-- where n is the input dimmensionality.
jacobian :: (Eq a, Num a, Eq b, Num b) =>
            (forall tag. [Tower tag a] -> [Tower tag b])
                -> [a] -> [[b]]
jacobian f xs = transpose $ map (diffMF f xs) (identity xs)

-- | The 'dualToPair' function converts a tower of derivatives to a
-- pair of the primal and the first derivative.
dualToPair :: (Eq a, Num a) => Tower tag a -> (a,a)
dualToPair x = (primal x, tangent x)

-- | The 'fdualsToPair' function converts a functor of derivative
-- towers to a pair: one with the functor holding the primal values,
-- the other with the functor holding the first derivatives.
fdualsToPair :: (Eq a, Num a, Functor f) => f (Tower tag a) -> (f a, f a)
fdualsToPair fxs = (fmap primal fxs, fmap tangent fxs)

-- | The 'zipWithBundle' function zip two lists of numbers into a list
-- of derivative towers with the given primal values andd first
-- derivatives.  The two lists should have the same length.
zipWithBundle :: (Eq a, Num a) => [a] -> [a] -> [Tower tag a]
zipWithBundle = zipWithDefaults (\x0 x1->toTower [x0,x1]) e e
    where e = error "zipWithBundle arguments, lengths differ"

-- | The 'primalUU' function lowers a function over dual numbers to a
-- function in the primal domain, where the function is
-- scalar-to-scalar.
primalUU :: (Eq a, Num a, Eq b, Num b) =>
           (forall tag. Tower tag a -> Tower tag b) -> a -> b
primalUU f = primal . f . lift

-- | The 'primalUF' function lowers a function over dual numbers to a
-- function over primals, where the function is scalar-to-nonscalar.
primalUF :: (Eq a, Num a, Eq b, Num b, Functor fb) =>
            (forall tag. Tower tag a -> fb (Tower tag b))
                -> a -> (fb b)
primalUF f = fmap primal . f . lift

-- | The 'primalFU' function lowers a function over dual numbers to a
-- function over primals where the function is nonscalar-to-scalar.
primalFU :: (Eq a, Num a, Eq b, Num b, Functor fa) =>
           (forall tag. fa (Tower tag a) -> Tower tag b)
               -> (fa a) -> b
primalFU f = primal . f . fmap lift

-- | The 'primalFF' function lowers a function over dual numbers to a
-- function over primals where the function is nonscalar-to-nonscalar.
primalFF :: (Eq a, Num a, Eq b, Num b, Functor fa, Functor fb) =>
           (forall tag. fa (Tower tag a) -> fb (Tower tag b))
               -> (fa a) -> (fb b)
primalFF f = fmap primal . f . fmap lift

-- | The 'identity' function makes an identity matrix, represented as
-- list of lists of numbers.  The dimensionality is taken from the
-- length of the argument list.
identity :: (Eq a, Num a) => [b] -> [[a]]
identity [] = error "cannot create 0-dimensional identity matrix"
identity xs = map (\i -> map (\j -> if i==j then 1 else 0) js) js
    where js = zipWith const [0..] xs

-- | The 'show2d' function formats a vector or matrix (represented as
-- list or list of lists) for convenient examination.
show2d :: Show a => [a] -> String
show2d = ("["++) . (++"]\n") . (foldl1 $ (++) . (++"\n ")) . map show

-- Misc Derivative-Using Routines

-- | The 'taylor' function evaluate a Taylor series of the given
-- function around the given point with the given delta.  It returns a
-- list of increasingly higher-order approximations.
--
-- EXAMPLE: @taylor exp 0 1@
taylor :: (Eq a, Fractional a) =>
          (forall tag. Tower tag a -> Tower tag a)
              -> a -> a -> [a]

taylor f x dx = scanl1 (+)
                $ zipWith3 (\x y z -> x*y*z)
                      (diffsUU f x)
                      recipFactorials
                      (powers dx)
    where
      powers x		= iterate (*x) 1
      recipFactorials	= scanl (/) 1 $ map fromIntegral [1..]

-- | The 'taylor2' function evaluates a two-dimensional Taylor series
-- of the given function.  This is calculated by nested application of
-- the 'taylor' function, and the exported signature reflects this.

taylor2 :: (Eq a, Fractional a) =>
      (forall tag0 tag.
              Tower tag0 (Tower tag a)
                  -> Tower tag0 (Tower tag a)
                  -> Tower tag0 (Tower tag a))
          -> a -> a -> a -> a -> [[a]]

taylor2 f x y dx dy =
    [taylor (\y -> taylor (flip f (lift y)) (lift x) (lift dx) !! ix)
            y dy
     | ix <- map fst $ zip [0..] rowsListLen]
    where rowsListLen = taylor (primalUU (flip f (lift (lift y)))) x dx

-- Optimization Routines

-- Perhaps these should be in a module, named things like
--   AD.Forward.Newton.findZero
--   AD.Forward.Newton.inverse

-- | The 'zeroNewton' function finds a zero of a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--  @take 10 $ zeroNewton (\\x->x^2-4) 1  -- converge to 2.0@
--
-- TEST CASE
--  :module Data.Complex Numeric.FAD
--  @take 10 $ zeroNewton ((+1).(^2)) (1 :+ 1)  -- converge to (0 :+ 1)@
--
zeroNewton :: (Eq a, Fractional a) =>
              (forall tag. Tower tag a -> Tower tag a)
                  -> a -> [a]
zeroNewton f x0 = iterate (\x -> let (y,y') = diff2UU f x in x - y/y') x0

-- | The 'inverseNewton' function inverts a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--   @take 10 $ inverseNewton sqrt 1 (sqrt 10)  -- converge to 10@
--
inverseNewton :: (Eq a, Fractional a) =>
                 (forall tag. Tower tag a -> Tower tag a)
                     -> a -> a -> [a]
inverseNewton f x0 y = zeroNewton (\x -> (f x) - (lift y)) x0

-- | The 'fixedPointNewton' function find a fixedpoint of a scalar
-- function using Newton's method; its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)
fixedPointNewton :: (Eq a, Fractional a) =>
                    (forall tag. Tower tag a -> Tower tag a)
                        -> a -> [a]
fixedPointNewton f x0 = zeroNewton (\x -> (f x) - x) x0

-- | The 'extremumNewton' function finds an extremum of a scalar
-- function using Newton's method; produces a stream of increasingly
-- accurate results.  (Modulo the usual caveats.)
extremumNewton :: (Eq a, Fractional a) =>
                  (forall tag. forall tag1.
                          Tower tag1 (Tower tag a)
                              -> Tower tag1 (Tower tag a))
                      -> a -> [a]
extremumNewton f x0 = zeroNewton (diffUU f) x0

-- | The 'argminNaiveGradient' function performs a multivariate
-- optimization, based on the naive-gradient-descent in the file
-- @stalingrad\/examples\/flow-tests\/pre-saddle-1a.vlad@ from the
-- VLAD compiler Stalingrad sources.  Its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)  The
-- gradient is calculated using Forward AD, which is O(n) inefficient
-- as compared to Reverse AD, where n is the input dimensionality.
argminNaiveGradient :: (Eq a, Fractional a, Ord a) =>
                       (forall tag. [Tower tag a] -> Tower tag a)
                           -> [a] -> [[a]]
argminNaiveGradient f x0 =
    let
        gf = grad f
        loop x fx gx eta i =
            -- should check gx = 0 here
            let
                x1 = zipWith (+) x (map ((-eta)*) gx)
                fx1 = primalFU f x1
                gx1 = gf x1
            in
              if eta == 0 then []
              else if (fx1 > fx) then loop x fx gx (eta/2) 0
                   else if all (==0) gx then []
                        -- else if fx1 == fx then loop x1 fx1 gx1 eta (i+1)
                        else x1:(if (i==10)
                                 then loop x1 fx1 gx1 (eta*2) 0
                                 else loop x1 fx1 gx1 eta (i+1))
    in
      loop x0 (primalFU f x0) (gf x0) 0.1 0

-- BUGS!  BUGS!  BUGS!  Or, test cases.

{-

shouldBe2 = diffUU (\x -> x*(diffUU (x*) 2)) 1     -- type error w/ or w/o tags
is2       = diffUU (\x -> x*(diffUU ((lift x)*) 2)) 1
shouldBe1 = diffUU (\x -> diffUU (x*) 2) 1         -- is 0 w/o tags, type error w/ tags
is1       = diffUU (\x -> diffUU ((lift x)*) 2) 1

constant_one x = diffUU (\y -> x + y) 1 -- fails type check w/ tags

-- Higher-Order derivatives via nesting, fails type check

ds :: (forall tag. Tower tag a -> Tower tag b) -> a -> [b]

ds f x = y:(ds (diffUU f) x)
    where (y,y') = diff2UU f x

ds f x = (f x):(ds (diffUU f) x)

ds f x = y:y':(ds (diffUU (diffUU f)) x)
    where (y,y') = diff2UU f x

-}
