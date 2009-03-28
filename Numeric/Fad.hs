{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS -fglasgow-exts #-}

{- |
   Copyright  : Copyright (C) 2008-2009 Barak A. Pearlmutter and Jeffrey Mark Siskind
   License    : BSD3

   Maintainer : bjorn.buckwalter@gmail.com
   Stability  : experimental
   Portability: GHC only?
-}

-- Forward Automatic Differentiation
module Numeric.Fad (
            lift, Dual,
            diffUU, diffUF, diffMU, diffMF,
            diffUU2, diffUF2, diffMU2, diffMF2,
            diff, diff2, grad, jacobian,
            zeroNewton, inverseNewton, fixedPointNewton, extremumNewton,
            argminNaiveGradient,
            taylor)
where

import Data.List (transpose, mapAccumL)

-- Forward Automatic Differentiation via overloading to perform
-- nonstandard interpretation that replaces original numeric type with
-- corresponding generalized dual number type.

-- Credits:

--  Authors: Copyright 2008,
--     Barak A. Pearlmutter <barak@cs.nuim.ie> &
--     Jeffrey Mark Siskind <qobi@purdue.edu>

--  Work started as stripped-down version of higher-order tower code
--  published by Jerzy Karczmarczuk <jerzy.karczmarczuk@info.unicaen.fr>
--  which used a non-standard standard prelude.

--  Initial perturbation-confusing code is a modified version of
--  http://cdsmith.wordpress.com/2007/11/29/some-playing-with-derivatives/

--  Tag trick, called "branding" in the Haskell community, from
--  Bj\"orn Buckwalter <bjorn.buckwalter@gmail.com>
--  http://thread.gmane.org/gmane.comp.lang.haskell.cafe/22308/

-- To Do:

--  Add some more optimization routines
--  Add some examples
--  Add pointers into literature
--  Fix complex number issues (requires changes to standard prelude)
--  Optimize for efficiency

-- Notes:

-- Each invocation of the differentiation function introduces a
-- distinct perturbation, which requires a distinct dual number type.
-- In order to prevent these from being confused, tagging, called
-- branding in the Haskell community, is used.  This seems to prevent
-- perturbation confusion, although it would be nice to have an actual
-- proof of this.  The technique does require adding invocations of
-- lift at appropriate places when nesting is present.

-- The "pass in a lifter" approach, discussed in the HOSC paper, was
-- rediscovered and implemented by David Roundy <droundy@darcs.net>
-- http://thread.gmane.org/gmane.comp.lang.haskell.cafe/22308
-- Unfortunately this would preclude writing in a natural style, and
-- is therefore not used here.  It however could be combined with
-- tagging to allow dynamic nesting, if the type system would allow.

-- The constructor is "Bundle" because dual numbers are tangent-vector
-- bundles, in the terminology of differential geometry.  For the same
-- reason, the accessor for the first derivative is "tangent".

-- The multivariate case is handled as a list on inputs, but an
-- arbitrary functor on outputs.  This asymmetry is because Haskell
-- provides fmap but not fzipWith.

-- The derivative towers can be truncated, using Zero.  Care is taken
-- to preserve said trunction, when possible.


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

-- | The 'Dual' type is a concrete representation of a higher-order
-- Dual number, meaning a number augmented with a tower of
-- derivatives.  These generalize the Dual numbers of Clifford (1873),
-- which hold only a first derivative.  They can be converted to
-- formal power series via division by the sequence of factorials.
newtype Dual tag a = Tower [a] deriving Show

-- Injectors and accessors for derivative towers

-- | The 'lift' function injects a primal number into the domain of
-- dual numbers, with a zero tower.  If dual numbers were a monad,
-- 'lift' would be 'return'.
lift :: Num a => a -> Dual tag a
lift = flip bundle zero

-- | The 'bundle' function takes a primal number and a dual number
-- tower and returns a dual number tower with the given tower shifted
-- up one and the new primal inserted.
--
-- Property: @x = bundle (primal x) (tangentTower x)@
bundle :: Num a => a -> Dual tag a -> Dual tag a
bundle x0 x' = Tower (x0:towerList x')
-- The following forces its second argument's structure, which is very bad:
-- bundle x0 (Tower xs) = Tower (x0:xs)

-- | The zero element of a Dual Number tower algebra
zero :: Num a => Dual tag a
zero = Tower []

-- | The 'apply' function applies a function to a number lifted from
-- the primal domain to the dual number domain, with derivative 1,
-- thus calculating the generalized push-forward, in the differential
-- geometric sense, of the given function at the given point.
apply :: Num a => (Dual tag a -> b) -> a -> b
apply = (. flip bundle 1)

-- | The 'towerElt' function finds the i-th element of a dual number
-- | tower, where the 0-th element is the primal value, the 1-st
-- | element is the first derivative, etc.
towerElt :: Num a => Int -> Dual tag a -> a
towerElt i (Tower xs) = xs !!! i

[] !!! i = if i<0
           then error "negative index"
           else 0
(x0:xs) !!! 0 = x0
(x0:xs) !!! i = xs !!! (i-1)

-- | The 'towerList' function converts a dual number tower to a list
-- of values with the i-th derivatives, i=0,1,..., possibly truncated
-- when all remaining values in the tower are zero.
towerList :: Dual tag a -> [a]
towerList (Tower xs) = xs

-- | The 'primal' function finds the primal value from a dual number
-- | tower.  The inverse of 'lift'.
primal :: Num a => Dual tag a -> a
primal = towerElt 0

-- | The 'tangent' function finds the tangent value of a dual number
-- | tower, i.e., the first-order derivative.
tangent :: Num a => Dual tag a -> a
tangent = towerElt 1

-- | The 'tangentTower' function finds the entire tower of tangent
-- values of a dual number tower, starting at the 1st derivative.
-- This is equivalent, in an appropriate sense, to taking the first
-- derivative.
tangentTower :: Num a => Dual tag a -> Dual tag a
tangentTower (Tower []) = zero
tangentTower (Tower (_ : x')) = Tower x'

-- | The 'liftA1' function lifts a scalar numeric function from a base
-- numeric type to a function over derivative towers.  Takes the
-- primal function and the derivative function as arguments.  The
-- derivative function should return a scalar.
--
-- EXAMPLE: @liftA1 sin cos@
liftA1 :: Num a =>
         (a -> a)
             -> (Dual tag a -> Dual tag a)
             -> Dual tag a -> Dual tag a

liftA1 f = (liftA1_ f) . const

-- | The 'liftA2' function lifts a binary numeric function from a base
-- numeric type to a function over derivative towers.  Takes the
-- primal function and the derivative function as arguments.  The
-- derivative function should return the Jacobian matrix,
-- representated as a pair.
--
-- EXAMPLE: @liftA2 (*) (\\x y -> (y,x))@
liftA2 :: Num a =>
         (a -> a -> a)
             -> (Dual tag a -> Dual tag a -> (Dual tag a, Dual tag a))
             -> Dual tag a -> Dual tag a -> Dual tag a

liftA2 f = (liftA2_ f) . const

-- | The 'liftA1_' funciton lifts a scalar numeric function, like
-- 'liftA1', except the the derivative function is given access to the
-- output value.  This eases recursion and reuse.
--
-- EXAMPLE: @liftA1_ exp const@
liftA1_ :: Num a =>
         (a -> a)
             -> (Dual tag a -> Dual tag a -> Dual tag a)
             -> Dual tag a -> Dual tag a

liftA1_ f df x = z
    where z = bundle (f (primal x)) (tangentTower x * df z x)

-- | The 'liftA2_' funciton lifts a binary numeric function, like
-- 'liftA2', except the the derivative function is given access to the
-- output value.  This eases recursion and reuse.
--
-- EXAMPLE: @liftA2_ (**) (\z x y -> (y*z\/x, z*log x))@
liftA2_ :: Num a =>
         (a -> a -> a)
             -> (Dual tag a
                     -> Dual tag a
                     -> Dual tag a
                     -> (Dual tag a, Dual tag a))
             -> Dual tag a -> Dual tag a -> Dual tag a

liftA2_ f df x y = z
    where z = bundle z0 z'
          z0 = f (primal x) (primal y)
          z' = tangentTower x * dfdx + tangentTower y * dfdy
          (dfdx, dfdy) = df z x y

-- | The 'liftA1disc' function lifts a scalar function with numeric
-- input and discrete output from into the derivative tower domain.
liftA1disc :: Num a => (a -> c) -> Dual tag a -> c
liftA1disc f x = f (primal x)

-- | The 'liftA2disc' function lifts a binary function with numeric
-- inputs and discrete output from into the derivative tower domain.
liftA2disc :: (Num a, Num b) => (a -> b -> c) -> Dual tag a -> Dual tag b -> c
liftA2disc f x y = f (primal x) (primal y)

-- | The 'liftLin' function lifts a linear scalar function from the
-- primal domain into the derivative tower domain.  WARNING: the
-- restriction to linear functions is not enforced by the type system.
liftLin :: (a -> b) -> Dual tag a -> Dual tag b
liftLin f = Tower . map f . towerList

-- Numeric operations on derivative towers.

instance Num a => Num (Dual tag a) where
    (Tower []) + y	= y
    x + (Tower [])	= x
    x + y = bundle (primal x + primal y) (tangentTower x + tangentTower y)
    x - (Tower [])	= x
    (Tower []) - x	= negate x
    x - y = bundle (primal x - primal y) (tangentTower x - tangentTower y)
    (Tower []) * _	= zero
    _ * (Tower [])	= zero
    x * y	= liftA2 (*) (flip (,)) x y
    negate	= liftLin negate
    abs (Tower [])	= abs 0
    abs x = let x0 = primal x
                x' = tangentTower x
                s  = signum x0
                s' = signum x'
            in bundle
                   (abs x0)
                   (if x0==0
                    then error "not differentiable: abs(0)"
                    else if s /= 0 && s' /= 0
                         then x' * lift s
                         else error "not differentiable: abs(complex)")
    signum (Tower []) = signum 0
    signum x = let x0 = primal x
                   x' = tangentTower x
                   s  = signum x0
                   s' = signum x'
               in bundle s
                  (if x0==0
                   then error "not differentiable: signum(0)"
                   else if s /= 0 && s' /= 0
                        then zero
                        else error "not differentiable: signum(complex)")
    fromInteger	= lift . fromInteger

-- Here is another problem with supporting complex numbers.  This is a
-- show stopper for doing transparent forward AD on functions that are
-- explicitly over complex numbers.

-- The following will not work:

-- instance Complex a => Complex (Dual tag a) where
--     realPart   = liftLin realPart
--     imagPart   = liftLin imagPart
--     conjugate  = liftLin conjugate
--     ...

-- This fails because Complex in the standard prelude is not abstract
-- enough.  It is impossible to make (Dual (Complex a)) a complex
-- number; the system can only do (Complex (Dual a)).  This makes it
-- impossible to take derivatives of complex functions, i.e., analytic
-- functions, using the same API as non-complex functions.

instance Fractional a => Fractional (Dual tag a) where
    recip		= liftA1_ recip (const . negate . (^2))
    fromRational	= lift . fromRational

instance Floating a => Floating (Dual tag a) where
    pi		= lift pi
    exp		= liftA1_ exp const
    sqrt	= liftA1_ sqrt (const . recip . (2*))
    log		= liftA1 log recip
    -- Bug on zero base, e.g., (0**2), since derivative is fine but
    -- can get division by 0 and log 0, oops.  Need special cases, ick.
    -- Here are some untested ideas:
    --  (**) x (Tower []) = 1
    --  (**) x y@(Tower [y0]) = liftA1 (**y0) ((y*) . (**(y-1))) x
    (**)	= liftA2_ (**) (\z x y -> (y*z/x, z*log x))
    sin		= liftA1 sin cos
    cos		= liftA1 cos (negate . sin)
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

 *Fad> let shouldBeOne a = diff (\a->atan2 (sin a) (cos a)) a

 *Fad> shouldBeOne (pi/2-1e-12)
 1.0

 *Fad> shouldBeOne (pi/2)
 1.0

 *Fad> shouldBeOne (pi/2+1e-12)
 1.0

 *Fad> diff shouldBeOne (pi/2-1e-12)
 0.0

 *Fad> diff shouldBeOne (pi/2)
 -4.0                          -- <<<<<<<<<<<<<<<< BUG IS HERE

 *Fad> diff shouldBeOne (pi/2+1e-12)
 0.0

-}

instance (RealFloat a, RealFrac a) => RealFloat (Dual tag a) where
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

instance RealFrac a => RealFrac (Dual tag a) where
    properFraction x = (z1, (bundle z2 (tangentTower x)))
        where (z1,z2) = properFraction (primal x)
    truncate	= liftA1disc truncate
    round	= liftA1disc round
    ceiling	= liftA1disc ceiling
    floor	= liftA1disc floor

instance Real a => Real (Dual tag a) where
    toRational	= liftA1disc toRational

instance (Eq a, Num a) => Eq (Dual tag a) where
    (==)	= liftA2disc (==)

instance (Ord a, Num a) => Ord (Dual tag a) where
    compare	= liftA2disc compare

instance (Enum a, Num a) => Enum (Dual tag a) where
    succ	= liftA1 succ (const 1)
    pred	= liftA1 pred (const 1)
    fromEnum	= liftA1disc fromEnum
    toEnum	= lift . toEnum

-- First-Order Differentiation Operators

-- These have two-letter suffices for the arity of the input and
-- output of the passed functions: U for univariate, meaning a number,
-- M for multivariate, meaning a list of numbers.

-- Perhaps these should be named things like
--   AD.Forward.D.uu
--   AD.Forward.D.um
--   AD.Forward.grad
--   AD.Forward.jacobian

-- When the input is multivariate a directional derivative is
-- calculated; this requires an additional "direction" parameter.  The
-- multivariate case is treated as a list (on input) and as a functor
-- of arbitrary shape, which includes lists as a special case, on
-- output.

-- | The 'diffUU' function calculates the first derivative of a
-- scalar-to-scalar function.
diffUU :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> b
diffUU f = tangent . apply f

-- | The 'diffUF' function calculates the first derivative of
-- scalar-to-nonscalar function.
diffUF :: (Num a, Num b, Functor f) =>
          (forall tag. Dual tag a -> f (Dual tag b)) -> a -> f b
diffUF f = fmap tangent . apply f

-- | The 'diffMU' function calculate the product of the Jacobian of a
-- nonscalar-to-scalar function with a given vector.  Aka: directional
-- derivative.
diffMU :: (Num a, Num b) =>
          (forall tag. [Dual tag a] -> Dual tag b) -> [a] -> [a] -> b
diffMU f xs = tangent . f . zipWithBundle xs

-- | The 'diffMF' function calculates the product of the Jacobian of a
-- nonscalar-to-nonscalar function with a given vector.  Aka:
-- directional derivative.
diffMF :: (Num a, Num b, Functor f) =>
          (forall tag. [Dual tag a] -> f (Dual tag b)) -> [a] -> [a] -> f b
diffMF f xs = fmap tangent . f . zipWithBundle xs

-- | The 'diffUU2' function calculates the value and derivative, as a
-- pair, of a scalar-to-scalar function.
diffUU2 :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> (b,b)
diffUU2 f = dualToPair . apply f

-- | The 'diffUF2' function calculates the value and derivative, as a
-- pair, of a scalar-to-nonscalar function.
diffUF2 :: (Functor f, Num a, Num b) =>
           (forall tag. Dual tag a -> f (Dual tag b)) -> a -> (f b, f b)
diffUF2 f = fdualsToPair . apply f

-- | The 'diffMU2' function calculates the value and directional
-- derivative, as a pair, of a nonscalar-to-scalar function.
diffMU2 :: (Num a, Num b) =>
           (forall tag. [Dual tag a] -> Dual tag b) -> [a] -> [a] -> (b,b)
diffMU2 f xs = dualToPair . f . zipWithBundle xs

-- | The 'diffMF2' function calculates the value and directional
-- derivative, as a pair, of a nonscalar-to-nonscalar function.
diffMF2 :: (Functor f, Num a, Num b) =>
           (forall tag. [Dual tag a] -> f (Dual tag b))
               -> [a] -> [a] -> (f b, f b)
diffMF2 f xs = fdualsToPair . f . zipWithBundle xs

-- Common access patterns

-- | The 'diff' function is a synonym for 'diffUU'.
diff :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> b
diff = diffUU

-- | The 'diff2' function is a synonym for 'diffUU2'.
diff2 :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> (b, b)
diff2 = diffUU2

-- | The 'grad' function calculates the gradient of a
-- nonscalar-to-scalar function, using n invocations of forward AD,
-- where n is the input dimmensionality.  NOTE: this is O(n)
-- inefficient as compared to reverse AD.
grad :: (Num a, Num b) => (forall tag. [Dual tag a] -> Dual tag b) -> [a] -> [b]
-- grad f = head . jacobian ((:[]) . f) -- Robot face, robot claw!
grad f xs = map (diffMU f xs) (identity xs)

-- | The 'jacobian' function calcualtes the Jacobian of a
-- nonscalar-to-nonscalar function, using n invocations of forward AD,
-- where n is the input dimmensionality.
jacobian :: (Num a, Num b) =>
            (forall tag. [Dual tag a] -> [Dual tag b]) -> [a] -> [[b]]
jacobian f xs = transpose $ map (diffMF f xs) (identity xs)

-- | The 'dualToPair' function converts a tower of derivatives to a
-- pair of the primal and the first derivative.
dualToPair :: Num a => Dual tag a -> (a,a)
dualToPair x = (primal x, tangent x)

-- | The 'fdualsToPair' function converts a functor of derivative
-- towers to a pair: one with the functor holding the primal values,
-- the other with the functor holding the first derivatives.
fdualsToPair :: (Functor f, Num a) => f (Dual tag a) -> (f a, f a)
fdualsToPair fxs = (fmap primal fxs, fmap tangent fxs)

-- | The 'zipWithBundle' function zip two lists of numbers into a list
-- of derivative towers with the given primal values andd first
-- derivatives.  Like @zipWith Bundle@ except that the two lists
-- should be the same length.
zipWithBundle :: Num a => [a] -> [a] -> [Dual tag a]
zipWithBundle [] [] = []
zipWithBundle (x:xs) (y:ys) = (bundle x (lift y)):(zipWithBundle xs ys)
zipWithBundle _ _ = error "zipWithBundle arguments, lengths differ"

-- | The 'lowerUU' function lowers a function over dual numbers to a
-- function in the primal domain, where the function is
-- scalar-to-scalar.
lowerUU :: (Num a, Num b) =>
           (forall tag. Dual tag a -> Dual tag b) -> a -> b
lowerUU f = primal . f . lift

-- | The 'lowerUF' function lowers a function over dual numbers to a
-- function over primals, where the function is scalar-to-nonscalar.
lowerUF :: (Num a, Functor fb, Num b) =>
            (forall tag. Dual tag a -> fb (Dual tag b)) -> a -> (fb b)
lowerUF f = fmap primal . f . lift

-- | The 'lowerFU' function lowers a function over dual numbers to a
-- function over primals where the function is nonscalar-to-scalar.
lowerFU :: (Functor fa, Num a, Num b) =>
           (forall tag. fa (Dual tag a) -> Dual tag b) -> (fa a) -> b
lowerFU f = primal . f . fmap lift

-- | The 'lowerFF' function lowers a function over dual numbers to a
-- function over primals where the function is nonscalar-to-nonscalar.
lowerFF :: (Functor fa, Num a, Functor fb, Num b) =>
           (forall tag. fa (Dual tag a) -> fb (Dual tag b))
               -> (fa a) -> (fb b)
lowerFF f = fmap primal . f . fmap lift

-- | The 'identity' function makes an identity matrix, represented as
-- list of lists of numbers.  The dimensionality is taken from the
-- length of the argument list.
identity :: Num a => [b] -> [[a]]
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
taylor :: Fractional a => (forall tag. Dual tag a -> Dual tag a) -> a -> a -> [a]

taylor f x dx = snd
                $ mapAccumL (\a x -> app2 (,) $ a+x) 0
                      $ zipWith3 (\x y z -> x*y*z)
                            (towerList $ apply f x)
                            recipFactorials
                            (powers dx)
    where
      powers x		= iterate (*x) 1
      recipFactorials	= snd $ mapAccumL (\a i -> (a/fromIntegral i, a)) 1 [1..]
      app2 f x		= f x x

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
--  :module Complex Fad
--  @take 10 $ zeroNewton ((+1).(^2)) (1 :+ 1)  -- converge to (0 :+ 1)@
--
zeroNewton :: Fractional a =>
              (forall tag. Dual tag a -> Dual tag a) -> a -> [a]
zeroNewton f x0 = iterate (\x -> let (y,y') = diffUU2 f x in x - y/y') x0

-- | The 'inverseNewton' function inverts a scalar function using
-- Newton's method; its output is a stream of increasingly accurate
-- results.  (Modulo the usual caveats.)
--
-- TEST CASE:
--   @take 10 $ inverseNewton sqrt 1 (sqrt 10)  -- converge to 10@
--
inverseNewton :: Fractional a =>
                 (forall tag. Dual tag a -> Dual tag a)
                     -> a -> a -> [a]
inverseNewton f x0 y = zeroNewton (\x -> (f x) - (lift y)) x0

-- | The 'fixedPointNewton' function find a fixedpoint of a scalar
-- function using Newton's method; its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)
fixedPointNewton :: Fractional a =>
                    (forall tag. Dual tag a -> Dual tag a) -> a -> [a]
fixedPointNewton f x0 = zeroNewton (\x -> (f x) - x) x0

-- | The 'extremumNewton' function finds an extremum of a scalar
-- function using Newton's method; produces a stream of increasingly
-- accurate results.  (Modulo the usual caveats.)
extremumNewton :: Fractional a =>
                  (forall tag. forall tag1.
                          Dual tag1 (Dual tag a) -> Dual tag1 (Dual tag a))
                      -> a -> [a]
extremumNewton f x0 = zeroNewton (diffUU f) x0

-- | The 'argminNaiveGradient' function performs a multivariate
-- optimization, based on the naive-gradient-descent in the file
-- @stalingrad\/examples\/flow-tests\/pre-saddle-1a.vlad@ from the
-- VLAD compiler Stalingrad sources.  Its output is a stream of
-- increasingly accurate results.  (Modulo the usual caveats.)  The
-- gradient is calculated using Forward AD, which is O(n) inefficient
-- as compared to Reverse AD, where n is the input dimensionality.
argminNaiveGradient :: (Fractional a, Ord a) =>
                       (forall tag. [Dual tag a] -> Dual tag a)
                           -> [a] -> [[a]]
argminNaiveGradient f x0 =
    let
        gf = grad f
        loop x fx gx eta i =
            -- should check gx = 0 here
            let
                x1 = zipWith (+) x (map ((-eta)*) gx)
                fx1 = lowerFU f x1
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
      loop x0 (lowerFU f x0) (gf x0) 0.1 0

-- BUGS!  BUGS!  BUGS!  Or, test cases.

{-

shouldBe2 = diffUU (\x -> x*(diffUU (x*) 2)) 1     -- type error w/ or w/o tags
is2       = diffUU (\x -> x*(diffUU ((lift x)*) 2)) 1
shouldBe1 = diffUU (\x -> diffUU (x*) 2) 1         -- is 0 w/o tags, type error w/ tags
is1       = diffUU (\x -> diffUU ((lift x)*) 2) 1

constant_one x = diffUU (\y -> x + y) 1 -- fails type check w/ tags

-- Successful tests of directional derivative:

-- should be [54321]
diffMF (\xs -> [sum (zipWith (*) xs [1..5])]) [1,1,1,1,1] (map (10^) [0..4])

-- should be [[1.0,1.0,1.0,1.0,1.0],[120.0,60.0,40.0,30.0,24.0],[1.0,1.0,1.0,1.0,1.0]]
jacobian (\xs->[sum xs,product xs,log $ product $ map (sqrt . (^2) . exp) xs]) [1..5]

-- should be [0,1,2,3,4]
diffMF id [10..14] [0..4]

-- Higher-Order derivatives via nesting, fails type check

ds :: (forall tag. Dual tag a -> Dual tag b) -> a -> [b]

ds f x = y:(ds (diffUU f) x)
    where (y,y') = diffUU2 f x

ds f x = (f x):(ds (diffUU f) x)

ds f x = y:y':(ds (diffUU (diffUU f)) x)
    where (y,y') = diffUU2 f x

-}
