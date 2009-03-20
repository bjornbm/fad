{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS -fglasgow-exts #-}

-- Forward Automatic Differentiation
module Fad (lift, Dual,
            diffUU, diffUF, diffUF', diffMU, diffMF,
            diffUU2, diffUF2, diffMU2, diffMF2,
            diff, diff', grad, jacobian,
            zeroNewton, inverseNewton, fixedPointNewton, extremumNewton)
where

import Data.List (transpose, mapAccumL)

-- Forward Automatic Differentiation via overloading to perform
-- nonstandard interpretation that replaces original numeric type with
-- corresponding dual number type.

-- License:

--  Copyright (C) 2008 Barak A. Pearlmutter & Jeffrey Mark Siskind
--
--  This program is free software; you can redistribute it and/or modify
--  it under the terms of the GNU General Public License as published by
--  the Free Software Foundation; either version 2 of the License, or
--  (at your option) any later version.
--
--  This program is distributed in the hope that it will be useful,
--  but WITHOUT ANY WARRANTY; without even the implied warranty of
--  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
--  GNU General Public License for more details.
--
--  You should have received a copy of the GNU General Public License along
--  with this program; if not, write to the Free Software Foundation, Inc.,
--  51 Franklin Street, Fifth Floor, Boston, MA 02110-1301 USA.

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

data Dual tag a = Bundle a (Dual tag a) | Zero deriving Show

-- Injectors and accessors for derivative towers

lift :: Num a => a -> Dual tag a
lift = flip Bundle Zero

liftOne :: Num a => a -> Dual tag a
liftOne = flip Bundle (lift 1)

towerElt :: Num a => Int -> Dual tag a -> a
towerElt 0 (Bundle x0 _) = x0
towerElt i (Bundle _ x') = if i<0
                           then error "negative index"
                           else towerElt (i-1) x'
towerElt i Zero = if i<0
                  then error "negative index"
                  else 0

towerList :: Dual tag a -> [a]
towerList Zero = []
towerList (Bundle x0 x') = x0:towerList x'

primal :: Num a => Dual tag a -> a
primal = towerElt 0

tangent :: Num a => Dual tag a -> a
tangent = towerElt 1

tangentTower :: Num a => Dual tag a -> Dual tag a
tangentTower Zero = Zero
tangentTower (Bundle x0 x') = x'

-- Evaluate function using an i-th order Taylor series

taylor :: Fractional a => (Dual tag a -> Dual tag a) -> a -> a -> [a]

taylor f x dx = snd
                $ mapAccumL (\a t -> (a+t,a)) 0
                      $ zipWith3 (\x y -> (x*y*))
                            (towerList (f (liftOne x)))
                            recipFactorials
                            (powers dx)
    where
      powers x		= iterate (*x) 1
      recipFactorials	= snd $ mapAccumL (\a i -> (a/fromIntegral i, a)) 1 [1..]


-- Lift a numeric function from a base numeric type to a function over
-- derivative towers.  Takes the primal function and the derivative
-- function as arguments.  In the binary case, the derivative function
-- returns the Jacobian, representated as a pair.

liftA1 :: Num a =>
         (a -> a)
             -> (Dual tag a -> Dual tag a)
             -> Dual tag a -> Dual tag a

liftA1 f = (liftA1_ f) . const

liftA2 :: Num a =>
         (a -> a -> a)
             -> (Dual tag a -> Dual tag a -> (Dual tag a, Dual tag a))
             -> Dual tag a -> Dual tag a -> Dual tag a

liftA2 f = (liftA2_ f) . const

-- These are like liftA and liftA2, except they take an extra argument
-- to df which is the numeric output, allowing easy recursion/reuse.

liftA1_ :: Num a =>
         (a -> a)
             -> (Dual tag a -> Dual tag a -> Dual tag a)
             -> Dual tag a -> Dual tag a

liftA1_ f df x@(Bundle x0 x')
    = let z = Bundle z0 z'
          z0 = f (primal x)
          z' = tangentTower x * df z x
      in z


liftA2_ :: Num a =>
         (a -> a -> a)
             -> (Dual tag a
                     -> Dual tag a
                     -> Dual tag a
                     -> (Dual tag a, Dual tag a))
             -> Dual tag a -> Dual tag a -> Dual tag a

liftA2_ f df x y
    = let z = Bundle z0 z'
          z0 = (f (primal x) (primal y))
          z' =  tangentTower x * dfdx + tangentTower y * dfdy
          (dfdx, dfdy) = df z x y
      in z

-- Lift functions which return values in discrete domains.

liftA1disc :: Num a => (a -> c) -> Dual tag a -> c
liftA2disc :: (Num a, Num b) => (a -> b -> c) -> Dual tag a -> Dual tag b -> c

liftA1disc f x = f (primal x)
liftA2disc f x y = f (primal x) (primal y)

-- Lift linear functions.
-- Note: the restriction to linear function is not enforced by the type system.

liftLin :: (a -> b) -> Dual tag a -> Dual tag b
liftLin f Zero = Zero
liftLin f (Bundle x x') = Bundle (f x) (liftLin f x')

-- Numeric operations on derivative towers.

instance Num a => Num (Dual tag a) where
    Zero + y	= y
    x + Zero	= x
    (Bundle x0 x') + (Bundle y0 y') = Bundle (x0 + y0) (x' + y')
    x - Zero	= x
    Zero - x	= negate x
    (Bundle x0 x') - (Bundle y0 y') = Bundle (x0 - y0) (x' - y')
    (*) Zero _	= Zero
    (*) _ Zero	= Zero
    (*) x y	= liftA2 (*) (flip (,)) x y
    negate	= liftLin negate
    abs Zero	= abs (Bundle 0 Zero)
    abs (Bundle 0 _) = Bundle 0 (error "not differentiable: abs(0)")
    abs (Bundle x x') = let s  = signum x
                            s' = signum x'
                        in Bundle (abs x)
                                   (if (s == 1 || s == (-1))
                                           && (s' == 1 || s' == (-1))
                                    then (x' * (lift s))
                                    else error "not differentiable: abs(complex)")
    signum Zero = signum (Bundle 0 Zero)
    signum (Bundle x0@0 _) = Bundle x0 (error "not differentiable: signum(0)")
    signum (Bundle x x')   = let s  = signum x
                                 s' = signum x'
                             in Bundle s
                                (if (s == 1 || s == (-1))
                                        && (s' == 1 || s' == (-1))
                                 then 0
                                 else error "not differentiable: signum(complex)")
    fromInteger	= lift . fromInteger

-- Here is another problem with supporting complex numbers.  This is a
-- show stopper for doing transparent forward AD on functions that are
-- explicitly over complex numbers.

-- The following will not work:

-- instance Complex a => Complex (Dual tag a) where
--     realPart  (Bundle x x') = Bundle (realPart x)  (realPart x')
--     imagPart  (Bundle x x') = Bundle (imagPart x)  (imagPart x')
--     conjugate (Bundle x x') = Bundle (conjugate x) (conjugate x')
--     ...

-- This fails because Complex in the standard prelude is not abstract
-- enough.  It is impossible to make (Dual (Complex a)) a complex
-- number; the system can only do (Complex (Dual a)).  This makes it
-- impossible to take derivatives of complex functions using the same
-- API as non-complex functions.

instance Fractional a => Fractional (Dual tag a) where
    recip		= liftA1_ recip (const . negate . (^2))
    fromRational	= lift . fromRational

instance Floating a => Floating (Dual tag a) where
    pi		= lift pi
    exp		= liftA1_ exp (const . id)
    sqrt	= liftA1_ sqrt (const . recip . (2*))
    log		= liftA1 log recip
    -- Bug on zero base, e.g., (0**2), since derivative is fine but
    -- can get division by 0 and log 0, oops.  Need special cases, ick.
    -- Here are some untested ideas:
    --  (**) x Zero = 1
    --  (**) x y@(Bundle y0 Zero) = liftA1 (**y0) ((y*) . (**(y-1))) x
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
    encodeFloat n i	= Bundle (encodeFloat n i)
                          (error "not differentiable: encodeFloat")
    scaleFloat i	= liftA1_ (scaleFloat i) (/)
    isNaN		= liftA1disc isNaN
    isInfinite		= liftA1disc isInfinite
    isDenormalized	= liftA1disc isDenormalized
    isNegativeZero	= liftA1disc isNegativeZero
    isIEEE		= liftA1disc isIEEE
    atan2		= liftA2 atan2 (\x y->let r = recip (x^2+y^2) in (y*r, -x*r))

instance RealFrac a => RealFrac (Dual tag a) where
    properFraction (Bundle x x') = (z1, (Bundle z2 x'))
        where (z1,z2) = properFraction x
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

diff' :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> (b, b)
diff' f = dual2pair . f . liftOne
-- diff' f x = (y, y') where Bundle y y' = f (Bundle x 1)

diffUU :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> b
diffUU f = tangent . f . liftOne

diffUF :: (Num a, Num b, Functor f) =>
          (forall tag. Dual tag a -> f (Dual tag b)) -> a -> f b
diffUF f = fmap tangent . f . liftOne

diffUF' :: (Num a, Num b, Functor f) =>
           (forall tag. Dual tag a -> f (Dual tag b)) -> a -> (f b, f b)
diffUF' f x = (fprimal y, ftangent y) where y = f (liftOne x)

diffMU :: (Num a, Num b) =>
          (forall tag. [Dual tag a] -> Dual tag b) -> [a] -> [a] -> b
diffMU f xs = tangent . f . zipWithBundle xs

diffMF :: (Num a, Num b, Functor f) =>
          (forall tag. [Dual tag a] -> f (Dual tag b)) -> [a] -> [a] -> f b
diffMF f xs = fmap tangent . f . zipWithBundle xs

-- value and derivative as a pair, for all combos uni/multi in/out

diffUU2 :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> (b,b)
diffUU2 f = dual2pair . f . flip Bundle 1

diffUF2 :: (Functor f, Num a, Num b) =>
           (forall tag. Dual tag a -> f (Dual tag b)) -> a -> (f b, f b)
diffUF2 f = fduals2pair . f . flip Bundle 1

diffMU2 :: (Num a, Num b) =>
           (forall tag. [Dual tag a] -> Dual tag b) -> [a] -> [a] -> (b,b)
diffMU2 f xs = dual2pair . f . zipWithBundle xs

diffMF2 :: (Functor f, Num a, Num b) =>
           (forall tag. [Dual tag a] -> f (Dual tag b))
               -> [a] -> [a] -> (f b, f b)
diffMF2 f xs = fduals2pair . f . zipWithBundle xs

-- Common access patterns

diff :: (Num a, Num b) => (forall tag. Dual tag a -> Dual tag b) -> a -> b
diff = diffUU

grad :: (Num a, Num b) => (forall tag. [Dual tag a] -> Dual tag b) -> [a] -> [b]
-- grad f = head . jacobian ((:[]) . f) -- Robot face, robot claw!
grad f xs = map (diffMU f xs) (identity xs)

jacobian :: (Num a, Num b) =>
            (forall tag. [Dual tag a] -> [Dual tag b]) -> [a] -> [[b]]
jacobian f xs = transpose $ map (diffMF f xs) (identity xs)

-- Utility functions for shared code in above

ftangent :: (Functor f, Num a) => f (Dual tag a) -> f a
ftangent = fmap tangent

fprimal :: (Functor f, Num a) => f (Dual tag a) -> f a
fprimal = fmap primal

flift :: (Functor f, Num a) => f a -> f (Dual tag a)
flift = fmap lift

dual2pair :: Num a => Dual tag a -> (a,a)
dual2pair x = (primal x, tangent x)

fduals2pair :: (Functor f, Num a) => f (Dual tag a) -> (f a, f a)
fduals2pair fxs = (fprimal fxs, ftangent fxs)

zipWithBundle :: Num a => [a] -> [a] -> [Dual tag a]
zipWithBundle [] [] = []
zipWithBundle (x:xs) (y:ys) = (Bundle x (lift y)):(zipWithBundle xs ys)
zipWithBundle _ _ = error "zipWithBundle arguments, lengths differ"

-- Lower a function over duals to a function over primals.
-- Four variants, for unary/functorized domain/range.

lowerUU :: (Num a, Num b) =>
           (forall tag. Dual tag a -> Dual tag b) -> a -> b
lowerUU f = primal . f . lift

lowerUF :: (Num a, Functor fb, Num b) =>
            (forall tag. Dual tag a -> fb (Dual tag b)) -> a -> (fb b)
lowerUF f = fprimal . f . lift

lowerFU :: (Functor fa, Num a, Num b) =>
           (forall tag. fa (Dual tag a) -> Dual tag b) -> (fa a) -> b
lowerFU f = primal . f . flift

lowerFF :: (Functor fa, Num a, Functor fb, Num b) =>
           (forall tag. fa (Dual tag a) -> fb (Dual tag b))
               -> (fa a) -> (fb b)
lowerFF f = fprimal . f . flift

-- Create identity matrix, represented as list of lists of numbers.

identity :: Num a => [b] -> [[a]]
identity [] = error "cannot create 0-dimensional identity matrix"
identity xs
    = [unit i xs | (i,_) <- zip [0..] xs]
      where unit i xs = [if j==i then 1 else 0 | (j,_) <- zip [0..] xs]

-- Format matrix for convenient examination.  Also works on vectors.

show2d :: Show a => [a] -> String
show2d = ("["++) . (++"]\n") . (foldl1 $ (++) . (++"\n ")) . map show

-- Optimization
-- Perhaps these should be in a module, named things like
--   AD.Forward.Newton.findZero
--   AD.Forward.Newton.inverse

-- Find a zero of a unary function using Newton's method; produces a
-- stream of increasingly accurate results.

-- TEST CASE:
--  take 10 $ zeroNewton (\x->x^2-4) 1  -- converge to 2.0

-- TEST CASE
--  :module Complex Fad
--  take 10 $ zeroNewton ((+1).(^2)) (1 :+ 1)  -- converge to (0 +: 1)

zeroNewton :: Fractional a =>
              (forall tag. Dual tag a -> Dual tag a) -> a -> [a]
zeroNewton f x0 = iterate (\x -> let (y,y') = diffUU2 f x in x - y/y') x0

-- Invert a unary function using Newton's method; produces a stream of
-- increasingly accurate results.

-- TEST CASE:
--   take 10 $ inverseNewton sqrt 1 (sqrt 10)  -- converge to 10

inverseNewton :: Fractional a =>
                 (forall tag. Dual tag a -> Dual tag a)
                     -> a -> a -> [a]
inverseNewton f x0 y = zeroNewton (\x -> (f x) - (lift y)) x0

-- Find a fixedpoint of a unary function using Newton's method;
-- produces a stream of increasingly accurate results.

fixedPointNewton :: Fractional a =>
                    (forall tag. Dual tag a -> Dual tag a) -> a -> [a]
fixedPointNewton f x0 = zeroNewton (\x -> (f x) - x) x0

-- Find an extremum of a unary function using Newton's method;
-- produces a stream of increasingly accurate results.

extremumNewton :: Fractional a =>
                  (forall tag. forall tag1.
                          Dual tag1 (Dual tag a) -> Dual tag1 (Dual tag a))
                      -> a -> [a]
extremumNewton f x0 = zeroNewton (diffUU f) x0

-- Multivariate optimization, based on naive-gradient-descent from
-- stalingrad/examples/flow-tests/pre-saddle-1a.vlad
-- Produces stream of increasingly accurate results.

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
