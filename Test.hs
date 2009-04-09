import Numeric.FAD
import Data.Complex
import Test.QuickCheck
import Data.Function (on)


-- Test only once, useful for properties with no parameters (could use
-- HUnit for such tests instead.)
onceCheck = check (defaultConfig {configMaxTest = 1})

-- | Comparison allowing for inaccuracy.  Not transitive.

nearbyAbsolute accuracy x1 x2 = abs (x1 - x2) < accuracy
nearbyRelative accuracy x1 x2 = abs (x1 - x2) < accuracy * maximum (map abs [x1,x2])
nearbyHybrid   accuracy x1 x2 = abs (x1 - x2) < accuracy * maximum (map abs [x1,x2,1])

(~=) :: (Fractional t, Ord t) => t -> t -> Bool
(~=) = nearbyHybrid 1.0e-10
infix 4 ~=

(~~=) :: (Fractional t, Ord t) => [t] -> [t] -> Bool
(~~=) [] [] = True
(~~=) (x:xs) (y:ys) = x ~= y && xs ~~= ys
(~~=) _ _ = False
infix 4 ~~=


-- Type signatures are supplied when QuickCheck is otherwise unable to
-- infer the type of the property's arguments.  An alternative way of
-- providing the type information would be, e.g.:
--
--   prop_constant_one x y = diffUU (\y -> lift x + y) y == (1 :: Double)
--

-- Test cases copied from end of Numeric/FAD.hs.
prop_is1, prop_is2 :: Double -> Bool
prop_is1 x = diffUU (\x ->    diffUU ((lift x)*) 2)  x == 1
prop_is2 x = diffUU (\x -> x*(diffUU ((lift x)*) 2)) x == 2 * x

prop_constant_one :: Double -> Double -> Bool
prop_constant_one x y = diffUU (\y -> lift x + y) y == 1

prop_diffMF_1 = diffMF (\xs -> [sum (zipWith (*) xs [1..5])]) [1,1,1,1,1] (map (10^) [0..4]) == [54321]
prop_diffMF_2 = diffMF id [10..14] [0..4] == [0,1,2,3,4]
prop_jacobian = jacobian (\xs->[sum xs,product xs,log $ product $ map (sqrt . (^2) . exp) xs]) [1..5]
             == [[1,1,1,1,1],[120,60,40,30,24],[1,1,1,1,1]]

-- @zeroNewton@ test cases.
prop_zeroNewton_1 = zeroNewton (\x->x^2-4) 1 !! 10 ~= 2
prop_zeroNewton_2 = zeroNewton ((+1).(^2)) (1 :+ 1) !! 10 == 0 :+ 1

-- @inverseNewton@ test case.
prop_inverseNewton = inverseNewton sqrt 1 (sqrt 10) !! 10 == 10

-- @atan2@ test cases.
prop_atan2_shouldBeOne :: Double -> Bool
prop_atan2_shouldBeOne a = diff (\a->atan2 (sin a) (cos a)) a ~= 1


-- @diffsUU@ test cases.
prop_diffs_1 = (diffsUU (^5) 1) == [1,5,20,60,120,120]
prop_diffs_5 n = map (2^) [0..n-1] ~~= take n (diffsUU (exp . (2*)) 0)

-- @diffs0UU@ test cases:
prop_diffs_2 = (take 20 $ diffs0UU (^5) 1) == [1,5,20,60,120,120,0,0,0,0,0,0,0,0,0,0,0,0,0,0]

-- @diffsUF@ test cases:
prop_diffs_3 = (diffsUF ((:[]) . (^5)) 1) == [[1],[5],[20],[60],[120],[120]]

-- @diffs0UF@ test cases:
prop_diffs_4 =
    (take 20 $ diffs0UF ((:[]) . (^5)) 1)
    == [[1],[5],[20],[60],[120],[120],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]]

-- List indexing which sticks with the last element when it runs off the end.

(!!~) :: [a] -> Int -> a
(!!~) xs =  (!!) (xs ++ repeat (last xs))

-- General routines for testing Taylor series accuracy

taylor_accurate :: (Ord a, Fractional a) => (forall tag. Tower tag a -> Tower tag a) -> Int -> a -> a -> Bool

taylor_accurate f n x dx = s !! 0 ~= f0 x &&
                       s !!~ n ~= f0 (x+dx)
    where s = taylor f x dx
          f0 = primalUU f

taylor_accurate_p :: (forall tag. Tower tag Double -> Tower tag Double) ->
                 Int -> Double -> Double -> Double -> Double -> Property

taylor_accurate_p f n dLo dHi x d =
    dLo <= d && d <= dHi ==> taylor_accurate f n x d

taylor2_accurate  :: (Ord a, Fractional a) =>
                  (forall tag0 tag. Tower tag0 (Tower tag a) -> Tower tag0 (Tower tag a) -> Tower tag0 (Tower tag a))
                      -> Int -> Int -> a -> a -> a -> a -> Bool

taylor2_accurate f nx ny x y dx dy =
    let
        s2 = taylor2 f x y dx dy
        f2 x y = primal $ primal $ on f (lift . lift) x y
    in
      f2 x y ~= s2 !! 0 !! 0
            &&
      f2 (x+dx) (y+dy) ~= s2 !! nx !! ny

-- Test all properties.
main = do
  quickCheck prop_is1
  quickCheck prop_is2
  quickCheck prop_constant_one
  onceCheck  prop_diffMF_1
  onceCheck  prop_diffMF_2
  onceCheck  prop_jacobian
  onceCheck  prop_zeroNewton_1
  onceCheck  prop_zeroNewton_2
  onceCheck  prop_inverseNewton
  quickCheck prop_atan2_shouldBeOne
  onceCheck  $ prop_atan2_shouldBeOne (pi/2)
  onceCheck prop_diffs_1
  onceCheck prop_diffs_2
  onceCheck prop_diffs_3
  onceCheck prop_diffs_4
  onceCheck  $ prop_diffs_5 1024
  quickCheck $ \x -> taylor_accurate_p (+(lift x))         1 (-1e9) 1e9
  quickCheck $ \x -> taylor_accurate_p ((lift x)+)         1 (-1e9) 1e9
  quickCheck $ \x -> taylor_accurate_p (flip (-) (lift x)) 1 (-1e9) 1e9
  quickCheck $ \x -> taylor_accurate_p ((lift x)-)         1 (-1e9) 1e9
  quickCheck $ \x -> taylor_accurate_p (*(lift x))         1 (-1e9) 1e9
  quickCheck $ \x -> taylor_accurate_p ((lift x)*)         1 (-1e9) 1e9
  quickCheck $ taylor_accurate_p abs 1 (-1) 1e9 1
  quickCheck $ taylor_accurate_p abs 1 (-1e9) 1 (-1)
  quickCheck $ taylor_accurate_p recip 12 (-100) 100 200
  quickCheck $ taylor_accurate_p recip 12 (-100) 100 (-200)
  quickCheck $ taylor_accurate_p negate 1 (-1e9) 1e9
  quickCheck $ taylor_accurate_p exp 40 (-4) 4
  onceCheck  $ taylor_accurate   sin 40 0 (2*pi)
  quickCheck $ taylor_accurate_p sin 40 (-2.5*pi) (2.5*pi)
  quickCheck $ taylor_accurate_p sqrt 10 (-1) 1 10
  quickCheck $ taylor_accurate_p log 10 (-1) 1 (exp 2)
  quickCheck $ taylor_accurate_p (**2.5) 12 (-0.5) 1 3
  quickCheck $ taylor_accurate_p (2.5**) 12 (-0.5) 1 3
