import Numeric.Fad
import Data.Complex
import Test.QuickCheck

-- Test only once, useful for properties with no parameters (could use
-- HUnit for such tests instead.)
onceCheck = check (defaultConfig {configMaxTest = 1})

-- | Comparison allowing for inaccuracy (not pretty).
cmpE :: Double -> Double -> Double -> Bool
cmpE accuracy x1 x2 = abs (x1 - x2) < accuracy
(~=) = cmpE 1.0e-10


-- Type signatures are supplied when QuickCheck is otherwise unable to
-- infer the type of the properties arguments. An alternative way of
-- providing the type information would be e.g.:
--
--   prop_constant_one x y = diffUU (\y -> lift x + y) y == (1 :: Double)
--

-- Test cases copied from end of Fad.hs.
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
prop_zeroNewton_1 = zeroNewton (\x->x^2-4) 1 !! 10 == 2
prop_zeroNewton_2 = zeroNewton ((+1).(^2)) (1 :+ 1) !! 10 == 0 :+ 1

-- @inverseNewton@ test case.
prop_inverseNewton = inverseNewton sqrt 1 (sqrt 10) !! 10 == 10

-- @atan2@ test cases.
prop_atan2_shouldBeOne :: Double -> Bool
prop_atan2_shouldBeOne a = diff (\a->atan2 (sin a) (cos a)) a ~= 1


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
  onceCheck (prop_atan2_shouldBeOne (pi/2))

