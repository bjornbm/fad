module List.Util

where

-- | The 'zipWithDefaults' function is like zipWith except that it
-- continues until both lists are exhausted, filling in any missing
-- elements with the given defaults.

zipWithDefaults :: (a -> b -> c) -> a -> b -> [a] -> [b] -> [c]
zipWithDefaults f x0 y0 [] [] = []
zipWithDefaults f x0 y0 xs [] = map (`f`y0) xs
zipWithDefaults f x0 y0 [] ys = map (x0`f`) ys
zipWithDefaults f x0 y0 (x:xs) (y:ys) = f x y:zipWithDefaults f x0 y0 xs ys

-- | The 'indexDefault' function indexes into a list like @(!!)@, but
-- when it runs off the end either returns the given default or, if no
-- default is given, sticks with the last element.

indexDefault :: Maybe a -> [a] -> Int -> a

indexDefault _        _      i | i<0 = error "negative index"
indexDefault _        (x:_)  0       = x
indexDefault Nothing  [x]    _       = x
indexDefault (Just x) []     _       = x
indexDefault m        (_:xs) i       = indexDefault m xs (i-1)
indexDefault Nothing  []     0       = error "no ultimate element"
