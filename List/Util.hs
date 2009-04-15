module List.Util

where

-- | The 'zipWithDefaults' function is like zipWith except that it
-- continues until both lists are exhausted, filling in any missing
-- elements with the given defaults.

zipWithDefaults :: (a -> b -> c) -> a -> b -> [a] -> [b] -> [c]
zipWithDefaults f x0 y0 [] [] = []
zipWithDefaults f x0 y0 xs [] = map (flip f y0) xs
zipWithDefaults f x0 y0 [] ys = map (f x0) ys
zipWithDefaults f x0 y0 (x:xs) (y:ys) = f x y:zipWithDefaults f x0 y0 xs ys

-- | The '(!!~)' function indexes into a list like @(!!)@, but sticks
-- with the last element when it runs off the end.

(!!~) :: [a] -> Int -> a

_      !!~ i | i<0 = error "negative index"
[x]    !!~ _       = x
(x:_)  !!~ 0       = x
(x:xs) !!~ i       = xs !!~ (i-1)

-- | The 'indexDefault' function indexes into a list like @(!!)@, but
-- returns the given default when it runs off the end.

indexDefault :: a -> [a] -> Int -> a

indexDefault def _       i | i<0 = error "negative index"
indexDefault def (x:_)   0       = x
indexDefault def []      i       = def
indexDefault def (x:xs)  i       = indexDefault def xs (i-1)
