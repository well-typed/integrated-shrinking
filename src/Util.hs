module Util where

twice :: Applicative m => m a -> m (a, a)
twice f = (,) <$> f <*> f

splits :: [a] -> [([a], a, [a])]
splits []     = []
splits (x:xs) = ([], x, xs) : map (\(as, b, cs) -> (x : as, b, cs)) (splits xs)

dropElement :: [a] -> [[a]]
dropElement xs = [ as ++ cs | (as, _b, cs) <- splits xs ]

deleteAtIx :: Int -> [a] -> [a]
deleteAtIx _ []     = error "deleteAtIx: invalid arguments"
deleteAtIx 0 (_:xs) = xs
deleteAtIx n (x:xs) = x : deleteAtIx (n - 1) xs
