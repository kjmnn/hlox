module Util where


class PrettyPrint a where
    prettyPrint :: a -> String

prettyShort :: PrettyPrint a => a -> String
prettyShort a = if length pretty < 100
    then pretty
    else take 100 pretty <> "..."
    where pretty = prettyPrint a


data ListPair l r = ListPair
    { getLeftList  :: [l]
    , getRightList :: [r]
    }
    deriving Show

instance Semigroup (ListPair l r) where
    (ListPair l r) <> (ListPair l' r') = ListPair (l <> l') (r <> r')

instance Monoid (ListPair l r) where
    mempty = ListPair [] []

toEither :: ListPair l r -> Either [l] [r]
toEither (ListPair l@(x : _) _) = Left l
toEither (ListPair []        r) = Right r
