module Parser
    ( Parser(..)
    , ParseResult(..)
    , extractOutput
    , (<<*)
    , mmany
    , msome
    , exact
    , single
    , single'
    , oneOf
    , parseError
    ) where

import           Control.Applicative            ( Alternative(..)
                                                , Applicative(..)
                                                )

data ParseResult e i o
    = Fail
    | Error e i
    | Success o i
    deriving (Eq, Show)

instance Functor (ParseResult e i) where
    fmap f Fail          = Fail
    fmap f (Error   e i) = Error e i
    fmap f (Success s i) = Success (f s) i

extractOutput :: ParseResult e i o -> o
extractOutput (Success s i) = s
extractOutput _ = error "attempted to extract output from a Fail or Error"


newtype Parser e i o = Parser
    { runParser :: i -> ParseResult e i o
    }

instance Functor (Parser e i) where
    fmap f (Parser g) = Parser (fmap f . g)

instance Applicative (Parser e i) where
    pure = Parser . Success
    (Parser f) <*> (Parser g) = Parser $ \x -> case f x of
        Fail        -> Fail
        Error   e y -> Error e y
        Success h y -> h <$> g y

-- a "peek" version of (<*) that doesn't consume additional input
infixl 4 <<*
(<<*) :: Parser e i a -> Parser e i b -> Parser e i a
(Parser f) <<* (Parser g) = Parser $ \x -> case f x of
    Fail        -> Fail
    Error   e r -> Error e r
    Success o r -> case g r of
        Fail        -> Fail
        Error   e r -> Error e r
        Success _ _ -> Success o r

instance Alternative (Parser e i) where
    empty = Parser (const Fail)
    (Parser f) <|> (Parser g) = Parser $ \x -> case f x of
        Fail        -> g x
        Error   e i -> Error e i
        Success s i -> Success s i

mmany :: (Alternative f, Monoid m) => f m -> f m
mmany v = msome v <|> pure mempty
msome :: (Alternative f, Monoid m) => f m -> f m
msome v = liftA2 (<>) v (mmany v)

parseError :: (i -> e) -> Parser e [i] o
parseError f = Parser p  where
    p (x : xs) = Error (f x) (x : xs)
    p _ =
        error "parseError invoked on empty list (maybe use `some` and `many`?)"

parseErrorMunch :: (i -> e) -> Parser e [i] o
parseErrorMunch f = Parser p  where
    p (x : xs) = Error (f x) xs
    p _ =
        error "parseError invoked on empty list (maybe use `some` and `many`?)"


single :: (a -> Bool) -> Parser e [a] a
single f = Parser single  where
    single []       = Fail
    single (x : xs) = if f x then Success x xs else Fail

single' :: Eq a => a -> Parser e [a] a
single' x = single (== x)

exact :: Eq a => [a] -> Parser e [a] [a]
exact []       = pure []
exact (x : xs) = liftA2 (:) (single (== x)) (exact xs)

oneOf :: (Eq a) => [a] -> Parser e [a] a
oneOf xs = single (`elem` xs)



