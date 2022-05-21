module Main where
import           Hlox                           ( interpretString )


main :: IO ()
main = getContents >>= interpretString
