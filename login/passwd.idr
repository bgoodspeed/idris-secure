module Main
{-
letterCount : (c : Char) -> String -> Int
letterCount _ []        = 0
letterCount c (c :: xs) = 1 + letterCount c xs
letterCount c (x :: xs) = letterCount xs
-}


letterCount : Char -> String -> Int
letterCount c ""        = 0
letterCount c (x :: xs) = ?foo

main : IO ()
main = putStrLn $ show $ (letterCount ':' "foo:bar:baz")
