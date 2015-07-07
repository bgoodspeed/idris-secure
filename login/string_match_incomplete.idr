module Main

count : String -> Nat
count x = countList (unpack x) where
  countList : List Char -> Nat
  countList [] = 0
  countList (y :: xs) = 1 + countList xs
  
countChar : Char -> String -> Nat
countChar c s = countCharList c (unpack s) where
  countCharList : Char -> List Char -> Nat
  countCharList x [] = 0
  countCharList x (y :: xs) = ?countCharList_rhs_2


main : IO ()
main = putStrLn "login ok."

