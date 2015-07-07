module Main

count : String -> Nat
count x = countList (unpack x) where
  countList : List Char -> Nat
  countList [] = 0
  countList (y :: xs) = 1 + countList xs

{-
countChar : Char -> String -> Nat
countChar c s = countCharList c (unpack s) where
  countCharList : (c : Char) -> List Char -> Nat
  countCharList x [] = 0
  countCharList c (c :: xs) = ?countCharList_rhs_2
  countCharList c (x :: xs) = ?countCharList_rhs_3
  -}
{-
foo : (c : Char) -> (c2 : Char) -> Nat
foo c c = 1
foo _ _ = 2
-}
{-
countCharList : Char -> List Char -> Nat
countCharList _ [] = 0
countCharList c (c :: xs) = 1 + countCharList c xs
countCharList c (x :: xs) = countCharList c xs
-}

countCharList : Char -> List Char -> Nat
countCharList _ [] = 0
countCharList c (x :: xs) with (c == x)
    countCharList c (c :: xs) | True  = S $ countCharList c xs
    countCharList c (_ :: xs) | False = countCharList c xs

countCharString : Char -> String -> Nat
countCharString c s = countCharList c (unpack s)

validPasswordDBEntry : String -> Bool
validPasswordDBEntry s = (countCharString ':' s) == 3

-- TODO how to turn this notion into a type, with a constructor guard maybe?  how do.
addPasswordDBEntry : (s : String) -> So ( validPasswordDBEntry s) -> List String -> List String
addPasswordDBEntry s pf xs = s :: xs

nthValue : Nat -> Char -> String -> Maybe String
nthValue k token str = let tokens = split (== token) str in
                           index' k tokens

passwordFor : String -> Maybe String
passwordFor entry = nthValue 1 ':' entry 


matchingInField : Nat -> Char -> String -> List String -> Maybe String
matchingInField n token str [] = Nothing
matchingInField n token str (x :: xs) = let v = nthValue n token x in
                                            case v of
                                                 Nothing => matchingInField n token str xs
                                                 Just s  => if s == str then
                                                                        Just x
                                                            else
                                                                        matchingInField n token str xs

matchingUsername : String -> List String -> Maybe String
matchingUsername username db = matchingInField 0 ':' username db



computeHash : String -> String
computeHash x = reverse x


-- UUUGLY.
data AuthenticationResult = OK | BAD | NO_USER | MALFORMED_LINE

checkLogin : String -> String -> List String -> AuthenticationResult
checkLogin username passwordInput passwordDb = let password = computeHash passwordInput in
                                                   let entry = matchingUsername username passwordDb in
                                                       case entry of
                                                            Nothing => NO_USER
                                                            Just s  => case passwordFor s of
                                                                            Nothing => MALFORMED_LINE
                                                                            Just actualPassword => if actualPassword == password then OK else BAD

{-
inBounds : Int -> Int -> Bool
inBounds x y = x >= 0 && x < 640 && y >= 0 && y < 480
drawPoint : (x : Int) -> (y : Int) -> So (inBounds x y) -> IO ()
drawPoint x y p = unsafeDrawPoint x y
-}

main : IO ()
main = putStrLn "login ok."

