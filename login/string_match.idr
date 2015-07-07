module Main

count : String -> Nat
count x = countList (unpack x) where
  countList : List Char -> Nat
  countList [] = 0
  countList (y :: xs) = 1 + countList xs


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


-- data PasswordEntry : (s : String) -> So (validPasswordDBEntry s) -> Type 


data PasswordEntry : Type where
  MkPasswordEntry : (s : String) -> So (validPasswordDBEntry s) -> PasswordEntry

{-
data PasswordDatabase : Type where
  Nil : 
  -}

-- data PasswordDB = List PasswordEntry


-- passwordDatabase : List PasswordEntry

-- *string_match> pePasswd (MkPasswordEntry "foo:bar:baz:quz" Oh)
-- *... an invalid call like MkPasswordEntry "asdf" Oh will fail.
-- *string_match> pePasswd (MkPasswordEntry "foo:bar:baz:quz" Oh)
-- "bar" : String

-- can I use the proof in the dependent type
-- eg count split token = x ==> length split token array = x+1 ==> nthValue x array is always ok

nthValue : Nat -> Char -> String -> Maybe String
nthValue k token str = let tokens = split (== token) str in
                           index' k tokens

passwordFor : String -> Maybe String
passwordFor entry = nthValue 1 ':' entry 


total pePasswd : PasswordEntry -> String
pePasswd (MkPasswordEntry s x) = let pwd = passwordFor s in
                                     case pwd of 
                                          Nothing => "impossible."
                                          Just str => str


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
--splitV : (s : String) -> So (validPasswordDBEntry s) -> Vect 4 String
--splitV s pf = fromList (split (== ':') s) 

--splitProperty : (s : String) -> So (validPasswordDBEntry s) -> length (split (== ':') s) = 4 
--splitProperty = ?splitProperty_rhs1 

--splitPE : PasswordEntry -> Vect 4 String
--splitPE (MkPasswordEntry s pf) = fromList ( split (== ':') s)

-- TODO the info about the proof in So() is discarded...
--countPE : (s : String) -> So (validPasswordDBEntry s) -> (countCharString ':' s) = 3
--countPE s p = ?countPE_rhs1


validPasswordDBEntryCT : (s : String) -> { default Refl ok : countCharString ':' s = 3} -> Bool
validPasswordDBEntryCT s = True

data PasswordEntryCT : Type where
  MkPasswordEntryCT : (s : String) -> { default Refl ok : countCharString ':' s = 3} -> PasswordEntryCT



countPECT : (s : String) -> {default Refl ok : countCharString ':' s = 3 } -> (countCharString ':' s) = 3
countPECT = proof
  intros
  trivial


countCSEquals : (s : String) -> {default Refl ok : countCharString ':' s = 3} -> length (split (== ':') s) = 4
countCSEquals = ?foo

-- Q: is it possible to put this into a type signature like this?
--data PasswordEntryRT : Type where
--  MkPasswordEntryRT : (s : String) -> (decEq (countCharString ':' s) 3) -> PasswordEntryRT




main : IO ()
main = putStrLn "login ok."

