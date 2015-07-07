module str

countCharList : Char -> List Char -> Nat 
countCharList _ [] = 0 
countCharList c (x :: xs) with (c == x)
  countCharList c (c :: xs) | True  = S $ countCharList c xs
  countCharList c (_ :: xs) | False = countCharList c xs

countCharString : Char -> String -> Nat 
countCharString c s = countCharList c (unpack s)

validPasswordDBEntry : String -> Bool
validPasswordDBEntry s = (countCharString ':' s) == 3

validateCompileTime : (s : String) -> 
                      {default Refl ok : countCharString ':' s = 3 } 
                      -> Bool
validateCompileTime s = True
{-
*str> :t validateCompileTime ":::"
validateCompileTime ":::" : Bool
Metavariables: str.countPE_rhs1
*str> validateCompileTime ":::"
True : Bool
Metavariables: str.countPE_rhs1
*str> validateCompileTime "::::"
(input):1:21:When elaborating argument ok to function str.validateCompileTime:
  Can't unify
        x = x
  with
        countCharString ':' "::::" = fromInteger 3
              
  Specifically:
  Can't unify
        1
  with
        0
-}


validateRuntime : String -> Bool
validateRuntime s with (decEq (countCharString ':' s) 3)
  validateRuntime s | (Yes p) = True -- doSomethingWithValidStringAndProof s p
  validateRuntime s | (No _)  = False -- invalidStringHandler s ca


countPE : (s : String) -> So (validPasswordDBEntry s) -> (countCharString ':' s) = 3
countPE s p = ?countPE_rhs1


