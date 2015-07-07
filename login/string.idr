module string

{-
stringLengthByInduction : String -> Nat
stringLengthByInduction ""     = Z
stringLengthByInduction c ++ s = S stringLengthByInduction s

-}

strMLen : StrM a -> Nat
strMLen StrNil = Z
strMLen (StrCons x xs) = S (strMLen (strM xs))
