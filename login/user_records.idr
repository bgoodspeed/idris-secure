module UserRecords

-- Thanks Dr. Brady 

data ValidEntry : List String -> Type where
  DB: (w,x,y,z : String) -> ValidEntry [w,x,y,z]


-- MkPasswordEntryCT : (s : String) -> {auto ok : countCharString ':' s = 3} -> PasswordEntryCT

isValid : String -> Maybe (xs ** ValidEntry xs)
isValid str with (split (== ':') str)
  isValid str | [w,x,y,z] = Just (_ ** DB w x y z)
  isValid str | _         = Nothing

getUserName : ValidEntry xs -> String
getUserName (DB w x y z) = w


