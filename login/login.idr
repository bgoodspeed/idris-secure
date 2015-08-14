module Main

import System
{-j
vadd : Num a => Vect n a -> Vect n a -> Vect n a
vadd [] [] = []
vadd (x :: xs) (y :: ys) = (x + y) :: vadd xs ys
-}

compute_hash : String -> String
compute_hash x = reverse x

--check_login : String -> String -> List String -> Bool
--check_login user password auth_db = let vl = length auth_db
--  (modNat vl 2) == 0


matching_in_field : Nat -> String -> List (List String) -> List String
matching_in_field idx val [] = [] 
matching_in_field idx val (y :: xs) = let candidate = index' idx y in
                                          case candidate of
                                               Nothing     => []
                                               Just actual => if actual == val then y else matching_in_field idx val xs






mif1 : matching_in_field 0 "A" [ ["A"]] = ["A"]
mif1 = Refl 
mif2 : matching_in_field 0 "B" [ ["A"], ["B"], ["C"]] = ["B"]
mif2 = Refl 

mif3 : matching_in_field 0 "C" [ ["A"]] = []
mif3 = Refl 


mif4 : matching_in_field 1 "A" [ ["A", "B"]] = []
mif4 = Refl 

mif5 : matching_in_field 1 "B" [ ["A", "B"]] = ["A", "B"]
mif5 = Refl 


check_login : String -> String -> List String -> Bool
check_login user pass db = let parsed = map (\x => split (== ':') x) db
                               user_record = matching_in_field 0 user parsed in
                               case user_record of
                                    []        => False
                                    (x :: xs) => let cand_pass = index' 1 (x :: xs) in
                                                     case cand_pass of
                                                          Nothing   => False
                                                          Just cp   => cp == compute_hash pass




cl1 : check_login "u" "p" ["u:p:x"] = True
cl1 = Refl 

cl2 : check_login "u" "p" ["n:p:x"] = False
cl2 = Refl

cl3 : check_login "u" "p" ["u:n:x"] = False
cl3 = Refl 

                                                      
cl4 : check_login "u2" "p2" ["u:p:x", "u2:2p:x"] = True
cl4 = Refl 
                                                      
cl5 : check_login "u2" "p" ["n:p:x", "u2:p2:x"] = False
cl5  = Refl



--fileToList : String -> List String
--fileToList x = do fc <- readFile x
                  --return split (== '\n') fc


main : IO ()
main = do 
  args <- getArgs
  case args of 
       [self] => putStrLn "usage: <user> <pass> <passwd.db>" 
       [_, user] => putStrLn "user: " 
       [_, user, pass] => putStrLn "pass" 
       [_, user, pass, db] => do { f <- readFile db 
                                   case lines f of
                                      []  =>  putStrLn "Could not read from file"
                                      (x :: xs) => if check_login user pass (x :: xs) then putStrLn "Login ok" else putStrLn "Login rejected"
                                 }


