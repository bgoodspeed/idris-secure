module Main
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
matching_in_field idx token [] = []
matching_in_field idx token (x :: y) = if (token == (index 1 x))
                                        then x
                                        else matching_in_field idx token y




main : IO ()
main = putStrLn "login ok."

