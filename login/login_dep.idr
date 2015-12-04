module Main

import System
import Data.Fin
import Data.Vect

compute_hash : String -> String
compute_hash x = reverse x



data LoginRecord : Type where
  MkLoginRecord : Vect 3 String -> LoginRecord


-- TODO note this actually works -- if you add something to the end it will break
splitv : (s : String) -> Vect (length (split (== ':') s)) String
splitv x = let xs = split (== ':') x 
               vs = fromList xs in
               vs
        



vectToLoginRecord : {n : Nat} -> Vect n String -> Maybe LoginRecord
vectToLoginRecord {n} xs = case natToFin 0 n of
                Nothing  => Nothing
                Just  z  => let un = index z xs in
                                case natToFin 1 n of 
                                     Nothing => Nothing 
                                     Just o  => let ep = index o xs in
                                                    case natToFin 2 n of
                                                         Nothing => Nothing
                                                         Just t  => Just (MkLoginRecord [un, ep, (index t xs)])

usernameFrom : LoginRecord -> String
usernameFrom (MkLoginRecord xs) = index 0 xs

hashedPasswordFrom : LoginRecord -> String
hashedPasswordFrom (MkLoginRecord xs) = index 1 xs

  
string_to_login_record_vector : String -> Maybe LoginRecord
string_to_login_record_vector s = let vs = splitv s in
                                      vectToLoginRecord vs

string_to_login_record_vector_empty_is_nothing : string_to_login_record_vector "" = Nothing
string_to_login_record_vector_empty_is_nothing = Refl 


data PasswordDatabase : Type where
  MkPasswordDatabase : List LoginRecord -> PasswordDatabase


--validate_login 

-- HACK
--instance Eq LoginRecord where
--  (==) a b = True

stringsToLoginRecords : List String -> List LoginRecord
stringsToLoginRecords [] = [] 
stringsToLoginRecords (x :: xs) = case string_to_login_record_vector x of
                                       Nothing => stringsToLoginRecords xs
                                       Just lr => lr :: stringsToLoginRecords xs

{-
stringsToLoginRecords : List String -> List LoginRecord
stringsToLoginRecords xs = 
  let candidates = map (\x => string_to_login_record_vector x) xs
                               valids = filter (\x => not (x == Nothing)) candidates 
                               
                               ?asdf
                               -}

stringsToPasswordDatabase : List String -> PasswordDatabase
stringsToPasswordDatabase xs = MkPasswordDatabase (stringsToLoginRecords xs )

matchesLoginRecord : String -> String -> LoginRecord -> Bool
matchesLoginRecord u p lr = (u == (usernameFrom lr)) && (compute_hash p) == (hashedPasswordFrom lr)



validateLogin : String -> String -> PasswordDatabase -> Bool
validateLogin u p (MkPasswordDatabase []) = False 
validateLogin u p (MkPasswordDatabase (y :: xs)) = any (matchesLoginRecord u p) (y :: xs) 

strLR : String -> String -> String -> LoginRecord
strLR x x1 x2 = MkLoginRecord [x, x1, x2] 


emptyPasswdDB : PasswordDatabase
emptyPasswdDB = MkPasswordDatabase [] 


samplePasswdDB : PasswordDatabase
samplePasswdDB = let lr = strLR "user" "pass" "whatever" in
                    MkPasswordDatabase [lr]


samplePermitsLogin : validateLogin "user" "ssap" samplePasswdDB = True
samplePermitsLogin = Refl

sampleForbidsBadPassword : validateLogin "user" "wrong" samplePasswdDB = False
sampleForbidsBadPassword = Refl

sampleForbidsAllPasswordWithWrongUsername : (pass : String) -> validateLogin "badusername" pass samplePasswdDB = False
sampleForbidsAllPasswordWithWrongUsername pass = Refl 

-- TODO add to proofs and tactics section and appropriate repos
anyAndDelayFalseIsFalse : (b : Bool) -> b && False = False
anyAndDelayFalseIsFalse b = ?anyAndDelayFalseIsFalse_rhs1

anyIntAndIntToBoolAndDelayFalseIsFalse : (i : Int) -> (intToBool i) && False = False
anyIntAndIntToBoolAndDelayFalseIsFalse i = ?anyIntAndIntToBoolAndDelayFalseIsFalse_rhs


sampleForbidsAllUsernamesWithBadPassword : (s : String) -> validateLogin s "wrong" samplePasswdDB = False
sampleForbidsAllUsernamesWithBadPassword s = ?badPasswordPF


emptyPasswordDBMeansNoLogin : (u : String) -> (p : String) -> validateLogin u p emptyPasswdDB = False
emptyPasswordDBMeansNoLogin u p = Refl


badLoginRecordsMeanFalseForAllUserAndPasswords : (lr : LoginRecord) -> matchesLoginRecord "foo" "bar" lr = False -> validateLogin "foo" "bar" (MkPasswordDatabase [lr]) = False 
badLoginRecordsMeanFalseForAllUserAndPasswords lr prf = ?badLoginRecordsMeanFalseForAllUserAndPasswords_rhs



allBadLoginRecordsMeanFalseForAllUserAndPasswords : (u : String) -> (p : String) -> (lr : LoginRecord) -> matchesLoginRecord u p lr = False -> validateLogin u p (MkPasswordDatabase [lr]) = False 
allBadLoginRecordsMeanFalseForAllUserAndPasswords u p lr prf = ?allBadLoginRecordsMeanFalseForAllUserAndPasswords_rhs



allBadLoginRecordsMeanFalseForAllUserAndPasswords2 : (u : String) -> (p : String) -> (lr : LoginRecord) -> 
                                                     (lr2 : LoginRecord) -> matchesLoginRecord u p lr = False -> 
                                                      matchesLoginRecord u p lr2 = False ->
                                                            validateLogin u p (MkPasswordDatabase [lr, lr2 ]) = False 
allBadLoginRecordsMeanFalseForAllUserAndPasswords2 u p lr lr2 prf prf1 = ?allBadLoginRecordsMeanFalseForAllUserAndPasswords2_rhs




Main.allBadLoginRecordsMeanFalseForAllUserAndPasswords2_rhs = proof
  intros
  rewrite prf
  rewrite sym prf
  rewrite prf1
  rewrite sym prf1
  trivial


Main.allBadLoginRecordsMeanFalseForAllUserAndPasswords_rhs = proof
  intros
  rewrite prf
  trivial


Main.badLoginRecordsMeanFalseForAllUserAndPasswords_rhs = proof
  intros
  rewrite prf
  trivial


Main.badPasswordPF = proof
  intros
  case intToBool (prim__eqString s "user")
  trivial
  trivial


Main.anyIntAndIntToBoolAndDelayFalseIsFalse_rhs = proof
  intros
  case intToBool i
  trivial
  trivial


Main.anyAndDelayFalseIsFalse_rhs1 = proof
  intros
  compute
  case b
  trivial
  trivial


