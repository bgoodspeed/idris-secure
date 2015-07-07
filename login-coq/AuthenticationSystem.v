Require Import List.
Require Import Ascii.
Require Import Setoid.
Require Import Coq.Strings.String.
Require Import StringHelper.

Open Local Scope string_scope.


Fixpoint matching_in_field (idx: nat) (token: string) (db: list (list string)) : list string := 
	match (db) with
	| nil    => nil
	| x :: y => if andb (prefix token (nth idx x "NOPE")) (prefix (nth idx x "NEVER") token) then
			x
		    else
			matching_in_field idx token y
	end.

Example matchingInFieldSimpleCaseSuccess: matching_in_field 0 "foo" [ ["asdf", "blah"], ["foo", "bar"], ["baz"] ] = ["foo", "bar"].
Proof. reflexivity. Qed.

Lemma emptyDbAlwaysYieldsNilForFixedToken: 
	forall n : nat,
	matching_in_field n "a" [] = [].
Proof. reflexivity. Qed.

Lemma emptyDbAlwaysYieldsNilForFixedField: 
	forall s : string,
	matching_in_field 0 s [] = [].
Proof. reflexivity. Qed.

Lemma emptyDbAlwaysYieldsNil: 
	forall n : nat,
	forall s : string,
	matching_in_field n s [] = [].
Proof. reflexivity. Qed.



Fixpoint string_rev (s : string) : string :=
 match s with
 | EmptyString => EmptyString
 | String c rest => append (string_rev rest) (String c EmptyString)
end.

Fixpoint compute_hash (input: string) : string := string_rev input.

(* XXX should work? *)



Fixpoint check_login (user pass: string) (auth_db: list string) : string := 
	let entry := matching_in_field 0 user (map (fun str => split_string ":" str "" nil) auth_db) in
	let passwd_crypted := compute_hash pass in
	let db_passwd := nth 1 entry "BADPASSWORD" in
				if andb (prefix passwd_crypted db_passwd) (prefix db_passwd passwd_crypted) then
					"ok"
				else
					"no".



Example goodLogin: 
	check_login "user" "passwd" [ "different:asdf:whatever:irrelevent", "another:whatever:asdf", 
        "user:dwssap:foo", "monkey:butler:iiii" ] = "ok".
Proof. reflexivity. Qed.

Example badLogin:
	check_login "user" "BADpasswd" [ "different:asdf:whatever:irrelevent", "another:whatever:asdf", "user:dwssap:foo", "monkey:butler:iiii" ] = "no".
Proof. reflexivity. Qed.

Example noSuchUserLogin:
	check_login "unknownuser" "passwd" [ "different:asdf:whatever:irrelevent", "another:whatever:asdf", "user:dwssap:foo", "monkey:butler:iiii" ] = "no".
Proof. reflexivity. Qed.



Theorem okOnlyIfUserExistsAndPasswordMatches:
	forall username password : string,
	forall password_database : list string,
		In (username ++ ":" ++ (compute_hash password)) password_database ->
			check_login username password password_database = "ok". 
		
		
Proof.

	admit.
Qed.


(*
Theorem badIfNotInPasswordDb:
	forall username password : string,
	forall password_database : list string,
		not (matching) ->
			check_login username password password_database = "bad". 
		
		
Proof.

	admit.
Qed.
*)

(* TODO...
Theorem usersNotInPasswordDBNeverLogin : 
forall
*)
Eval compute in "AuthSystemOk".

(*
Lemma differentStringsHaveDifferentHashes: 
	forall s1 s2 : string,
	(s1 <> s2) -> (compute_hash s1 <> compute_hash s2).
Proof. 


Lemma checkLoginFalseForEmptyDB: 
	forall passwd : string,
	check_login "user" passwd [] = "no".
Proof. reflexivity. Qed.

*)






