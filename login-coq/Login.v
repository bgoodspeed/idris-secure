(* Copyright 2014 main entry point and login code *)

Require Import Ynot.
Require Import Basis.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import RSep.
Require Import NArith.
Require Import Arith.

(*
Require Import VCRBase.
Require Import VCRIO.
Require Import Message.
Require Import Sumbool.

Require Import FS.

Require Import Coq.Strings.String.
*)

Require Import AuthenticationSystem.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.


Open Local Scope string_scope.
Open Local Scope list_scope.





Definition main : STsep (__) (fun _:unit => hprop_empty).
   refine (printStringLn 
		(check_login "user" "passwd" 
			("different:asdf:whatever:irrelevent" :: "another:whatever:asdf" :: "user:dwssap:foo" :: "monkey:butler:iiii" :: nil)));
   sep auto fail.
Qed.