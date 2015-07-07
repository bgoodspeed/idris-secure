(* Copyright 2014 main entry point and login code *)

Require Import Ynot.
Require Import Basis.
Require Import List.
Require Import Ascii.
Require Import String.
Require Import List.
Require Import RSep.
Require Import NArith.
Require Import Arith.

Require Import VCRBase.
Require Import VCRIO.
Require Import Message.
Require Import Sumbool.

Require Import StringHelper.

Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.

(*

Require Import Ynot.
Require Import Basis.
Require Import String.
Require Import Ascii.

Require Import VCRIO.
*)
(*
Require Import RSep.
Require Import IO.
Require Import FS.
*)
(*
Local Open Scope string_scope.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
*)

Open Local Scope string_scope.
(*
Open Local Scope stsepi_scope.
Open Local Scope hprop_scope.
*)
Definition get_msg : string := "do login stuff".


(*

Record kstate : Set :=
  mkst { ctab  : option tab
       ; ctabs : list tab
       ; cprocs: list cproc
       ; ktr   : [Trace] 
       }.

*)

(* defn
Fixpoint ReadFile (fm : fd_model) (ms : list mode) (fd : File fm ms) (str : string) {struct str} : Trace :=

*)

(* 
  c <- readfile stdin ;
 *)
(*  
 
   refine ( printStringLn (readfile stdin (ktr (mkst None nil nil [nil]) )  ));
 
   refine ( printStringLn (readfile stdin [nil%Trace] ));  
   refine ( c <- readfile stdin [nil] );

   refine (printStringLn (readfile stdin [[(FakeAction 1234)]] )); 
*)
(*

   refine (printStringLn (readfile stdin [nil] ));


   refine (printStringLn (get_msg));
*)

Definition main : STsep (__) (fun _:unit => hprop_empty).
   refine (
	c <- readfile stdin
           [nil] <@> fhandle stdout * ohandle gout * thandles nil * chandles nil * hprop_empty;
	printStringLn (get_msg ++ get_msg2)
   );
   admit.
   (* sep fail auto. *)
Qed.
