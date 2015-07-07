Require Import Arith.
Require Import String.
Require Import Ascii.
Require Import List.
Require Import Coq.Strings.String.

Local Open Scope string_scope.

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).


Fixpoint split_string_r (delimiter : ascii) ( str current_word : string) (accumulated_words : list string) 
	{struct str} : list string :=
	match str with
	| EmptyString => current_word :: accumulated_words
	| String a b  => if prefix (String delimiter EmptyString) str then
				split_string_r delimiter b EmptyString (current_word :: accumulated_words)  
			 else
				split_string_r delimiter b (append current_word (substring 0 1 str)) accumulated_words
	end.

Definition split_string (delimiter : ascii) ( str current_word : string) (accumulated_words : list string) : list string :=
	rev (split_string_r delimiter str current_word accumulated_words).


Definition split_string_simplified (delimiter : ascii) (str : string) : list string := split_string delimiter str "" nil.

Fixpoint token_count (token : ascii) (str : string) : nat := 
	match str with
	| EmptyString => 0
	| String a b  => if ascii_dec token a then
				S (token_count token b)
			 else
				token_count token b
	end.



Example matchingSplitsBegin_r: split_string_r ":" ":foo:bar" "" nil = ["bar", "foo", ""].
Proof. reflexivity. Qed.

Example matchingSplitsEndOmitted_r: split_string_r ":" "foo:bar:" "" nil = ["", "bar", "foo"].
Proof. reflexivity. Qed.

Example blankYieldsEmpty: split_string ":" "" "" nil = [""].
Proof. reflexivity. Qed.

Example blankYieldsCurWord: split_string ":" "" "ben" nil = ["ben"].
Proof. reflexivity. Qed.

Example noMatchingCharYieldsOne: split_string ":" "asdf" "" nil = ["asdf"].
Proof. reflexivity. Qed.

Example matchingSplits: split_string ":" "foo:bar" "" nil = ["foo", "bar"].
Proof. reflexivity. Qed.

Example matchingSplitsBegin: split_string ":" ":foo:bar" "" nil = ["", "foo", "bar"].
Proof. reflexivity. Qed.

Example matchingSplitsEndOmitted: split_string ":" "foo:bar:" "" nil = ["foo", "bar", ""].
Proof. reflexivity. Qed.

Example matchingSplitsEndOmittedSimple: split_string_simplified ":" "foo:bar:" = ["foo", "bar", ""].
Proof. reflexivity. Qed.

Example noOccurencesOfTokenBlank: token_count ":" "" = 0.
Proof. reflexivity. Qed.

Example noOccurencesOfTokenString: token_count ":" "asdfasdfasfdasfdf" = 0.
Proof. reflexivity. Qed.

Example occurencesOfTokenString: token_count ":" ":asdfas:dfasfda:sfdf:" = 4.
Proof. reflexivity. Qed.

(*
Lemma rev_appP : forall A (l1 : list A),
rev_app l1 nil = rev l1.
rev_length*)

Lemma revEmptyIsEmpty :
	rev [ "" ] = [ "" ].
Proof. reflexivity. Qed.

Lemma anyDelimiterOnBlankGivesEmptyStringArray :
	forall a : ascii,
	split_string_r a "" "" nil = [ "" ].
Proof. reflexivity. Qed. 


Lemma anyDelimiterOnBlankGivesEmptyStringArrayNonRev :
	forall a : ascii,
	split_string a "" "" nil = [ "" ].
Proof.
	intros.
	simpl.
	unfold split_string.
	split.
Qed.

Lemma anyDelimiterOnBlankGivesEmptyStringArrayNonRevB :
	forall a : ascii,
	split_string a "" "" nil = [ "" ].
Proof.

Theorem anyDelimiterOnBlankGivesArraySizedAtLeastOne :
	forall a : ascii,
	List.length (split_string_r a "" "" nil) >= 1.
Proof.
	intros a.
	rewrite anyDelimiterOnBlankGivesEmptyStringArray.
	simpl.
	auto.
Qed.


Lemma anyDelimiterOnBlankGivesEmptyStringArraySimple : forall a : ascii, split_string_simplified a "" = [ "" ].
Proof. 
	intros.
	unfold split_string_simplified.
	auto.
Qed. 


Lemma anyDelimiterOnBlankGivesArraySizedAtLeastOneSimple :
	forall a : ascii,
	List.length (split_string_simplified a "") >= 1.
Proof.
	intros a.
	rewrite anyDelimiterOnBlankGivesEmptyStringArraySimple.
	simpl.
	auto.
Qed.

Lemma consOnlyIncreasesLengthOfList :
	forall l : list string,
	forall x : string,
	List.length (l) < List.length (x :: l).
Proof.
	auto.
Qed.

Lemma consNeverDecreasesLengthOfList :
	forall l : list string,
	forall x : string,
	List.length (x :: l) > List.length (l).
Proof.
	auto.
Qed.

(* TODO how to coerce type of nil
Lemma lengthNilLessThanOrEqualLengthAnything :
	forall l : list string,
	List.length (nil % string) <= List.length (l).
Proof.

*)


Lemma consAlwaysYieldsGTEZero :
	forall l : list string,
	forall x : string,
	0 <= List.length (x :: l).
Proof.
	intros.
	auto.
	intuition.
Qed.


Lemma consAlwaysYieldsGTEZeroNil :
	forall l : list string,
	forall x : string,
	List.length (nil : list string) <= List.length (x :: l).
Proof.
	intros.
	auto.
	intuition.
Qed.

(*
Lemma splitStringRUsesOnlyConsOnLists :
	forall a : ascii,
	forall str : string,
	forall current_word : string,
	forall accumulated_words : list string,
	List.length accumulated_words <= List.length (split_string_r a str current_word accumulated_words).
Proof.


Require Import Coq.Lists.List.
Local Open Scope list_scope.
*)


Lemma anyDelimitedOnAnyStringGivesAtLeastOne : 
forall a : ascii, 
forall s : string, List.length (split_string_simplified a s) >= 1.
Proof.
intros a s.
induction s.
left ; reflexivity.
unfold split_string_simplified.
unfold split_string.
auto.
admit.
Qed.



Lemma anyDelimitedOnAnyStringGivesAtLeastOneA : 
forall a : ascii, 
forall s : string, List.length (split_string_simplified a s) >= 1.
Proof.

(*
Constructor.
*)

(*
intros.
elim s.
 apply anyDelimiterOnBlankGivesArraySizedAtLeastOneSimple.
 
 intros.
 case s0.

*)




(* try using a let expression to introduce new vars into the content *)
(* https://github.com/maximedenes/native-coq/blob/master/theories/Strings/String.v
Theorem splitResultIsTokenCountPlusOne : 
	forall a : ascii,
	forall s : string,
	S (token_count a s) = List.length (split_string_simplified a s).
	*)


Eval compute in "ok".


