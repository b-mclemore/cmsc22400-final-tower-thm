Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export VectorFields.
Set Default Goal Selector "!".
Require Import Ensembles.
Require Import Vector.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.

Module Type LinearCombinations.
(* 
	We'll use the Coq standard library's definition of vectors, which is
	"a list of size n whose elements belong to a set A."
	We need to prove that a set of vectors satisfies the vector space axioms
	under some defined operations, which we will define here:
*)

Global Notation "[ ]" := (nil _) (format "[ ]").
Global Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

(*	Vector addition *)
Definition vec_add : forall {n : nat} (v1 : t V n) (v2 : t V n), t V n :=
	fix vec_add_fix {n} (v1 : t V n) (v2 : t V n) : t V n := 
		((map2 v_add) v1 v2).

(* Scalar - vector multiplication *)
Definition s_vec_mult : forall {n : nat} (s : Sclrs) (v: t V n), t V n :=
	fix s_vec_mult_fix {n} (s : Sclrs) (v : t V n) : t V n := 
		match v with
		| [] => []
		| hd :: tl => (s *v hd) :: (s_vec_mult_fix s tl)
		end.

(* The zero vector *)
Global Notation "[0v]" := (nil V).

(* 
	Now we'd like to show that these operations form a vector space:
	...
*)

(* TODO *)
(* Define basis *)

(* 
	Create spanning set:
	Multiply nats by each vector in the set and add.
	fold_left in the standard library works by:
	f b x1 ... xn = f ... (f (f b x1) x2) ... xn

	Proposition of span: a spans b if some coefficients
	exist to create b as linear combination
*)
Definition span_comb {n : nat} (a : t V n) : V -> Prop :=
	fun b => exists alpha, b = fold_left v_add 0v (s_vec_mult alpha a).

End LinearCombinations.

