Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export VectorFields.
Set Default Goal Selector "!".
Require Import Vector.
(* In order to use Full_set in span *)
Require Import Ensembles.

Module Type LinearCombinations.
Axiom v_th : vector_space_theory v_add s_v_mult 0v eq.
(* 
	We'll use the Coq standard library's definition of vectors, which is
	"a list of size n whose elements belong to a set A."
	We need to prove that a set of vectors satisfies the vector space axioms
	under some defined operations, which we will define here:
*)

Global Notation "[ ]" := (nil _) (format "[ ]").
Global Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

(*
	Multiply set of coefficients (Sclrs vector) by set of vectors (V vector) 
	map2 takes fn g, vec s1 s2 ..., vec v1 v2 ..., and returns 
	vec (g s1 v1) (g s2 v2) ... (g sn vn)
*)
Definition linear_com : forall {n : nat} (s : t Sclrs n) (v : t V n), t V n :=
	fix linear_com_fix {n} (s : t Sclrs n) (v : t V n) : t V n := 
		(map2 s_v_mult) s v.

(* The zero vector *)
Global Notation "[0v]" := (nil V).

(* 
	Now we'd like to show that these operations form a vector space:
	...
*)

(* TODO *)
(* Define basis *)

(*
	A linear combination of vectors is a sum
	(a1v1 + a2v2 + a3v3 + ...) where a_i are scalars.
	A set of vectors is linearly independent if ONLY the trivial 
	combination is equal to 0.
*)
Definition lin_indep {n : nat} (vs : t V n) : Prop :=
  forall (coeffs : t Sclrs n),
    fold_left v_add 0v (linear_com coeffs vs) = 0v ->
	(* Forall is a vector proposition that a proposition holds over all elements *)
    Forall (fun y => y = 0) coeffs.

(* 
	Create spanning set:
	Multiply nats by each vector in the set and add.
	fold_left in the standard library works by:
	f b x1 ... xn = f ... (f (f b x1) x2) ... xn

	Proposition of in_span: a spans b if some coefficients
	exist to create b as linear combination of vecs in a
*)
Definition in_span {n : nat} (a : t V n) (b : V) : Prop :=
	exists alpha, b = fold_left v_add 0v (linear_com alpha a).

(*
	Proposition of generates: the set of vectors in the span
	of some set of vectors is equal to the entire vector space.
	This is equivalent to vs being a basis for V.
*)
Definition generates {n : nat} (vs : t V n) : Prop
  :=
    in_span vs = Full_set V.

(* 
	"shiftin" in the standard library adds an element to the end
	of a vector
*)
Infix "++" := shiftin.
(* (LADW 2.5) A vector not in the span is linearly independent *)
Theorem not_span_lin_indep: forall (n : nat) (a : t V n) (b : V),
	~ in_span a b <-> lin_indep (b ++ a).
Proof. 
	intros; split; intros.
	- Admitted.

End LinearCombinations.

