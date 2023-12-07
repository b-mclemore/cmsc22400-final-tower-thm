Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export VectorFields.
Set Default Goal Selector "!".
Require Import Vector.
Require Import Logic.FunctionalExtensionality.
Require Import Logic.PropExtensionality.

Module Type LinearCombinations.
Axiom v_th : vector_space_theory V Sclrs v_add s_v_mult 0v r_add r_mult 1.
(* 
	We'll use the Coq standard library's definition of vectors, which is
	"a list of size n whose elements belong to a set A."
	NOTE: These vectors DO NOT represent vectors as we've defined them;
	instead, these standard-library vectors represent finite sets of
	our vectors, which is necessary to prove theorems about bases, linear
	combinations, etc.

	Our goal is to prove that given three vector spaces V1, V2, V3, if
	V3 has degree m as a V2 vector space and V2 has degree n as a V1 vector
	space, then V3 has degree m*n as a V1 vector space.
	This requires:
	defining the degree of a vector space ('n' in t V n of
	a generating set);
	defining span and linear independence (required to be a basis);
	constructing (?) the basis for V3:V1 thru V3:V2 & V2:V1

*)

Global Notation "[ ]" := (nil _) (format "[ ]").
Global Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

(*
	Multiply set of coefficients (Sclrs vector) by set of vectors (V vector) 
	map2 takes fn g, vec s1 s2 ..., vec v1 v2 ..., and returns 
	vec (g s1 v1) (g s2 v2) ... (g sn vn)
*)
Definition linear_com : forall {n : nat} (s : t Sclrs n) (v : t V n), V :=
	fix linear_com_fix {n} (s : t Sclrs n) (v : t V n) : V := 
		fold_left v_add 0v ((map2 s_v_mult) s v).

Hint Unfold linear_com : datatypes.

(* Useless test definition *)
Definition first_element {n} (v : t V n) : V :=
	match v with
	| [] => 0v
	| fst :: tail => fst
	end.

(* The zero vector *)
Global Notation "[0v]" := (nil V).

(* 
	Now we'd like to show that given a specific n, all vectors t Sclrs n
	form a vector space:
	Therefore we need addition, scalar multiplication, a zero vector, and an equality operator.
	We then submit these to a vector_space_theory record.
*)

Check vector_space_theory.

(* Definition vector_space_theory *)

(* TODO *)
(* Define subset/subspace *)

(*
	A linear combination of vectors is a sum
	(a1v1 + a2v2 + a3v3 + ...) where a_i are scalars.
	A set of vectors is linearly independent if ONLY the trivial 
	combination is equal to 0.
	Here the proposition is stating that all linear combinations
	of a set of vectors which sum to zero must have only zero as the 
	coefficient.
*)
Definition lin_indep {n : nat} (vs : t V n) : Prop :=
  forall (coeffs : t Sclrs n),
    (linear_com coeffs vs) = 0v ->
	(* Forall is a vector proposition that a proposition holds over all elements *)
    Forall (fun y => y = 0) coeffs.

Check lin_indep.
Check linear_com.
Hint Unfold lin_indep : datatypes.

(* 
	Helper lemma mirroring (LADW 1.6) from VectorFields.v:
	If a set has no elements, it must be the empty set
*)
Lemma empty_set_unique {A : Type} : forall (set : t A 0), set = nil A.
Proof. 
	apply case0 (* From the inductive type of t *). 
	reflexivity. 
Qed.

(* The empty set is linearly independent *)
Theorem empty_set_is_linearly_independent : lin_indep (@nil V).
Proof.
	unfold lin_indep; intros. 
	specialize (empty_set_unique coeffs); intros.
	subst.
	econstructor.
Qed.

(* 
	Create spanning set:
	Multiply nats by each vector in the set and add.
	fold_left in the standard library works by:
	f b x1 ... xn = f ... (f (f b x1) x2) ... xn

	Proposition of in_span: vecs spans v if some coefficients
	exist to create v as linear combination
*)
Definition in_span {n : nat} (vecs : t V n) (v : V) : Prop :=
	exists coeffs, v = (linear_com coeffs vecs).

(* Being in the span of the empty set is equivalent to being the zero vector *)
Theorem span_empty_zero : in_span (@nil V) = fun (x : V) => x = 0v.
Proof.
	apply (functional_extensionality (in_span (@nil V)) (fun x => x = 0v)).
	intros; unfold in_span.
	apply propositional_extensionality; split; intros.
	Admitted.

Hint Unfold in_span : datatypes.

(*
	Proposition of generates: the set of vectors in the span
	of some set of vectors is equal to the entire vector space.
*)
Definition generates {n : nat} (vs : t V n) : Prop
  := forall (v : V), in_span vs v.

Hint Unfold generates : datatypes.

(* A basis must generate a space AND be linearly independent *)
Definition basis {n : nat} (vs : t V n) : Prop
	:= generates vs /\ lin_indep vs.

(* The cardinality (degree) of a basis is simply its size *)
Definition cardinality {n : nat} (vs : t V n) (m : nat) : Prop
	:= exists (es : t V m), basis es.

Hint Unfold generates : datatypes.

(* (LADW 2.2) A basis need not contain 0v *)
Theorem basis_without_zero : forall (n : nat), exists (vs : t V n),
	(* 	There exists a set vs which generates but for all vectors in vs,
		no vector is equal to the zero vector *)
	generates vs /\ ~ Exists (eq 0v) vs.
Proof.
	(* How to prove non-constructively? *)
	(* Might be a poorly described theorem *)
	Admitted.

(* 
	"shiftin" in the standard library adds an element to the end
	of a vector
*)
Infix "++" := shiftin.
(* (LADW 2.5) A vector not in the span is linearly independent *)
Theorem not_span_lin_indep: forall (n : nat) (a : t V n) (b : V),
	~ in_span a b -> lin_indep (b ++ a).
Proof. 
	(* Informally: ... *)
	unfold not. intros. 
	- Admitted.

End LinearCombinations.

Module Type Subspaces.
Axiom v_th : vector_space_theory V Sclrs v_add s_v_mult 0v r_add r_mult 1.

(* A vector space V2 is a subspace of a vector space V1 if V1 can be described
	as a vector space over V2 *)

End Subspaces.
