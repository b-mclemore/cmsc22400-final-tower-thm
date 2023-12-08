Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export VectorFields.
Set Default Goal Selector "!".
Require Field.
Import Field_theory.
Require Import Vector.
Require Import Logic.FunctionalExtensionality.

(* 
	Tower theorem:
	If V3 is a V2 vector space with degree m and V2 is a V1 vector space
	with degree n, V3 is a V1 vector space with degree
	vector space with degree m * n.
	Let U be the basis of V3/V2 as a vector space and V be the basis of V2/V1
	as a vector space, with vectors {u_i} and {v_j} respectively. Then we claim
	that the set of vectors {u_i * v_j} is a basis for V3/V1. 
	To prove this, we must show that this set is linearly independent and that
	it spans (generates) V3/V1.
	Once this is complete, it is clear that this basis has degree m * n, so we
	are done.
*)

(* ============================================================================== *)

(*	Setup	*)

(* ============================================================================== *)

Module Type TowerTheorem.
Axiom (F1 F2 F3 : Type).
Context `{Field F1}.
Context `{Field F2}.
Context `{Field F3}.
(* 
	Here we are using Field notation to make the extension property obvious.
	We are taking as a given that F3/F2, F2/F1, and F3/F1 are valid field
	extensions, which by definition means that F3 is a F2-vector space, etc.
	So we define operations for each vector space here. 
*)
(* Identities *)
Axiom (E1_0 E1_1 : F1) (E2_0 E2_1 : F2) (E3_0 E3_1 : F3).
Notation "0_1" := E1_0.
Notation "1_1" := E1_1.
Notation "0_2" := E2_0.
Notation "1_2" := E2_1.
Notation "1_3" := E3_1.
Notation "0_3" := E3_0.
(* Vector (and scalar) addition *)
Axiom (add_1 : F1 -> F1 -> F1) (add_2 : F2 -> F2 -> F2) (add_3 : F3 -> F3 -> F3).
Infix "+_1" := add_1 (at level 50).
Infix "+_2" := add_2 (at level 50).
Infix "+_3" := add_3 (at level 50).
(* Scalar multiplication *)
Axiom (mult_1 : F1 -> F1 -> F1) (mult_2 : F2 -> F2 -> F2) (mult_3 : F3 -> F3 -> F3).
Infix "*_1" := mult_1 (at level 60).
Infix "*_2" := mult_2 (at level 60).
Infix "*_3" := mult_3 (at level 60).
(* Scalar-vector multiplication (extension operation, sort of) *)
Axiom (mult_21 : F1 -> F2 -> F2) (mult_32 : F2 -> F3 -> F3) (mult_31 : F1 -> F3 -> F3).
Infix "*_21" := mult_21 (at level 60).
Infix "*_32" := mult_32 (at level 60).
Infix "*_31" := mult_31 (at level 60).
(* Vector space axioms (assumed) *)
Axiom E21_th : vector_space_theory F2 F1 add_2 mult_21 0_2 add_1 mult_1 1_1.
Axiom E32_th : vector_space_theory F3 F2 add_3 mult_32 0_3 add_2 mult_2 1_2.
Axiom E31_th : vector_space_theory F3 F1 add_3 mult_31 0_3 add_1 mult_1 1_1.

(* 
	We need a few more operations in order to state also that each is a field,
	though these are unnecessary for the proof later:
	Subtraction, division, and the additive/multiplicative inverse operations
*)
Axiom (min_1 div_1 : F1 -> F1 -> F1) (ainv_1 minv_1 : F1 -> F1).
Axiom F1_th : field_theory 0_1 1_1 add_1 min_1 mult_1 ainv_1 div_1 minv_1 eq.
Axiom (min_2 div_2 : F2 -> F2 -> F2) (ainv_2 minv_2 : F2 -> F2).
Axiom F2_th : field_theory 0_2 1_2 add_2 min_2 mult_2 ainv_2 div_2 minv_2 eq.
Axiom (min_3 div_3 : F3 -> F3 -> F3) (ainv_3 minv_3 : F3 -> F3).
Axiom F3_th : field_theory 0_3 1_3 add_3 min_3 mult_3 ainv_3 div_3 minv_3 eq.

(* 
	To continue with the proofs, we'll use the Coq standard library's 
	definition of vectors, which is "a list of size n whose elements belong to 
	a set A." NOTE: These vectors DO NOT represent vectors as we've defined 
	them; instead, these standard-library vectors represent finite sets of
	our vectors, which is necessary to prove theorems about bases, linear
	combinations, etc.
	We use vectors instead of the standard library's lists because it's useful
	to have the length embedded (especially since the tower theorem is essentially
	a theorem concerning the product of these lengths), but the standard library
	does allow for vector--list translations, if we want to switch types
*)

Global Notation "[ ]" := (nil _) (format "[ ]").
Global Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

(*
	Multiply set of coefficients by set of vectors
	map2 takes fn g, vec s1 s2 ..., vec v1 v2 ..., and returns 
	vec (g s1 v1) (g s2 v2) ... (g sn vn)
	Takes the types, the functions, a zero vector, then the set of vectors
	and scalars
	We have multiple definitions because otherwise we can't have explicit functions
	within the definition body, meaning all operations and identities would have to
	be supplied.
*)

Definition linear_com_21 : forall {n : nat} (s : t F1 n) (v : t F2 n), F2 :=
	fix linear_com_fix {n} (s : t F1 n) (v : t F2 n) : F2 := 
		fold_left add_2 0_2 ((map2 mult_21) s v).

Definition linear_com_32 : forall {n : nat} (s : t F2 n) (v : t F3 n), F3 :=
	fix linear_com_fix {n} (s : t F2 n) (v : t F3 n) : F3 := 
		fold_left add_3 0_3 ((map2 mult_32) s v).

Definition linear_com_31 : forall {n : nat} (s : t F1 n) (v : t F3 n), F3 :=
	fix linear_com_fix {n} (s : t F1 n) (v : t F3 n) : F3 := 
		fold_left add_3 0_3 ((map2 mult_31) s v).

(* Injectivity lemmas *)
Lemma linear_com_32_inj : forall (n : nat) (x y : t F2 n) (U : t F3 n), 
	linear_com_32 x U = linear_com_32 y U -> x = y.
Proof.
	intros. Admitted.

(*
	A linear combination of vectors is a sum
	(a1v1 + a2v2 + a3v3 + ...) where a_i are scalars.
	A set of vectors is linearly independent if ONLY the trivial 
	combination is equal to 0.
	Here the proposition is stating that all linear combinations
	of a set of vectors which sum to zero must have only zero as the 
	coefficient.
*)
Definition lin_indep_21 {n : nat} (vs : t F2 n) : Prop :=
  forall (coeffs : t F1 n),
    (linear_com_21 coeffs vs) = 0_2 ->
	(* Forall is a vector proposition that a proposition holds over all elements *)
    Forall (fun y => y = 0_1) coeffs.

Definition lin_indep_32 {n : nat} (vs : t F3 n) : Prop :=
	forall (coeffs : t F2 n),
		(linear_com_32 coeffs vs) = 0_3 ->
		Forall (fun y => y = 0_2) coeffs.

Definition lin_indep_31 {n : nat} (vs : t F3 n) : Prop :=
	forall (coeffs : t F1 n),
		(linear_com_31 coeffs vs) = 0_3 ->
		Forall (fun y => y = 0_1) coeffs.

(* 
	Create spanning set:
	Multiply nats by each vector in the set and add.
	fold_left in the standard library works by:
	f b x1 ... xn = f ... (f (f b x1) x2) ... xn

	Proposition of in_span: vecs spans v if some coefficients
	exist to create v as linear combination
*)
Definition in_span_21 {n : nat} (vecs : t F2 n) (v : F2) : Prop :=
	exists coeffs, v = (linear_com_21 coeffs vecs).

Definition in_span_32 {n : nat} (vecs : t F3 n) (v : F3) : Prop :=
	exists coeffs, v = (linear_com_32 coeffs vecs).

Definition in_span_31 {n : nat} (vecs : t F3 n) (v : F3) : Prop :=
	exists coeffs, v = (linear_com_31 coeffs vecs).

(*
	Proposition of generates: the set of vectors in the span
	of some set of vectors is equal to the entire vector space.
*)
Definition generates_21 {n : nat} (vs : t F2 n) : Prop
	:= forall (v : F2), in_span_21 vs v.

Definition generates_32 {n : nat} (vs : t F3 n) : Prop
	:= forall (v : F3), in_span_32 vs v.

Definition generates_31 {n : nat} (vs : t F3 n) : Prop
	:= forall (v : F3), in_span_31 vs v.

(* A basis must generate a space AND be linearly independent *)
Definition basis_21 {n : nat} (vs : t F2 n) : Prop
	:= generates_21 vs /\ lin_indep_21 vs.

Definition basis_32 {n : nat} (vs : t F3 n) : Prop
	:= generates_32 vs /\ lin_indep_32 vs.

Definition basis_31 {n : nat} (vs : t F3 n) : Prop
	:= generates_31 vs /\ lin_indep_31 vs.

(* The cardinality (degree) of a basis is simply its size *)
Definition cardinality_21 (m : nat) : Prop
	:= exists (es : t F2 m), basis_21 es.

Definition cardinality_32 (m : nat) : Prop
	:= exists (es : t F3 m), basis_32 es.

Definition cardinality_31 (m : nat) : Prop
	:= exists (es : t F3 m), basis_31 es.

(* ============================================================================== *)

(*	Lengths of vectors	*)

(* ============================================================================== *)

(* 
	In order to prove that the combination of these bases form a basis, we need
	to define a notion of set-combination; that is, we need to multiply each vector
	in each set by each vector in the other set.
	This only needs to be defined for F3 * F2, since U is F3/F2 and V is F2/F1.
	We also want a helper lemma that the length of a set-combination is equal to
	the product of the lengths of each set.
*)
Require Import List.

Fixpoint cart_prod (U : list F3) (V : list F2) : list F3 :=
	match U with
	| nil => nil
	| cons x t => (map (fun y:F2 => (mult_32 y x)) V) ++ (cart_prod t V)
	end.

Definition cart_vec {m n : nat} (U : t F3 m) (V : t F2 n) : list F3 :=
	(cart_prod (to_list U) (to_list V)).

(* Cons-ing before turning vec into list is the same as cons-ing after *)
Lemma preserve_cons : forall (n : nat) (F : Type) (h : F) (U : t F n),
	(to_list (Vector.cons F h n U)) = (cons h nil) ++ (to_list U).
Proof.
	trivial. (* <--- I wish this worked more often! *)
Qed.

(* The vector length is the same as the list length *)
Lemma vec_length { F : Type}: forall (n : nat) (U : t F n),
	length (to_list U) = n.
Proof.
	intros. induction U. 
	- simpl; auto.
	- auto. rewrite preserve_cons. simpl. auto.
Qed.

(* Helper tactic for the assertions we'll be making *)
Ltac by_simple_induction lst :=
	intros;
	induction lst; simpl; auto.

(* Appending two lists has a length equal to the sum of their lengths *)
Lemma app_lst_length {F : Type} : forall (lst lst2 : list F),
	length (lst ++ lst2) = (length lst) + (length lst2).
Proof.
	by_simple_induction lst.
Qed.

(* Mapping onto a list preserves length *)
Lemma map_lst_length : forall (lst : list F2) (f : F2 -> F3),
	length (map f lst) = length lst.
Proof.
	by_simple_induction lst.
Qed.

(* Length of a product is product of lengths, for lists *)
Lemma list_product_length: forall (U : list F3) (V : list F2),
	length (cart_prod U V) = (length U) * (length V).
Proof.
	intros. unfold cart_vec.
	induction U; simpl; auto.
	rewrite app_lst_length. rewrite IHU. 
	rewrite map_lst_length. auto.
Qed.

(* Length of a product is product of lengths, for vectors *)
Theorem product_length : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	length (cart_vec U V) = m * n.
Proof.
	intros. unfold cart_vec. rewrite list_product_length.
	rewrite vec_length. rewrite vec_length. auto.
Qed.

(* ============================================================================== *)

(*	Main theorem	*)

(* ============================================================================== *)

(* Proof that this set is linearly independent *)
(* 
	Informally:
	Assume that such a set is dependent, so a nontrivial combination c_k * u_i * v_j 
	exists. Then we have that either v_j's are dependent (a contradiction, 
	since we assume it's a basis for V3/V2), or each combination of c_k * u_i 
	is zero. But u_j's are also independent. Hence this set is independent.

	Informal coq version:
	1.) V3/V2 independent means that for any combination b_1u_1 + b_2u_2 + ...
		we have that the b_i's are all zero
	2.) V2/V1 independent means that for any b_i (which lies in V2), it must
		be the case that for b_i = c_1v_1 + c_2v_2 + ... we have that
		all c_i's are zero
	3.) Therefore since we construct c_1 * u_1 * v_1 ... we see all c_i's
		are zero so dependent
*)
Theorem product_independent : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	lin_indep_32 U -> lin_indep_21 V -> lin_indep_31 (of_list (cart_vec U V)).
Proof.
	unfold lin_indep_32; unfold lin_indep_21; intros. unfold lin_indep_31. intros.
	Admitted.

(*
	To prove that this set spans:
	Informally:
	Let v be a vector in V3. Then it can be written with V to be a combination 
	of vectors b_j*u_j, where b_j is in F2. Then b_j can be written as a combination 
	of vectors c_iu_i, where c_i is in F1. Each product u_i*v_j is in F3 and each
	coefficient c_i is in F1, so we can describe any vector as a linear combination 
	of vector products u_i*v_j, so this set indeed spans.

	Informal coq version:
	1. By H5, there are some coeffs in F2 to lin com. v out of vectors u
	2. By H6, each coeff can be made of lin com. v's w/ coeffs in F1
	3. Each element is then a product c_ij * (u_i * v_j), so generates.
*)

(* Helper that a length 0 vector is empty *)
Lemma empty_vector {F : Type} : forall (x : t F 0), x = [].
Proof.
	apply case0; auto.
Qed.

(* TODO: Delete these empty helpers if they prove unnecessary *)
(* Helpers that linear combinations of [] and [] are 0 for that extension *)
Lemma comb_0_3 : linear_com_32 [] [] = 0_3.
Proof. trivial. Qed.

Lemma comb_0_2 : linear_com_21 [] [] = 0_2.
Proof. trivial. Qed.

(* 
	Helper theorems that any vector in F3 is a linear_com_32 on top of a bunch of 
	linear_com_21's
*)
Local Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity).

Theorem expand_vector_2 : forall (m n : nat) (V : t F2 n) (vs : t F2 m),
	generates_21 V -> exists (cs : t (t F1 n) m), 
	vs = (Vector.map (fun com => linear_com_21 com V) cs).
Proof.
	intros. unfold generates_21 in H5. unfold in_span_21 in H5.
	induction vs.
	- exists []. auto.
	(* Second case : need to just add on the coeffs to the new vector *)
	- 	specialize (H5 h). inversion IHvs; inversion H5. 
		exists (x0 :: x). simpl. rewrite H7. rewrite H6. auto.
Qed.

Theorem expand_vector_3 : forall (m n : nat) (U : t F3 m) (V : t F2 n) (v : F3),
	generates_32 U -> generates_21 V ->
	exists (coeffs : t (t F1 n) m), v = linear_com_32 (Vector.map (fun com => linear_com_21 com V) coeffs) U.
Proof.
	unfold generates_32; unfold in_span_32. intros.
	specialize (H5 v). inversion H5. rewrite H7.
	specialize (expand_vector_2 m n V x); intros. apply H8 in H6. inversion H6.
	subst. exists x0. auto.
Qed.

(* Therefore any linear_com_31 can be expressed in the same way *)
Theorem expand_linear_com : forall (m n : nat) (U : t F3 m) (V : t F2 n) (v : F3),
	generates_32 U -> generates_21 V ->
	exists (coeffs: t F1 (length (cart_vec U V))), v = linear_com_31 coeffs (of_list (cart_vec U V)).
Proof.
	intros.
	specialize (expand_vector_3 m n U V v); intros. apply H7 in H5; auto.
	inversion H5. rewrite H8. 
	(* What to do now? *)
	Admitted.

(* Main proof that this set spans *)
Theorem product_spans : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	generates_32 U -> generates_21 V -> generates_31 (of_list (cart_vec U V)).
Proof.
	intros. unfold generates_31; unfold in_span_31.
	intros. specialize (expand_linear_com m n U V v). intros.
	apply H7 in H5; auto.
Qed.

(* Proof that this set forms a basis *)
Theorem product_is_basis : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	basis_32 U -> basis_21 V -> basis_31 (of_list (cart_vec U V)).
Proof.
	intros. inversion H5; inversion H6.
	unfold basis_31.
	assert (IndependentLemma: lin_indep_31 (of_list (cart_vec U V))).
	{ apply product_independent; assumption. }
	assert (SpansLemma: generates_31 (of_list (cart_vec U V))).
	{ apply product_spans; assumption. }
	split; assumption.
Qed.

(* Proof of the Tower Theorem for field extensions *)
Theorem tower_theorem : forall (m n : nat),
	cardinality_32 m -> cardinality_21 n -> cardinality_31 (m * n).
Proof.
	intros. inversion H5; inversion H6.
	assert (B31: basis_31 (of_list (cart_vec x x0))).
	{ specialize (product_is_basis m n x x0 H7 H8). auto. }
	simpl in B31.
	unfold cardinality_31.
	assert (LengthLemma: length (cart_vec x x0) = m * n).
	{ apply product_length. }
	rewrite <- LengthLemma.
	exists (of_list (cart_vec x x0)). assumption.
Qed.