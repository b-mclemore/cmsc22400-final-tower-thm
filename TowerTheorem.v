Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export VectorFields.
Set Default Goal Selector "!".
Require Field.
Import Field_theory.
Require Import List.
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

(*	Typecasting	*)

(* ============================================================================== *)

Definition vec_cast {X : Type} {m n : nat} (H : m = n) v :=
	eq_rect _ (fun k => t X k) v _ H.

Lemma cast_vecs {m n : nat} : forall (F : Type),
	  forall (l1 : t F n) (l2 : t F m),
		forall (H : m = n),
		  l1 = vec_cast H l2.
Proof. Admitted.
	
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
Local Infix "++" := Vector.append.
Local Notation "h :: t" := (Vector.cons _ h _ t) (at level 60, right associativity).

Definition cart_prod : forall {m n : nat} (U : t F3 m) (V : t F2 n), t F3 (m * n) :=
	fix cart_prod_fix {m} {n} (U : t F3 m) (V : t F2 n) : t F3 (m * n) := 
		match U with
		| [] => []
		| hd :: lst => (map (fun v => mult_32 v hd) V) ++ cart_prod_fix lst V
		end.

(* Cons-ing before turning vec into list is the same as cons-ing after *)
Lemma preserve_cons : forall (n : nat) (F : Type) (h : F) (U : t F n),
	(to_list (h :: U)) = List.app (List.cons h List.nil) (to_list U).
Proof.
	trivial. (* <--- I wish this worked more often! *)
Qed.

(* Flatten a vector *)
Definition flatten_vec : forall {m n : nat} {F : Type} (x : t (t F n) m), t F (m * n) :=
	fix flatten_vec_fix {m} {n} {F} (x : t (t F n) m) : t F (m * n) := 
		match x with
		| [] => []
		| hd :: lst => hd ++ flatten_vec_fix lst
		end.

(* The vector length is the same as the list length *)
Lemma vec_length { F : Type}: forall (n : nat) (U : t F n),
	length (to_list U) = n.
Proof.
	intros. induction U. 
	- simpl; auto.
	- auto. rewrite preserve_cons. simpl. auto.
Qed.

(* Length of a product is product of lengths, for vectors *)
Theorem product_length : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	length (to_list (cart_prod U V)) = m * n.
Proof.
	intros. remember (cart_prod U V). auto. rewrite vec_length. auto.
Qed.

(* Helper that a length 0 vector is empty *)
Lemma empty_vector {F : Type} : forall (x : t F 0), x = [].
Proof.
	apply case0; auto.
Qed.

(* ============================================================================== *)

(*	Useful vector theory lemmas (borrowed from VectorFields.v)	*)

(* ============================================================================== *)

Theorem additive_injectivity_3 : forall (a b c : F3), a +_3 b = a +_3 c -> b = c.
Proof.
	destruct F3_th; destruct F_R.
	destruct E32_th.
	intros.
	rewrite <- (v_id0 b) at 1. specialize (v_inv0 a); inversion v_inv0.
	rewrite <- H6. rewrite v_assoc0.
	assert (a +_3 b = b +_3 a) as E1.
	{ apply v_comm0. } 
	rewrite <- E1. rewrite H5. 
	assert (a +_3 c = c +_3 a) as E2.
	{ apply v_comm0. } 
	rewrite E2. rewrite <- v_assoc0. rewrite H6. rewrite v_id0.
	reflexivity.
Qed.

Theorem zero_to_zero_32 : forall (a : F3), 0_2 *_32 a = 0_3.
Proof.
	destruct F2_th; destruct F_R.
	destruct E32_th.
	intros.
	assert (0_2 *_32 a = 0_2 *_32 a) as E1.
	{ reflexivity. }
	rewrite <- (Radd_0_l 0_2) in E1 at 1.
	rewrite s_dist0 in E1.
	rewrite <- (v_id0 (0_2 *_32 a)) in E1 at 3.
	apply additive_injectivity_3 in E1.
	assumption.
Qed.

Theorem zero_to_zero_31 : forall (a : F3), 0_1 *_31 a = 0_3.
Proof.
	destruct F1_th; destruct F_R.
	destruct E31_th.
	intros.
	assert (0_1 *_31 a = 0_1 *_31 a) as E1.
	{ reflexivity. }
	rewrite <- (Radd_0_l 0_1) in E1 at 1.
	rewrite s_dist0 in E1.
	rewrite <- (v_id0 (0_1 *_31 a)) in E1 at 3.
	apply additive_injectivity_3 in E1.
	assumption.
Qed.

Theorem additive_injectivity_2 : forall (a b c : F2), a +_2 b = a +_2 c -> b = c.
Proof.
	destruct F2_th; destruct F_R.
	destruct E21_th.
	intros.
	rewrite <- (v_id0 b) at 1. specialize (v_inv0 a); inversion v_inv0.
	rewrite <- H6. rewrite v_assoc0.
	assert (a +_2 b = b +_2 a) as E1.
	{ apply v_comm0. } 
	rewrite <- E1. rewrite H5. 
	assert (a +_2 c = c +_2 a) as E2.
	{ apply v_comm0. } 
	rewrite E2. rewrite <- v_assoc0. rewrite H6. rewrite v_id0.
	reflexivity.
Qed.

Theorem zero_to_zero_21 : forall (a : F2), 0_1 *_21 a = 0_2.
Proof.
	destruct F1_th; destruct F_R.
	destruct E21_th.
	intros.
	assert (0_1 *_21 a = 0_1 *_21 a) as E1.
	{ reflexivity. }
	rewrite <- (Radd_0_l 0_1) in E1 at 1.
	rewrite s_dist0 in E1.
	rewrite <- (v_id0 (0_1 *_21 a)) in E1 at 3.
	apply additive_injectivity_2 in E1.
	assumption.
Qed.


(* ============================================================================== *)

(*	Main theorem	*)

(* ============================================================================== *)
(* 
	The main theorem is not complete. When I've needed to skip something in the
	middle of a proof, I use the following tactic (which is mostly for proving
	assertions about manipulating lists)
*)

Axiom skip : forall (p : Prop), True -> p.
Ltac ADMITTED := apply skip; auto.

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

(* Helpers that taking away a vector doesn't affect independence *)
Lemma remove_vec_32 : forall (m : nat) (U : t F3 m) (h : F3),
	lin_indep_32 (h :: U) -> lin_indep_32 U.
Proof. 
	unfold lin_indep_32; intros. rename coeffs into cs. 
	specialize (H5 ((0_2 :: []) ++ cs)).
	simpl in H5.
	specialize (zero_to_zero_32 h); intros. rewrite H7 in H5.
	destruct F3_th; destruct F_R. rewrite Radd_0_l in H5.
	assert (fold_left add_3 0_3 (map2 mult_32 cs U) = linear_com_32 cs U).
	{ ADMITTED. }
	rewrite <- H8 in H6.
	apply H5 in H6.
	assert (Forall (fun y : F2 => y = 0_2) (0_2 :: cs) -> 
		Forall (fun y : F2 => y = 0_2) cs).
	{ ADMITTED. }
	apply H9 in H6.
	auto.
Qed.

Lemma remove_vec_21 : forall (m : nat) (V : t F2 m) (h : F2),
	lin_indep_21 (h :: V) -> lin_indep_21 V.
Proof. (* This should follow the same format as the above *)
	unfold lin_indep_21; intros. rename coeffs into cs. 
	specialize (H5 ((0_1 :: []) ++ cs)).
	simpl in H5.
	specialize (zero_to_zero_21 h); intros. rewrite H7 in H5.
	destruct F2_th; destruct F_R. rewrite Radd_0_l in H5.
	assert (fold_left add_2 0_2 (map2 mult_21 cs V) = linear_com_21 cs V).
	{ ADMITTED. }
	rewrite <- H8 in H6.
	apply H5 in H6.
	assert (Forall (fun y : F1 => y = 0_1) (0_1 :: cs) -> 
		Forall (fun y : F1 => y = 0_1) cs).
	{ ADMITTED. }
	apply H9 in H6.
	auto.
Qed.

Theorem product_independent : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	lin_indep_32 U -> lin_indep_21 V -> lin_indep_31 (cart_prod U V).
Proof.
	intros. unfold lin_indep_31. intros.
	induction U.
	- 	specialize (empty_vector coeffs); intros.
		rewrite H8. econstructor.
	-	induction V.
		+ 	unfold lin_indep_21 in H6. 
			(* Would like to say 'specialize (H6 coeffs)' but this fails typechecking *)
			ADMITTED.
		+ 	specialize (remove_vec_32 n0 U h); intros.
			specialize (remove_vec_21 n V h0); intros.
			apply H8 in H5; apply H9 in H6.
			Admitted.
			(* Why does 'apply H5 in IHU' not work? *)

(*
	To prove that this set spans:
	Informally:
	Let v be a vector in V3. Then it can be written with V to be a combination 
	of vectors b_j*u_j, where b_j is in F2. Then b_j can be written as a combination 
	of vectors c_iu_i, where c_i is in F1. Each product u_i*v_j is in F3 and each
	coefficient c_i is in F1, so we can describe any vector as a linear combination 
	of vector products u_i*v_j, so this set indeed spans.

*)
(* Helpers that linear combinations of [] and [] are 0 for that extension *)
Lemma comb_0_3 : linear_com_32 [] [] = 0_3.
Proof. trivial. Qed.

Lemma comb_0_2 : linear_com_21 [] [] = 0_2.
Proof. trivial. Qed.

(* 
	Helper theorems that any vector in F3 is a linear_com_32 on top of a bunch of 
	linear_com_21's
*)
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

(* Lemmas that mapping to 0 and taking a combination results in 0 vector *)
Lemma map_to_0_2 {F : Type }: forall (n : nat) (U : t F3 n) (x0 : t F n),
	linear_com_32 (map (fun _ : _ => 0_2) x0) U = 0_3.
Proof.
	intros.
	induction U.
	- 	specialize (empty_vector x0); intros; subst. simpl. auto.
	-	specialize (IHU (tl x0)). destruct E32_th. 
		assert (linear_com_32 (map (fun _ : F => 0_2) x0) (h :: U) =
			(0_2 *_32 h) +_3 linear_com_32 (map (fun _ : F => 0_2) (tl x0)) U).
			{ ADMITTED. }
			rewrite H5. specialize (zero_to_zero_32 h); intros.
			rewrite H6. rewrite v_comm0. rewrite v_id0. apply IHU.
Qed.

Lemma map_to_0_1 {F : Type} : forall (n : nat) (U : t F3 n) (x0 : t F n),
	linear_com_31 (map (fun _ : _ => 0_1) x0) U = 0_3.
Proof.
	intros.
	induction U.
	- 	specialize (empty_vector x0); intros; subst. simpl. auto.
	-	specialize (IHU (tl x0)). destruct E31_th. 
		assert (linear_com_31 (map (fun _ : F => 0_1) x0) (h :: U) =
			(0_1 *_31 h) +_3 linear_com_31 (map (fun _ : F => 0_1) (tl x0)) U).
			{  ADMITTED. }
			rewrite H5. specialize (zero_to_zero_31 h); intros.
			rewrite H6. rewrite v_comm0. rewrite v_id0. apply IHU.
Qed.

(* Taking linear combinations can be one or two step *)
Theorem telescope_linear_coms {m n : nat} : forall (U : t F3 m) (V : t F2 n) (coeffs : t (t F1 n) m),
	linear_com_32 (map (fun com : t F1 n => linear_com_21 com V) coeffs) U =
	linear_com_31 (flatten_vec coeffs) (cart_prod U V).
Proof.
	intros. induction coeffs.
	- specialize (empty_vector U); intros; subst. auto.
	- 	specialize (IHcoeffs (tl U)).
		assert (flatten_vec (h :: coeffs) = (h ++ flatten_vec coeffs)).
		{ auto. }
		rewrite H5.
		assert (linear_com_31 (h ++ (flatten_vec coeffs)) (cart_prod U V) =
		(linear_com_31 h ((map (fun v => mult_32 v (hd U)) V))) +_3
		(linear_com_31 (flatten_vec coeffs) (cart_prod (tl U) V))).
		{ ADMITTED. }
		simpl. rewrite H6. unfold linear_com_32 in IHcoeffs.
		Admitted.

Theorem expand_linear_com : forall (m n : nat) (U : t F3 m) (V : t F2 n) (v : F3),
	generates_32 U -> generates_21 V ->
	exists (coeffs: t F1 (m * n)), v = linear_com_31 coeffs (cart_prod U V).
Proof.
	intros.
	specialize (expand_vector_3 m n U V v); intros. apply H7 in H5; auto.
	inversion H5.
	exists (flatten_vec x). rewrite H8.
	apply telescope_linear_coms.
Qed.
 
(* Main proof that this set spans *)
Theorem product_spans : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	generates_32 U -> generates_21 V -> generates_31 (cart_prod U V).
Proof.
	intros. unfold generates_31; unfold in_span_31.
	intros. specialize (expand_linear_com m n U V v). intros.
	apply H7 in H5; auto.
Qed.

(* Proof that this set forms a basis *)
Theorem product_is_basis : forall (m n : nat) (U : t F3 m) (V : t F2 n),
	basis_32 U -> basis_21 V -> basis_31 (cart_prod U V).
Proof.
	intros. inversion H5; inversion H6.
	unfold basis_31.
	assert (IndependentLemma: lin_indep_31 (cart_prod U V)).
	{ apply product_independent; assumption. }
	assert (SpansLemma: generates_31 (cart_prod U V)).
	{ apply product_spans; assumption. }
	split; assumption.
Qed.

(* Proof of the Tower Theorem for field extensions *)
Theorem tower_theorem : forall (m n : nat),
	cardinality_32 m -> cardinality_21 n -> cardinality_31 (m * n).
Proof.
	intros. inversion H5; inversion H6.
	assert (B31: basis_31 (cart_prod x x0)).
	{ specialize (product_is_basis m n x x0 H7 H8). auto. }
	unfold cardinality_31.
	exists (cart_prod x x0).
	assumption.
Qed.



(*
	After running into issues with vectors, I tried to use lists instead to prove
	the result. The work below replicates all the functions and most lemmas above,
	but uses lists instead of vectors. The hope was that this would make induction
	much easier, but I didn't finish.
*)



Fixpoint lcom_21_lists (s : list F1) (v : list F2) : F2 :=
  match s, v with
  | List.nil, _ => 0_2
  | _, List.nil => 0_2
  | List.cons shd stl, List.cons vhd vtl => 
  	(mult_21 shd vhd) +_2 (lcom_21_lists stl vtl)
  end.

Fixpoint lcom_32_lists (s : list F2) (v : list F3) : F3 :=
  match s, v with
  | List.nil, _ => 0_3
  | _, List.nil => 0_3
  | List.cons shd stl, List.cons vhd vtl => 
  	(mult_32 shd vhd) +_3 (lcom_32_lists stl vtl)
  end.

Fixpoint lcom_31_lists (s : list F1) (v : list F3) : F3 :=
	match s, v with
	| List.nil, _ => 0_3
	| _, List.nil => 0_3
	| List.cons shd stl, List.cons vhd vtl => 
		(mult_31 shd vhd) +_3 (lcom_31_lists stl vtl)
	end.

Definition lindep_21_list (vs : list F2) : Prop :=
	forall (coeffs : list F1),
		(lcom_21_lists coeffs vs) = 0_2 ->
		List.Forall (fun y => y = 0_1) coeffs.
	
Definition lindep_32_list (vs : list F3) : Prop :=
	forall (coeffs : list F2),
		(lcom_32_lists coeffs vs) = 0_3 ->
		List.Forall (fun y => y = 0_2) coeffs.

Definition lindep_31_list (vs : list F3) : Prop :=
	forall (coeffs : list F1),
		(lcom_31_lists coeffs vs) = 0_3 ->
		List.Forall (fun y => y = 0_1) coeffs.

Definition in_span_21_list (vecs : list F2) (v : F2) : Prop :=
	exists coeffs, v = (lcom_21_lists coeffs vecs).

Definition in_span_32_list (vecs : list F3) (v : F3) : Prop :=
	exists coeffs, v = (lcom_32_lists coeffs vecs).

Definition in_span_31_list (vecs : list F3) (v : F3) : Prop :=
	exists coeffs, v = (lcom_31_lists coeffs vecs).

Definition generates_21_list (vs : list F2) : Prop
	:= forall (v : F2), in_span_21_list vs v.

Definition generates_32_list (vs : list F3) : Prop
	:= forall (v : F3), in_span_32_list vs v.

Definition generates_31_list (vs : list F3) : Prop
	:= forall (v : F3), in_span_31_list vs v.

Definition basis_21_list (vs : list F2) : Prop
	:= generates_21_list vs /\ lindep_21_list vs.

Definition basis_32_list (vs : list F3) : Prop
	:= generates_32_list vs /\ lindep_32_list vs.

Definition basis_31_list (vs : list F3) : Prop
	:= generates_31_list vs /\ lindep_31_list vs.

(* The cardinality (degree) of a basis is simply its size *)
Definition cardinality_21_list (m : nat) : Prop
	:= exists (es : list F2), basis_21_list es.

Definition cardinality_32_list (m : nat) : Prop
	:= exists (es : list F3), basis_32_list es.

Definition cardinality_31_list (m : nat) : Prop
	:= exists (es : list F3), basis_31_list es.

Fixpoint cart_prod_l (U : list F3) (V : list F2) : list F3 :=
	match U with
	| List.nil => List.nil
	| List.cons hd lst => List.app (List.map (fun v => mult_32 v hd) V) (cart_prod_l lst V)
	end.

Theorem remove_vec_2 : forall (V : list F2) (v : F2),
	lindep_21_list (v :: V) -> lindep_21_list V.
Proof.
	unfold lindep_21_list; intros.
	Admitted.

Theorem product_independent_l : forall (U : list F3) (V : list F2),
	lindep_32_list U -> lindep_21_list V -> lindep_31_list (cart_prod_l U V).
Proof.
	intros. unfold lindep_31_list. intros.
	induction coeffs.
	- auto.
	- induction V.
		+ auto.
		+ induction U.
			* apply IHV; auto. intros. specialize (remove_vec_2 V a0). auto.
			* intros. Admitted.

(* 
	Helper theorems that any vector in F3 is a linear_com_32 on top of a bunch of 
	linear_com_21's
*)
	
(* Main proof that this set spans *)
Theorem product_spans_l : forall (U : list F3) (V : list F2),
	generates_32_list U -> generates_21_list V -> generates_31_list (cart_prod_l U V).
Proof.
	intros. unfold generates_31_list; unfold in_span_31_list. intros.
	specialize (H5 v). inversion H5.
	induction x.
	- exists List.nil. auto.
	- specialize (H6 a). inversion H6. induction x0.
		+ apply IHx. simpl in H8. rewrite H8 in H7. 
			assert (lcom_32_lists (0_2 :: x) U = lcom_32_lists x U).
			{ ADMITTED. }
			subst; auto.
		+ unfold in_span_21_list in H6. inversion H6. apply IHx0. Admitted.


(* Proof that this set forms a basis *)
Theorem product_is_basis_l : forall (U : list F3) (V : list F2),
	basis_32_list U -> basis_21_list V -> basis_31_list (cart_prod_l U V).
Proof.
	intros. inversion H5; inversion H6.
	unfold basis_31_list.
	assert (IndependentLemma: lindep_31_list (cart_prod_l U V)).
	{ apply product_independent_l; auto. }
	assert (SpansLemma: generates_31_list (cart_prod_l U V)).
	{ apply product_spans_l; auto. }
	split; assumption.
Qed.

(* Proof of the Tower Theorem for field extensions *)
Theorem tower_theorem_list : forall (m n : nat),
	cardinality_32_list m -> cardinality_21_list n -> cardinality_31_list (m * n).
Proof.
	intros. inversion H5; inversion H6.
	assert (B31: basis_31_list (cart_prod_l x x0)).
	{ specialize (product_is_basis_l x x0 H7 H8). auto. }
	unfold cardinality_31.
	exists (cart_prod_l x x0).
	assumption.
Qed.

End TowerTheorem.