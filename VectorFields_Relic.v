Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Ring.
Import Ring_polynom Ring_tac Ring_theory InitialRing Setoid List Morphisms.
Require Field.
Import Field_theory.
Require Import Setoid Morphisms BinPos BinNat.
Set Default Goal Selector "!".

Section VectorSpaces.

(*
	This file represents the basics of vector spaces, and encompasses Linear
	Algebra Done Wrong (LADW) Section 1.
	In this file we'll define vector spaces much in the same way
	that Coq defines groups/rings/fields.
	The Coq standard library uses the 'record' type. This can be thought 
	of as the same as a record in most programming languages, and in fact 
	is often used to describe these types of common mathematical structures,
	which is why 'Record' is synonymous with 'Structure'.

	These records are the same as inductively defined propositions,
	so a 'field_theory' record is a proposition that a given type satisfies
	the field axioms.

	Let's look at what the Coq standard library uses to define rings:

	Section DEFINITIONS.
		Variable R : Type.
		Variable (rO rI : R) (radd rmul rsub: R->R->R) (ropp : R -> R).
		Variable req : R -> R -> Prop.
		Notation "0" := rO. Notation "1" := rI.
		Infix "==" := req. Infix "+" := radd. Infix "*" := rmul.
		Infix "-" := rsub. Notation "- x" := (ropp x)

	...

	Record ring_theory : Prop := mk_rt {
		Radd_0_l : forall x, 0 + x == x;
		Radd_comm : forall x y, x + y == y + x;
		Radd_assoc : forall x y z, x + (y + z) == (x + y) + z;

		...
	}

	It looks like we'll need to define all of our operations/equalities
	first, then define vector_space as a Prop record containing axioms
	which vector spaces must satisfy.

	First, let's define Rings and Fields in order to
	use them later. Here, we'll use Structures to denote rings/fields as types,
	and use Records later to denote specifically inductive propositions (theories).
	The definition of rings/fields here mirrors the definition of groups in CoqArt,
	with the addition of the 'theory' inductive propositions.

	(Later note)
	Actually, we'll use 'Class' instead of 'Structure'. My understanding is that
	these both define types, but Class allows for more type inference. This is
	going to be necessary to extend Rings to Fields, and more later.
*)

Variable (R : Type).

Class Ring R : Type :=
{
	r_add_id : R;
	r_mult_id : R;
	r_add : R -> R -> R;
	r_min : R -> R -> R;
	r_mult : R -> R -> R;
	r_inv : R -> R;
	R_ring : ring_theory r_add_id r_mult_id r_add r_mult r_min r_inv eq
}.

(*
	The backtick character ` below is needed for 'implicit generalization'.
	Basically, without mentioning that fields extend rings, (that field are
	also of type Ring), we can't properly define the F_field part of the class
	as we need to use its ring identities, ring inverses, etc
*)

Context `{Ring R}.
Class Field R `{Ring R} : Type :=
{
	f_div : R -> R -> R;
	f_inv : R -> R;
	F_field : field_theory r_add_id r_mult_id r_add r_mult r_min r_inv f_div f_inv eq
}.

(* 
	We'll need to declare scopes and operations before we get into vector
	space definitions. We need to declare a scope (why?) ...
*)

Declare Scope field_scope.
Delimit Scope field_scope with fieldsc.
Open Scope field_scope.
Bind Scope field_scope with Field.
Infix "+s" := r_add (at level 50) : field_scope.
Infix "*" := r_mult 	: field_scope.
Notation "-s" := r_inv	: field_scope.
Notation "/s" := f_inv : field_scope.
Infix "/" := f_div		: field_scope.

(*
	Now let's match the pattern used in the standard library's definition
	of rings to define notations for vector spaces:
	(Why is context needed?)
*)
Section DEFINITIONS.
Variable (Sclrs V : Type).
Context `{Field Sclrs}.
Variable (scl_0 scl_1 : Sclrs).
Notation "0" := scl_0.
Notation "1" := scl_1.
Variable (vec_0 : V).
Variable (v_add : V -> V -> V) (s_v_mult : Sclrs -> V -> V).
Variable vec_eq : (V -> V -> Prop).
Infix "==v" := vec_eq (at level 90).
Infix "+v" := v_add (at level 50).
Infix "*v" := s_v_mult (at level 60).
Notation "0v" := vec_0.

(*
	Now we can finally define the inductive proposition for vector fields.
	This will contain the axioms which all vector fields must satisfy
	(hence why it is a proposition: it proposes that 'proper' vector fields 
	satisfy these axioms)

	A vector space is an additive abelian group (vectors) and a field 
	(scalars) so we need the following axioms: (from WolframAlpha)

	Let a, b be scalars and let X, Y, Z be vectors.
	Let +_s be scalar addition and let + be vector addition.
	Let * be scalar multiplication.
	Let 0_s and 1_s be scalar identities, and let 0 be the vector identity.
	1. Commutativity:
		X + Y = Y + X. 	
	2. Associativity of vector addition:
		(X + Y) + Z = X + (Y + Z). 	
	3. Additive identity: 
		For all X,
		0 + X = X + 0 = X. 	
	4. Existence of additive inverse: 
		For any X, there exists a -X such that
		X + (-X) = 0. 	
	5. Associativity of scalar multiplication:
		a*(b*X)=(a*b)*X. 	
	6. Distributivity of scalar sums:
		(a + b)*X = a*X + b*X. 	
	7. Distributivity of vector sums:
		a*(X + Y) = a*X + a*Y. 	
	8. Scalar multiplication identity:
		1*X=X. 

	All we need to do is describe these in our inductive proposition as we see
	in the standard library's ring_theory.
	However, unlike the standard library, we'll want to supply our theory
	with implicit arguments.
*)

Record vector_space_theory 
	(v_add : V -> V -> V) (s_v_mult : Sclrs -> V -> V) 
	(vec_0 : V) (vec_eq : V -> V -> Prop)
	: Prop := mk_vector_space
  {
	v_comm	: forall (x y : V), x +v y ==v y +v x;
	v_assoc	: forall (x y z : V), x +v (y +v z) ==v (x +v y) +v z;
	v_id	: forall (x : V), x +v 0v ==v x;
	v_inv	: forall (x : V), exists (y : V), x +v y ==v 0v;
	s_assoc : forall (x : V) (a b : Sclrs), a *v (b *v x) ==v (a * b) *v x;
	s_dist	: forall (x : V) (a b : Sclrs), (a +s b) *v x ==v (a *v x) +v (b *v x);
	v_dist	: forall (x y : V) (a : Sclrs), a *v (x +v y) ==v (a *v x) +v (a *v y);
	s_id	: forall (x : V), scl_1 *v x ==v x;
  }.

(*
	Now let's define a Class (structure) so we can actually use the vector
	space type, as we did above with Rings and Fields. Vector spaces have the
	two operations of scalar multiplication and vector addition, and have an
	additive identity, so we only need these along with our theory described
	above.

	We'll add a prime character to each field as otherwise we'll run into
	some naming headaches from our definitions above
*)

Class Vector_Space : Type :=
{
	v_add' : V -> V -> V;
	s_v_mult' : Sclrs -> V -> V;
	e : V; (* Call the identity e for cleaner code later *)
	V_vector_space : vector_space_theory v_add' s_v_mult' e vec_eq;
}.

(*
	We'll also try to define here that equality is extensional. I'm not
	exactly sure why this is necessary, but it appears in the standard
	library's ring_theory section, so we'll replicate it here.
*)

Record vector_space_eq_ext : Prop := mk_vseqe 
{
	v_add_ext : Proper (vec_eq ==> vec_eq ==> vec_eq) v_add;
	s_v_mult_ext : Proper (eq ==> vec_eq ==> vec_eq) s_v_mult;
}.

(*
	To match ring_theory in the standard library we also need a section
	on morphisms. 
*)

Section MORPHISMS.

Variable (CS CV : Type).
Variable (Cvec_0 : CV).
Variable (Cv_add : CV -> CV -> CV) (Cs_v_mult : CS -> CV -> CV).
Variable (Cvec_eqb : CV -> CV -> bool).
Variable (Sphi : CS -> Sclrs) (Vphi : CV -> V).
Infix "?=!" := Cvec_eqb (at level 90).
Infix "+!" := Cv_add (at level 50).
Infix "*!" := Cs_v_mult (at level 60).
Notation "[ x ]Sc" := (Sphi x).
Notation "[ x ]V" := (Vphi x).

Record vector_space_morph : Prop := mkvec_morph {
	morph_id 		: [ Cvec_0 ]V ==v 0v;
	morph_v_add		: forall x y, [ x +! y ]V ==v [ x ]V +v [ y ]V;
	morph_s_v_mult 	: forall x y, [x *! y]V ==v [ x ]Sc *v [ y ]V;
	morph_eq 		: forall x y, (x ?=! y) = true -> [ x ]V ==v [ y ]V;
}.

End MORPHISMS.

Variable vec_eqb : V -> V -> bool.
Variable Vsth : Equivalence vec_eq.
Hypothesis morph_vec_eq : forall x y, (vec_eqb x y) = true -> x ==v y.
Definition VIDphi (x : V) := x.
Definition SIDphi (y : Sclrs) := y.
Check vector_space_morph.
Lemma IDmorph : vector_space_morph Sclrs V 0v v_add s_v_mult vec_eqb SIDphi VIDphi.
Proof.
	split; try (intros; compute; reflexivity).
	intros. compute. apply morph_vec_eq in H2. assumption.
Qed.

End DEFINITIONS.

(*
	Next, in order to work with setoids (my understanding is that this
	should allow us to use the rewrite tactic), we need to include the
	'Leibniz Equality', as ring_theory does in the standard library, as
	well as describe morphisms as axioms.
*)

Declare Scope vector_space_scope.
Delimit Scope vector_space_scope with vspc_sc.
Open Scope vector_space_scope.
Bind Scope vector_space_scope with Vector_Space.
Context `{Vector_Space}.

Variable (scl_0 : Sclrs).
Notation "0" := scl_0.
Notation "1" := scl_1.
Infix "==v" := vec_eq (at level 90) : vector_space_scope.
Infix "+v" := v_add (at level 60) : vector_space_scope.
Infix "*v" := s_v_mult (at level 50) : vector_space_scope.
Notation "-v" := v_inv : vector_space_scope.
Notation "-s" := r_inv	: vector_space_scope.
Notation "0v" := vec_0.

Variable r_th : ring_theory 0 1 r_add r_min r_mult r_inv eq.

Lemma Eq_vector_space : Equivalence (@eq V).
Proof.
	split; auto.
	unfold Transitive. intros.
	rewrite H2. assumption.
Qed.

Lemma Eq_vs_ext : vector_space_eq_ext Sclrs V v_add s_v_mult (@eq V).
Proof.
	split; compute; intros;
	rewrite H2, H3; reflexivity.
Qed.

Variable Vsth : Equivalence vec_eq.

Variable Veqe : vector_space_eq_ext Sclrs V v_add s_v_mult vec_eq.

(*
	Now we can get started with some basic theorems in linear algebra. Note that
	we have no concept of vector _elements_, so things like bases and span
	will need some more tools before we can work with them.

	We'll start with just checking our notation and seeing that every axiom
	of a vector space is properly satisfied.
*)

Theorem v_comm_thm : forall (a b : V), a +v b ==v b +v a.
Proof.
	destruct H1. 
	inversion V_vector_space0. assumption.
Qed.

Theorem v_assoc_thm : forall (a b c : V), a +v (b +v c) ==v (a +v b) +v c.
Proof.
	destruct H1.
	inversion V_vector_space0. assumption.
Qed.

(*
	It's starting to look like we should just define a tactic:
*)

Ltac by_axiom H :=
	destruct H; inversion V_vector_space0; assumption.

Theorem v_id_thm : forall (a : V), a +v 0v ==v a.
Proof. by_axiom H1. Qed.

Theorem v_inv_thm : forall (a : V), exists (b : V), a +v b ==v 0v.
Proof. by_axiom H1. Qed.

Theorem s_assoc_thm : forall (a : V) (m n : Sclrs), m *v (n *v a) ==v (m * n) *v a.
Proof. by_axiom H1. Qed.

Theorem s_dist_thm : forall (a : V) (m n : Sclrs), (m +s n) *v a ==v (m *v a) +v (n *v a).
Proof. by_axiom H1. Qed.

Theorem v_dist_thm : forall (a b : V) (m : Sclrs), m *v (a +v b) ==v (m *v a) +v (m *v b).
Proof. by_axiom H1. Qed.

Theorem s_id_thm : forall (a : V), 1 *v a ==v a.
Proof. by_axiom H1. Qed.

(*	
	Now let's try to prove some more interesting theorems, but first let's
	add morphisms and a parametric relation to allow for more tactic usage.

	We'll be using exercises in Linear Algebra Done Wrong (LADW).
	
*)
Theorem v_refl_thm : forall (a : V), (a ==v a).
Proof. intros; reflexivity. Qed.
Theorem v_symm_thm : forall (a b : V), (a ==v b) -> (b ==v a).
Proof. intros; rewrite H2; reflexivity. Qed.
Theorem v_trans_thm : forall (a b c : V), (a ==v b) -> (b ==v c) -> (a ==v c).
Proof. intros; rewrite H2, H3; reflexivity. Qed.

Add Parametric Relation : V vec_eq
	reflexivity proved by v_refl_thm
	symmetry proved by v_symm_thm
	transitivity proved by v_trans_thm as v_equiv.

Add Morphism v_add with signature (vec_eq ==> vec_eq ==> vec_eq) as v_add''.
Proof. 
	intros. destruct Veqe. compute in v_add_ext0. auto.
Qed.

Add Morphism s_v_mult with signature (eq ==> vec_eq ==> vec_eq) as s_v_mult''.
Proof.
	intros. destruct Veqe. compute in s_v_mult_ext0. auto.
Qed.

(*	(LADW 1.4) Uniqueness of the additive vector identity *)
Theorem id_unique : forall (a b c : V), a +v b ==v a -> b ==v 0v.
Proof. 
	intros. destruct H1; inversion V_vector_space0.
	specialize (v_inv0 a); inversion v_inv0.
	rewrite <- H3. rewrite <- H2. rewrite <- v_comm0. rewrite v_assoc0.
	rewrite v_comm0 with (y := a). rewrite H3. 
	symmetry. rewrite v_comm0. apply v_id0.
Qed.	


(* Useful helper lemma for injectivity *)
Theorem additive_injectivity : forall (a b c : V), a +v b ==v a +v c -> b ==v c.
Proof.
	destruct r_th.
	destruct H1; inversion V_vector_space0.
	intros.
	(*
	Informally: b = b + 0 = b + c - c = a + c - c = a
	*)
	rewrite <- (v_id0 b) at 1. specialize (v_inv0 a); inversion v_inv0.
	rewrite <- H3. rewrite v_assoc0.
	assert (a +v b ==v b +v a) as E1.
	{ apply v_comm0. } 
	rewrite <- E1. rewrite H2. 
	assert (a +v c ==v c +v a) as E2.
	{ apply v_comm0. } 
	rewrite E2. rewrite <- v_assoc0. rewrite H3. rewrite v_id0.
	reflexivity.
Qed.

(* (LADW 1.6) Additive inverse is unique *)
Theorem inv_unique : forall (a b c : V), a +v b ==v 0v -> a +v c ==v 0v -> b ==v c.
Proof.
	intros. rewrite <- H3 in H2.
	apply additive_injectivity in H2.
	assumption.
Qed.

(* (LADW 1.7) Zero scalar times vector is zero vector *)
Theorem zero_sc_is_zero_vec : forall (a : V), 0 *v a ==v 0v.
Proof.
	(*
	Informally: 
		0*a = (0 + 0)*a = 0*a + 0*a -> 
		0*a - 0*a = 0*a + 0*a - 0*a ->
		0v = 0*a
	*)
	destruct r_th.
	destruct H1; inversion V_vector_space0.
	intros.
	assert (0 *v a ==v 0 *v a) as E1.
	{ reflexivity. }
	rewrite <- (Radd_0_l 0) in E1 at 1.
	rewrite s_dist0 in E1.
	rewrite <- (v_id0 (0 *v a)) in E1 at 3.
	apply additive_injectivity in E1.
	assumption.
Qed.

(* (LADW 1.8) Scalar inverse is vector inverse *)
Theorem sc_inv_is_vec_inv : forall (a b : V), a +v b ==v 0v -> (-s 1) *v a ==v b.
Proof.
	(*
	Informally: a + b = 0v = 0*a = (1 - 1)a = a - a -> b = -a
	*)
	destruct r_th.
	destruct H1; inversion V_vector_space0.
	intros.
	rewrite <- (zero_sc_is_zero_vec a) in H2.
	rewrite <- s_id0 in H2.
	specialize (Ropp_def 1). rewrite <- Ropp_def in H2. rewrite s_dist0 in H2.
	rewrite v_dist0 in H2. rewrite s_id0 in H2 at 1. symmetry in H2.
	rewrite <- (s_id0 a) in H2 at 3. 
	rewrite s_id0 in H2; rewrite s_id0 in H2.
	apply additive_injectivity in H2.
	assumption.
Qed.

(*
	NOTE FOR LATER:
	Let V be a type for some kind of list with defined operations.
	This should allow us to look inside of vectors and start defining basis,
	span, linear independence, linear combination, etc
	Simply plug in to vector_space_theory.
*)