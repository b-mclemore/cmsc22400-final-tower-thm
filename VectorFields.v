Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
Require Ring.
Import Ring_polynom Ring_tac Ring_theory InitialRing Setoid List Morphisms.
Require Field.
Import Field_theory.
Require Import Setoid Morphisms RelationClasses.
Set Default Goal Selector "!".

Module Export VectorAxioms.
(*
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

Axiom (R : Type).

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
Global Infix "+s" := r_add (at level 50) : field_scope.
Global Infix "*" := r_mult 	: field_scope.
Global Notation "-s" := r_inv	: field_scope.
Global Notation "/s" := f_inv : field_scope.
Global Infix "/" := f_div		: field_scope.
Global Notation "0" := r_add_id.
Global Notation "1" := r_mult_id.

(*
	Now let's match the pattern used in the standard library's definition
	of rings to define notations for vector spaces:
*)
Axiom (Sclrs V : Type).
Context `{Field Sclrs}.
Axiom (vec_0 : V).
Notation "0v" := vec_0.
Axiom (v_add : V -> V -> V) (s_v_mult : Sclrs -> V -> V).
Infix "+v" := v_add (at level 50).
Infix "*v" := s_v_mult (at level 60).

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
	v_comm	: forall (x y : V), x +v y = y +v x;
	v_assoc	: forall (x y z : V), x +v (y +v z) = (x +v y) +v z;
	v_id	: forall (x : V), x +v 0v = x;
	v_inv	: forall (x : V), exists (y : V), x +v y = 0v;
	s_assoc : forall (x : V) (a b : Sclrs), a *v (b *v x) = (a * b) *v x;
	s_dist	: forall (x : V) (a b : Sclrs), (a +s b) *v x = (a *v x) +v (b *v x);
	v_dist	: forall (x y : V) (a : Sclrs), a *v (x +v y) = (a *v x) +v (a *v y);
	s_id	: forall (x : V), 1 *v x = x;
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
	V_vector_space : vector_space_theory v_add' s_v_mult' e eq;
}.

(*
	We'll also try to define here that equality is extensional. I'm not
	exactly sure why this is necessary, but it appears in the standard
	library's ring_theory section, so we'll replicate it here.
*)

Record vector_space_eq_ext : Prop := mk_vseqe 
{
	v_add_ext : Proper (eq ==> eq ==> eq) v_add;
	s_v_mult_ext : Proper (eq ==> eq ==> eq) s_v_mult;
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
	morph_id 		: [ Cvec_0 ]V = 0v;
	morph_v_add		: forall x y, [ x +! y ]V = [ x ]V +v [ y ]V;
	morph_s_v_mult 	: forall x y, [x *! y]V = [ x ]Sc *v [ y ]V;
	morph_eq 		: forall x y, (x ?=! y) = true -> [ x ]V = [ y ]V;
}.

End MORPHISMS.

Axiom vec_eqb : V -> V -> bool.
Definition Vsth := Equivalence (@eq V).
Axiom morph_vec_eq : forall x y, (vec_eqb x y) = true -> x = y.
Definition VIDphi (x : V) := x.
Definition SIDphi (y : Sclrs) := y.
Check vector_space_morph.
Lemma IDmorph : vector_space_morph Sclrs V 0v v_add s_v_mult vec_eqb SIDphi VIDphi.
Proof.
	split; intros; try (intros; compute; reflexivity).
	intros. compute. apply morph_vec_eq in H1. assumption.
Qed.

End VectorAxioms.

Module Type VectorSpaces.
Include VectorAxioms.

(*
	Next, in order to work with setoids (my understanding is that this
	should allow us to use the rewrite tactic), we need to include the
	'Leibniz Equality', as ring_theory does in the standard library, as
	well as describe morphisms as axioms.
*)

Axiom r_th : ring_theory 0 1 r_add r_min r_mult r_inv eq.
Add Ring SclrsRing : r_th.
Axiom f_th : field_theory 0 1 r_add r_min r_mult r_inv f_div f_inv eq.
Add Field SclrsField : f_th.
Axiom v_th : vector_space_theory v_add s_v_mult 0v eq.

Lemma Eq_vector_space : Equivalence (@eq V).
Proof.
	split; auto.
	unfold Transitive; intros.
	rewrite H1. assumption.
Qed.

Add Morphism v_add with signature (eq ==> eq ==> eq) as v_add_ext'.
Proof. auto. Qed.

Add Morphism s_v_mult with signature (eq ==> eq ==> eq) as s_v_mult_ext'.
Proof. auto. Qed.

(*
	Now we can get started with some basic theorems in linear algebra. Note that
	we have no concept of vector _elements_, so things like bases and span
	will need some more tools before we can work with them.

	We'll start with just checking our notation and seeing that every axiom
	of a vector space is properly satisfied.
*)

Theorem v_comm_thm : forall (a b : V), a +v b = b +v a.
Proof.
	destruct v_th.
	assumption.
Qed.

Theorem v_assoc_thm : forall (a b c : V), a +v (b +v c) = (a +v b) +v c.
Proof.
	destruct v_th. assumption.
Qed.

(*
	It's starting to look like we should just define a tactic:
*)

Ltac by_axiom H :=
	destruct v_th; assumption.

Theorem v_id_thm : forall (a : V), a +v 0v = a.
Proof. by_axiom H1. Qed.

Theorem v_inv_thm : forall (a : V), exists (b : V), a +v b = 0v.
Proof. by_axiom H1. Qed.

Theorem s_assoc_thm : forall (a : V) (m n : Sclrs), m *v (n *v a) = (m * n) *v a.
Proof. by_axiom H1. Qed.

Theorem s_dist_thm : forall (a : V) (m n : Sclrs), (m +s n) *v a = (m *v a) +v (n *v a).
Proof. by_axiom H1. Qed.

Theorem v_dist_thm : forall (a b : V) (m : Sclrs), m *v (a +v b) = (m *v a) +v (m *v b).
Proof. by_axiom H1. Qed.

Theorem s_id_thm : forall (a : V), 1 *v a = a.
Proof. by_axiom H1. Qed.

(*	
	Now let's try to prove some more interesting theorems.
	We'll be using exercises in Linear Algebra Done Wrong (LADW).
	
*)

(*	(LADW 1.4) Uniqueness of the additive vector identity *)
Theorem id_unique : forall (a b c : V), a +v b = a -> b = 0v.
Proof. 
	intros. destruct v_th.
	specialize (v_inv0 a); inversion v_inv0.
	rewrite <- H2. rewrite <- H1. rewrite <- v_comm0. rewrite v_assoc0.
	rewrite v_comm0 with (y := a). rewrite H2. 
	symmetry. rewrite v_comm0. apply v_id0.
Qed.	

(* Useful helper lemma for injectivity *)
Theorem additive_injectivity : forall (a b c : V), a +v b = a +v c -> b = c.
Proof.
	destruct r_th.
	destruct v_th.
	intros.
	(*
	Informally: b = b + 0 = b + c - c = a + c - c = a
	*)
	rewrite <- (v_id0 b) at 1. specialize (v_inv0 a); inversion v_inv0.
	rewrite <- H2. rewrite v_assoc0.
	assert (a +v b = b +v a) as E1.
	{ apply v_comm0. } 
	rewrite <- E1. rewrite H1. 
	assert (a +v c = c +v a) as E2.
	{ apply v_comm0. } 
	rewrite E2. rewrite <- v_assoc0. rewrite H2. rewrite v_id0.
	reflexivity.
Qed.

(* (LADW 1.6) Additive inverse is unique *)
Theorem inv_unique : forall (a b c : V), a +v b = 0v -> a +v c = 0v -> b = c.
Proof.
	intros. rewrite <- H2 in H1.
	apply additive_injectivity in H1.
	assumption.
Qed.

(* (LADW 1.7) Zero scalar times vector is zero vector *)
Theorem zero_sc_is_zero_vec : forall (a : V), 0 *v a = 0v.
Proof.
	(*
	Informally: 
		0*a = (0 + 0)*a = 0*a + 0*a -> 
		0*a - 0*a = 0*a + 0*a - 0*a ->
		0v = 0*a
	*)
	destruct r_th.
	destruct v_th.
	intros.
	assert (0 *v a = 0 *v a) as E1.
	{ reflexivity. }
	rewrite <- (Radd_0_l 0) in E1 at 1.
	rewrite s_dist0 in E1.
	rewrite <- (v_id0 (0 *v a)) in E1 at 3.
	apply additive_injectivity in E1.
	assumption.
Qed.

(* (LADW 1.8) Scalar inverse is vector inverse *)
Theorem sc_inv_is_vec_inv : forall (a b : V), a +v b = 0v -> (-s 1) *v a = b.
Proof.
	(*
	Informally: a + b = 0v = 0*a = (1 - 1)a = a - a -> b = -a
	*)
	destruct r_th.
	destruct v_th.
	intros.
	rewrite <- (zero_sc_is_zero_vec a) in H1.
	rewrite <- s_id0 in H1.
	specialize (Ropp_def 1). rewrite <- Ropp_def in H1. rewrite s_dist0 in H1.
	rewrite v_dist0 in H1. rewrite s_id0 in H1 at 1. symmetry in H1.
	rewrite <- (s_id0 a) in H1 at 3. 
	rewrite s_id0 in H1; rewrite s_id0 in H1.
	apply additive_injectivity in H1.
	assumption.
Qed.

End VectorSpaces.