Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export VectorFields LinearCombinations.
Set Default Goal Selector "!".

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
Module Type TowerTheorem.
Axiom (F1 F2 F3 : Type).
Context `{Field F1}.
Context `{Field F2}.
Context `{Field F3}.
(* 
	Here we are using Field notation to make the extension property obvious.
	We are taking as a given that F3/F2, F2/F1, and F3/F1 are valid field
	extensions, which by definition means that F3 is a F2-vector space, etc.
	So we define operations for each vector space here. Since each field is
	a subset of F3, each uses the same additive/multiplicative operations,
	which will make the following proofs clean up nicely.
*)
Axiom (E21_0 : F1).
Notation "0_21" := E21_0.
Axiom (v_add_21 : F2 -> F2 -> F2) (s_v_mult_21 : F1 -> F2 -> F2).
Infix "+_21" := v_add_21 (at level 50).
Infix "*_21" := s_v_mult_21 (at level 60).
Axiom E21_th : vector_space_theory v_add_21 s_v_mult_21 0_21 eq.


Axiom F32_th : vector_space_theory v_add s_v_mult 0v eq.
Axiom F31_th : vector_space_theory v_add s_v_mult 0v eq.



(* Proof that this set is linearly independent *)
(* 
	Informally:
	Assume that such a set is dependent, so a nontrivial combination c_k * u_i * v_j 
	exists. Then we have that either v_j's are dependent (a contradiction, 
	since we assume it's a basis for V3/V2), or each combination of c_k * u_i 
	is zero. But u_j's are also independent. Hence this set is independent.
*)

(* Proof that this set spans *)
(*
	Informally:
	Let l be a vector in V3. Then it can be written with V to be a combination 
	of vectors b_j*v_j, where b_j is in F2. Then b_j can be written as a combination 
	of vectors c_iu_i, where c_i is in F1. Each product u_i*v_j is in F3 and each
	coefficient c_i is in F1, so we can describe any vector as a linear combination 
	of vector products u_i*v_j, so this set indeed spans.
*)

(* Proof that this set forms a basis *)

(* Proof of the Tower Theorem for field extensions *)