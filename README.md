The theorem I've set out to prove in Coq is the Tower Theorem for field extensions:

Formally, given a finite field extension with degree [K3 : K1] and given an intermediate field K2, we have that [K3 : K1] = [K3 : K2][K2 : K1].

My proof of this will involve the fact a field extension K3/K1 can be thought of the same as K3 as a K1-vector space, so the degree [K3 : K1] is the same as the cardinality of K3 as a K1-vector space.

Therefore, I've opted to use Mathematical Components's framework for field extensions and build my own library (most of it, anyways) for vector spaces, then bridge the gap between the two in order to prove the Tower Theorem.

Here's a basic outline of the theorems we'll want in order to prove the Tower Theorem:

1. If L/K is a field extension, then L is also a K-vector space
2. If K3 is a K2-VS, and K2 is a K1-VS, then K3 is a K1-VS whose basis has cardinality equal to the product of the bases of K3 as a K2-VS and K2 as a K1-VS

This project owes a great deal of its initial framework (almost all of the VectorAxioms module) to the work done by Quinn Dougherty on his YouTube series "Linear Algebra Done Right In Coq". I would not have been able to formalize Vector Spaces without this series.

For exercises to prove as the library is built up, I am choosing to use Linear Algebra Done Wrong, the textbook we use in our Abstract Linear Algebra course at UChicago.