The theorem I've set out to prove in Coq is the Tower Theorem for field extensions:

Formally, given a finite field extension with degree [K3 : K1] and given an intermediate field K2, we have that [K3 : K1] = [K3 : K2][K2 : K1].

My proof of this will involve the fact a field extension K3/K1 can be thought of the same as K3 as a K1-vector space (VS), so the degree [K3 : K1] is the the cardinality of K3 as a K1-VS. Therefore the Tower Theorem reduces to the linear-algebraic theorem that if K3 is a K2-VS, and K2 is a K1-VS, then K3 is a K1-VS whose basis has cardinality equal to the product of the cardinality of the bases of K3 as a K2-VS and K2 as a K1-VS (in fact, you can construct its basis by taking the cartesian product of these sub-bases).

This project owes a great deal of its initial framework (basically all of the VectorAxioms module) to the work done by Quinn Dougherty on his YouTube series "Linear Algebra Done Right In Coq". The VectorAxioms module is therefore external code and not my own work. His code can be seen here: (insert github link). All proofs are my own work.