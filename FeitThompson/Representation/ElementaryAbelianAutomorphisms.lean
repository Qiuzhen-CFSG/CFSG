/-
Authors: Yusen Tang
-/

module

public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.ZMod.Torsion
public import FeitThompson.BGsection1.CriticalSubgroupLemmas
public import FeitThompson.Burnside.NormalComplement
public import FeitThompson.Extraspecial
public import FeitThompson.LinearAlgebra.BlockElementaryMap
public import FeitThompson.Representation.ConjugateRep
public import FeitThompson.BGsection2.EndFieldRep
public import FeitThompson.Representation.TwoDimensionalOddOrder

open Representation
open MonoidAlgebra
open Module
open Module.End
open Polynomial
open scoped DirectSum
open scoped BigOperators
open scoped TensorProduct
open scoped MonoidAlgebra
open scoped Function
open scoped IsMulCommutative
/-
**Kind**: Theorem
**Note**: Lemma 2.7
**Stmt**:
Let $p,q$ be distinct primes.
Let $P,Q$ be elementary abelian group of $p^2, q^2$ respectively.
Assume that $Q \subseteq \Aut(P)$.
Then
(a) $q$ divides $(p - 1)$.
(b) There exists $\alpha \in Q^\#$ and an integer $r$ such that $x^\alpha = x^r$ for every $x \in P, r^q \equiv 1 (\mod p), r \not\equiv 1 (\mod p)$.
-/


