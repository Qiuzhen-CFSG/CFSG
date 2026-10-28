module

public import Theory.Representation.NoncyclicDegreeThree

/-!
# Centralizers of noncyclic determinant-one subgroups in degree three

A cross-characteristic abelian subgroup of GL₃ over a finite field has abelian
centralizer if it is noncyclic and every element has determinant one. This module
provides the finite-field interface for the linear and unitary Cartan arguments.

The proof in `NoncyclicDegreeThree` embeds the matrices entrywise in an algebraic
closure, preserving determinant and faithfulness, and collects bases of all
simultaneous character spaces. If two basis vectors have the same character,
the determinant relation forces its kernel to fix the third vector too. That
character is then faithful, making the finite group cyclic. Thus all three
weights are distinct, their spaces are lines, and centralizing operators commute.
In particular, neither distinct weights nor one-dimensional weight spaces are
additional hypotheses.

Source: the degree-three calculation underlying Aschbacher--Smith, A.3.21(c),
printed pp.55--56, and the Cartan argument on pp.510--511 of `refs/quasithin.pdf`.
-/

public section

namespace Representation

/-- A noncyclic cross-characteristic abelian determinant-one subgroup of GL₃
over a finite field has abelian centralizer in the full general linear group. -/
theorem rankThreeDeterminantCentralizer
    {F : Type*} [Field F] [Finite F] (R : Subgroup (GL (Fin 3) F))
    [IsMulCommutative R] (horder : (Nat.card R : F) ≠ 0) (hn : ¬ IsCyclic R)
    (hdet : ∀ x : R, Matrix.GeneralLinearGroup.det x.val = 1) :
    IsMulCommutative (Subgroup.centralizer (R : Set (GL (Fin 3) F))) :=
  generalLinear_centralizer_isMulCommutative_of_noncyclic_det_one R horder hn hdet

end Representation
