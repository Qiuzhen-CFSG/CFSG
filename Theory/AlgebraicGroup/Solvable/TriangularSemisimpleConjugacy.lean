module

public import Theory.AlgebraicGroup.Solvable.SemisimpleConjugacy
public import Theory.AlgebraicGroup.Solvable.TorusComplement

/-!
# Semisimple conjugacy for a triangular presentation

This module specializes the solvable torus-unipotent conjugacy theorem to a
fixed triangular presentation.  For a connected solvable algebraic group, the
presentation's diagonal kernel is its connected unipotent radical.  Therefore
any supplied torus complement contains, up to conjugation by a point of that
radical, every semisimple ambient point.

The mathematical work is Borel, *Linear Algebraic Groups*, Chapter III,
Theorem 10.6(4): the lower `SemisimpleConjugacy` module carries out the central
quotient induction and its final Jordan-decomposition argument using the
semisimple commutator factorization theorem.  This module only supplies the
triangular radical certificates and deliberately remains independent of
maximal-torus conjugacy and the later numbered torus results.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every semisimple point of a connected solvable triangularly presented
algebraic group is conjugate into a supplied torus complement by a point of
the presentation's unipotent radical. -/
public theorem TriangularPresentation.semisimpleElement_conjugate_into_torusComplement_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (P : TriangularPresentation G)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (T : ClosedSubgroup G)
    (hT : IsTorusComplement T P.unipotentRadical)
    (s : Variety.Point G) (hs : IsSemisimpleElement G s) :
    ∃ u : Variety.Point G, u ∈ P.unipotentRadical.toSubgroup ∧
      u⁻¹ * s * u ∈ T.toSubgroup := by
  have hUrad : IsUnipotentRadicalSubgroup P.unipotentRadical := by
    intro x
    exact P.mem_unipotentRadical_iff_characteristicFree x
  exact semisimpleElement_conjugate_into_subtorus_of_unipotent_factorization
    T P.unipotentRadical hT.1
      (hUrad.isConnected_of_solvable_connected hsolvable hconnected)
      (hUrad.isUnipotent_of_solvable_connected hsolvable hconnected)
      P.unipotentRadical_normal hT.2.1 s hs

end Theory.AlgebraicGroup
