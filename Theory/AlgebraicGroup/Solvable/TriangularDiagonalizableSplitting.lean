module

public import Theory.AlgebraicGroup.Solvable.TorusComplementConjugacy
public import Theory.AlgebraicGroup.Solvable.TriangularSection

/-!
# Diagonalizable subgroups of connected solvable groups

This module proves Borel, *Linear Algebraic Groups*, Chapter III, Theorem
10.6(5), in the setting of a fixed triangular presentation.  A connected
solvable group has an honest torus complement to the presentation's diagonal
kernel by `TriangularSection`.  The characteristic-free triangular kernel
criterion identifies that kernel with the connected unipotent radical.

The complement-conjugacy argument then places an arbitrary diagonalizable
closed subgroup in a conjugate of this complement.  Crucially, the subgroup
need not be connected: Noetherianity reduces its centralizer to a finite list,
and Proposition 9.3(2) keeps the successive fixed subgroups in the unipotent
radical connected.  The last unipotent factor is also semisimple, so Jordan
uniqueness makes it trivial.  The proof is characteristic-free and does not
use maximal-torus conjugacy or the later numbered torus containment theorems.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every diagonalizable closed subgroup of a connected solvable,
triangularly presented algebraic group is contained in a closed subtorus. -/
public theorem TriangularPresentation.exists_subtorus_containing_diagonalizableClosedSubgroup_of_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (P : TriangularPresentation G)
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (S : ClosedSubgroup G)
    (hS : IsDiagonalizableClosedSubgroup S) :
    ∃ T : ClosedSubgroup G, IsSubtorus T ∧ S ≤ T := by
  obtain ⟨T, hT, -⟩ :=
    P.exists_torusComplement_diagonalImageIso_of_solvable_connected
      hsolvable hconnected
  have hUrad : IsUnipotentRadicalSubgroup P.unipotentRadical := by
    intro x
    exact P.mem_unipotentRadical_iff_characteristicFree x
  obtain ⟨u, -, hTu, hSTu⟩ :=
    diagonalizableClosedSubgroup_conjugate_into_torusComplement
      hsolvable hconnected P.unipotentRadical T S hUrad hT hS
  exact ⟨T.conjugate u, hTu, hSTu⟩

end Theory.AlgebraicGroup
