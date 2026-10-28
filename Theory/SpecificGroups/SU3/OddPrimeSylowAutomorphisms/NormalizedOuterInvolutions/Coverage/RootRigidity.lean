module

public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Coordinates
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.Diagonal
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.FirstField
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.OppositeCompatibility
public import Theory.SpecificGroups.SU3.OddPrimeSylowAutomorphisms.NormalizedOuterInvolutions.Coverage.RootRigidity.TorusPreservation

/-!
# Semilinear rigidity on opposite Hermitian root groups

An automorphism preserving both root groups over the prime-square field acts
on them by a common field automorphism and a genuine unitary diagonal matrix.
`TorusPreservation` recovers the torus, its involution at `-1`, and the Weyl
coset from the two preserved roots. `FirstField` recovers the upper field
formula using the additive span of the weights `k / conj(k)^2`.
`OppositeCompatibility` compares the Bruhat identity, retaining and cancelling
the projective scalar, to obtain the matching opposite first coordinate.

The common first-coordinate formulas determine the full coordinates: odd
characteristic and equivariance at `-1` eliminate central shears. `Diagonal`
realizes both formulas by `diag(t,1,conj(t)⁻¹)`. This proves the root-rigidity
part of Steinberg, Theorem 36, steps (2)–(7), in
`refs/KGroup/GLS3/Chapter2St1.tex`, using the actual unitary representatives
required in GLS3 §2.7. Characteristic three is included. Generation and
normalization of arbitrary ambient automorphisms belong to the separate
geometric assembly; neither is a premise of root rigidity.
-/

open Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- Common first-coordinate formulas determine the two complete root formulas,
using the same actual unitary diagonal representative. -/
public theorem root_formulas_of_first_coordinate_normalization
    (h2 : (2 : E) ≠ 0) (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ)
    (ht : b (hermitianTorusPSU J hJ (-1)) = hermitianTorusPSU J hJ (-1))
    (σ : E ≃+* E) (t : Eˣ)
    (hfirstU : ∀ z : hermitianUnipotentCoord J,
      (rootCoordinateAut J hJ b hU z).val.1 = (t : E) * σ z.val.1)
    (hfirstV : ∀ z : hermitianUnipotentCoord J,
      (oppositeCoordinateAut J hJ b hV z).val.1 = (J.conj (t : E))⁻¹ * σ z.val.1) :
    (∀ z : hermitianUnipotentCoord J,
      (b (root J hJ z)).val = ProjGenLinGroup.mk (diagonalUnitary J hJ t).val *
        ProjGenLinGroup.map σ.toRingHom (root J hJ z).val *
        (ProjGenLinGroup.mk (diagonalUnitary J hJ t).val)⁻¹) ∧
    (∀ z : hermitianUnipotentCoord J,
      (b (oppositeRoot J hJ z)).val = ProjGenLinGroup.mk (diagonalUnitary J hJ t).val *
        ProjGenLinGroup.map σ.toRingHom (oppositeRoot J hJ z).val *
        (ProjGenLinGroup.mk (diagonalUnitary J hJ t).val)⁻¹) := by
  have hu : rootCoordinateAut J hJ b hU = scaledFieldCoordAut J σ t :=
    coordAut_ext_of_first J h2 _ _
      (fun z => (hfirstU z).trans (scaledFieldCoordAut_fst J σ t z).symm)
      (rootCoordinateAut_neg_equivariant J hJ b hU ht)
      (scaledFieldCoordAut_neg_equivariant J σ t)
  have hv : oppositeCoordinateAut J hJ b hV =
      scaledFieldCoordAut J σ (Units.map J.conj.toMonoidHom t)⁻¹ := by
    apply coordAut_ext_of_first J h2
    · intro z
      rw [scaledFieldCoordAut_fst, hfirstV]
      simp
    · exact oppositeCoordinateAut_neg_equivariant J hJ b hV ht
    · exact scaledFieldCoordAut_neg_equivariant J σ _
  constructor
  · intro z
    rw [← rootCoordinateAut_spec J hJ b hU z, hu]
    exact scaledFieldCoordAut_root J hJ σ t z
  · intro z
    rw [← oppositeCoordinateAut_spec J hJ b hV z, hv]
    exact scaledFieldCoordAut_opposite J hJ σ t z

/-- Preservation of the two opposite roots yields their semilinear formulas
with one field automorphism and one actual unitary matrix. This has exactly
the conclusion required by `semilinear_coverage_of_root_geometry`'s rigidity
input. The matrix-field cardinality suffices; fixed-field cardinality,
perfectness and simplicity are not needed for this step. -/
public theorem root_formulas_of_opposite_root_preserving
    {p : ℕ} (hp : p.Prime) (hp8 : p % 8 = 3) (hcard : Nat.card E = p ^ 2)
    (b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : (rootGroup J hJ).map b.toMonoidHom = rootGroup J hJ)
    (hV : (oppositeRootGroup J hJ).map b.toMonoidHom = oppositeRootGroup J hJ) :
    ∃ (σ : E ≃+* E) (u : J.unitarySubgroup),
      (∀ z : hermitianUnipotentCoord J,
        (b (root J hJ z)).val = ProjGenLinGroup.mk u.val *
          ProjGenLinGroup.map σ.toRingHom (root J hJ z).val *
          (ProjGenLinGroup.mk u.val)⁻¹) ∧
      (∀ z : hermitianUnipotentCoord J,
        (b (oppositeRoot J hJ z)).val = ProjGenLinGroup.mk u.val *
          ProjGenLinGroup.map σ.toRingHom (oppositeRoot J hJ z).val *
          (ProjGenLinGroup.mk u.val)⁻¹) := by
  have hp3 : 3 ≤ p := by omega
  have h2 : (2 : E) ≠ 0 := two_ne_zero_of_prime_square hp hp3 hcard
  obtain ⟨hT, ht, hw⟩ :=
    torus_and_weyl_of_opposite_root_preserving J hJ hp hp8 hcard b hU hV
  obtain ⟨σ, t, hfirstU⟩ :=
    root_first_field_of_torus_preserving J hJ hp hp3 hcard b hU hT
  have hfirstV := opposite_first_of_root_first J hJ h2 b hU hV hT ht hw σ t hfirstU
  exact ⟨σ, diagonalUnitary J hJ t,
    root_formulas_of_first_coordinate_normalization J hJ h2 b hU hV ht σ t hfirstU hfirstV⟩

end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
