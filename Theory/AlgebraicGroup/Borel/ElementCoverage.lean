module

public import Theory.AlgebraicGroup.Borel.ElementCoverage.ClosedImage
public import Theory.AlgebraicGroup.Borel.Existence

/-!
# Reduction of Borel element coverage to a dense conjugacy image

The conjugacy saturation of every Borel is closed, by its genuine complete
homogeneous-space model. Thus a dense conjugacy saturation gives element
coverage. It suffices to find any connected solvable closed subgroup with
dense conjugacy saturation: Borel existence places it in a Borel, and genuine
Borel conjugacy transfers the conclusion to the supplied Borel.

This is the last assembly step of Borel, *Linear Algebraic Groups*, §11.10
(`refs/KGroup/Bor1/Chapter4.tex`), and the element-coverage clause of GLS3,
Theorem 1.6.3 (`refs/KGroup/GLS3/Chapter1.tex`). The density input is explicit
here. Its finite-fiber proof and the earlier Cartan regular-point witness are
still required for unconditional coverage.
-/

namespace Theory.AlgebraicGroup.BorelElementCoverage

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- A dense Borel conjugacy saturation is all of the group, since completeness
has already made it closed. -/
public theorem exists_conjugate_mem_of_dense
    {B : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (hdense : Dense (conjugacySaturation B)) (x : Variety.Point G) :
    ∃ g : Variety.Point G, g⁻¹ * x * g ∈ B.toSubgroup := by
  have hclosed := Variety.isClosed_iff_isZariskiClosed.mpr
    (isZariskiClosed_conjugacySaturation hB)
  have hx := hdense x
  rw [hclosed.closure_eq] at hx
  exact hx

/-- A connected solvable closed subgroup with dense conjugacy saturation
supplies element coverage for every Borel. -/
public theorem exists_conjugate_mem_of_dense_solvable
    {B : ClosedSubgroup G} (hB : IsBorelSubgroup B)
    (H : ClosedSubgroup G)
    (hconnected : _root_.IsConnected (H : Set (Variety.Point G)))
    (hsolvable : Group.IsSolvable (Variety.Point H.carrierVariety))
    (hdense : Dense (conjugacySaturation H)) (x : Variety.Point G) :
    ∃ g : Variety.Point G, g⁻¹ * x * g ∈ B.toSubgroup := by
  obtain ⟨C, hC, hHC⟩ :=
    exists_borelSubgroup_containing_connected_solvable H hconnected hsolvable
  apply exists_conjugate_mem_of_dense hB ?_ x
  obtain ⟨g, rfl⟩ := BorelGeometricConjugacy.conjugacy hC hB
  rw [conjugacySaturation_conjugate]
  exact hdense.mono (conjugacySaturation_mono hHC)

end Theory.AlgebraicGroup.BorelElementCoverage
