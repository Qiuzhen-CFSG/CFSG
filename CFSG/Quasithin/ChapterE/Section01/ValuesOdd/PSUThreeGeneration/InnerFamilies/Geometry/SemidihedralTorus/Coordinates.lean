module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Frames

/-!
# Sign and Frobenius coordinates for the four-group centralizer

The formula below specifies automorphisms of the actual projective unitary
image, using a diagonal sign matrix and the stored Hermitian involution.
It asserts neither that arbitrary two-actors admit these coordinates nor
that a Sylow subgroup is monomial. The missing placement concerns only the
pointwise centralizer of the four-group inside the ambient Sylow subgroup.

This is a coordinate contract for Aschbacher--Smith E.1.14(7), printed p.214,
and the semidihedral unitary case of A.3.21(a)--(b), printed p.55.
-/

public section
open Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
variable {F : Type*} [Field F]

/-- The literal diagonal matrix of three independently chosen signs. -/
@[expose] def signGL (ε : Fin 3 → Bool) : GL (Fin 3) F :=
  UnitaryThree.OddTorusNormalizer.diagonalHom (fun i => if ε i then -1 else 1)

/-- An actual projective formula using a diagonal sign matrix and either identity or Frobenius. -/
@[expose] def HasSignSemilinearForm (J : HermitianForm 3 F)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) : Prop :=
  ∃ (ε : Fin 3 → Bool) (σ : F ≃+* F), (σ = 1 ∨ σ = J.conj) ∧
    ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk (signGL ε) *
        ProjGenLinGroup.map σ.toRingHom x.val * (ProjGenLinGroup.mk (signGL ε))⁻¹


end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus
