module

public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicGeometry
public import Theory.SpecificGroups.ClassicalUnitary.FiveIsotropicTransitivity
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTwoLocal

/-!
# Geometric coverage and two-locality of the PSU₅(4) parabolics

The fixed-radical argument places every actual projective two-local inside
the stabilizer of a nonzero totally isotropic line or plane. An actual SU
matrix carrying a standard flag member to that subspace identifies the
stabilizer with the required conjugate parabolic in PSU.

The proved special-unitary transitivity theorem discharges the geometric
input over the field of sixteen elements with fourth-power conjugation.
Both standard parabolics are themselves two-local: they are the ambient
normalizers of the respective nonidentity projective shear two-subgroups.
Thus coverage and two-locality require no additional geometric premises.

Source: Aschbacher--Smith, Theorem 0.1.2(1), printed p.4 (Theorem 0.1.1(1),
p.482), and F.1.12(7), printed pp.263--264, in `refs/quasithin.pdf`.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryFive.Coverage

open BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
open Theory.SpecificGroups.UnitaryFive.IsotropicGeometry

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Isotropic-subspace transitivity completes the actual two-local cover.
The normalizer lifting and nonzero isotropic subspace are proved upstream. -/
public theorem twoLocal_parabolic_cover_of_isotropic_transitivity
    (J : HermitianForm 5 F) (hJ : J.form = 1)
    (htrans : ∀ W : Submodule F (Fin 5 → F), W ≠ ⊥ → W ≤ orthogonal J W →
      ∃ (b : Bool) (g : J.specialSubgroup),
        W = (if b then plane F else line F).map (linearAction J g).toLinearMap)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsTwoLocal M) :
    ∃ (b : Bool) (g : ProjectiveSpecialUnitaryMatrixGroup J),
      M ≤ (if b then planeParabolic J else lineParabolic J).map
        (MulAut.conj g).toMonoidHom := by
  obtain ⟨W, hn, hi, _, hMW⟩ := projective_twoLocal_stabilizes_isotropic J hJ M hM
  obtain ⟨b, g, hg⟩ := htrans W hn hi
  refine ⟨b, project J g, ?_⟩
  have he : parabolic J W =
      (if b then planeParabolic J else lineParabolic J).map
        (MulAut.conj (project J g)).toMonoidHom := by
    rw [hg, parabolic_map_action]
    cases b <;> rfl
  exact he ▸ hMW

/-- Every actual two-local of PSU₅(4) lies in a conjugate of the standard
line or plane parabolic. The special-unitary transitivity premise is proved. -/
public theorem twoLocal_parabolic_cover
    (J : HermitianForm 5 F) (hcard : Nat.card F = 16)
    (hconj : ∀ x, J.conj x = x ^ 4) (hJ : J.form = 1)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsTwoLocal M) :
    ∃ (b : Bool) (g : ProjectiveSpecialUnitaryMatrixGroup J),
      M ≤ (if b then planeParabolic J else lineParabolic J).map
        (MulAut.conj g).toMonoidHom :=
  twoLocal_parabolic_cover_of_isotropic_transitivity J hJ
    (IsotropicTransitivity.transitive J hcard hconj hJ) M hM

/-- Each standard parabolic is an actual two-local, witnessed by its
nonidentity projective shear two-subgroup and exact ambient normalizer. -/
public theorem parabolic_isTwoLocal (J : HermitianForm 5 F) (hJ : J.form = 1)
    (b : Bool) : IsTwoLocal (if b then planeParabolic J else lineParabolic J) := by
  cases b
  · exact lineParabolic_isTwoLocal J hJ
  · exact planeParabolic_isTwoLocal J hJ

end CFSG.Quasithin.MainConverse.UnitaryFive.Coverage
