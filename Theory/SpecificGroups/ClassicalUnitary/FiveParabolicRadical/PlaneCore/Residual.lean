module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Index
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.ResidualAction.Geometric
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Counting
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PCoreSurjective

/-!
# The solvable residual of the unitary-five plane parabolic over F₁₆

The determinant modulo fifth roots has abelian image and kernel the geometric
unipotent--SL₂ subgroup. Perfection of that subgroup identifies the solvable
residual. The SL₂ projection has two-group kernel and two-reduced target, so
its kernel is the canonical two-core. Counting the faithful matrix parameters
gives its order.

Source: the plane-parabolic calculation in Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264.
-/

public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] [CharP F 2] [Finite F] (J : HermitianForm 5 F)

private instance planeParabolic_finite : Finite (planeParabolic J) := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (project_surjective J)
  infer_instance

/-- The geometric unipotent--SL₂ subgroup is exactly the solvable residual,
not the full plane parabolic. -/
theorem plane_solvableResidual_eq (hcard : Nat.card F = 16)
    (hconj : ∀ a, J.conj a = a ^ 4) (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) :
    Subgroup.solvableResidual (planeParabolic J) = planeRadicalLevi J c hc hJ := by
  let : Group.IsPerfect (planeRadicalLevi J c hc hJ) :=
    ResidualAction.planeRadicalLevi_isPerfect J hcard hconj c hc hJ
  apply le_antisymm
  · rw [← planeParabolicDeterminant_ker J c hc hJ hconj]
    apply (Subgroup.map_eq_bot_iff _).mp
    apply le_bot_iff.mp
    simpa only [Subgroup.solvableResidual_eq_bot] using
      Subgroup.map_solvableResidual_le (planeParabolicDeterminant J)
  · exact Subgroup.le_solvableResidual_of_isPerfect _

/-- The entire unipotent subgroup relative to the geometric radical--Levi
subgroup is its canonical two-core. -/
theorem planeRadicalLevi_twoCore_eq (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) :
    pCore 2 (planeRadicalLevi J c hc hJ) =
      (projectiveUnipotent J hJ).subgroupOf (planeRadicalLevi J c hc hJ) := by
  have hu : projectiveUnipotent J hJ ≤ planeRadicalLevi J c hc hJ := le_sup_left
  have hk : IsPGroup 2 (planeRadicalLeviProjection J c hc hJ).ker := by
    rw [planeRadicalLeviProjection_ker]
    exact (projectiveUnipotent_isPGroup J hJ).of_equiv
      (Subgroup.subgroupOfEquivOfLe hu).symm
  have he := (planeRadicalLeviProjection J c hc hJ).comap_pCore_of_ker_isPGroup
    (planeRadicalLeviProjection_surjective J c hc hJ) hk
  rw [ResidualAction.sl_twoCore_eq_bot, MonoidHom.comap_bot,
    planeRadicalLeviProjection_ker] at he
  exact he.symm

/-- Cardinality of the faithful projective plane-unipotent matrix subgroup. -/
theorem projectiveUnipotent_card_four (hcard : Nat.card F = 16)
    (hconj : ∀ a, J.conj a = a ^ 4) (hJ : J.form = 1) :
    Nat.card (projectiveUnipotent J hJ) = 2 ^ 16 := by
  rw [projectiveUnipotent_card]
  exact parameters_card J hcard hconj

end Theory.SpecificGroups.UnitaryFive.PlaneCore
