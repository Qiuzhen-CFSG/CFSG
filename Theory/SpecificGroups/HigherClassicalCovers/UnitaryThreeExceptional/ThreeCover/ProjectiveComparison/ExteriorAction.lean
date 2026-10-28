module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.UnitaryGeometry
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.ExteriorAction.Points
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.ProjectiveComparison.ExteriorAction.Kernel

/-!
# The faithful projective exterior action of PSU₄(3)

`rho` acts on the literal published 252 sign classes and satisfies
`rho_realizesExterior` for the original SU projection, identity Hermitian
form, cube conjugation, and lexicographic compound matrix. Projective scalars
act by a sign because their fourth powers are one. Conversely, the point
kernel forces a scalar exterior map, and hence a scalar original matrix.
The two kernels are therefore exactly equal, proving `rho_injective`.

These unconditional exports discharge the faithful-action and exterior-formula
premises of `modelEquivOfCandidateGeneration` in the parent comparison module.
The separate matrix-pair generation premise remains with that assembly.
Neither quasisimplicity nor an orthogonal-group identification is assumed here.

Source: GLS3 §2.7 and the concrete comparison used for Aschbacher–Smith
I.1.4(5), printed p.408. The compound and exterior-kernel identities retain
the attribution of the ATLAS port (Gerald Höhn and ATLAS contributors;
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).

-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
open Matrix Atlas.Order20160A8.Bivectors
open Theory.SpecificGroups.ClassicalUnitary

local notation "E" => FiniteField.Nine

private theorem matrix_scalar_eq (c : E) : Matrix.scalar (Fin 4) c = c • 1 := by
  rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem project_ker_le_specialPointAction_ker :
    (UnitaryFourThree.project 4).ker ≤ specialPointAction.ker := by
  intro g hg
  have hp : ProjGenLinGroup.mk g.val = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
  rw [ProjGenLinGroup.mk_eq_one] at hp
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hp
  have hA : g.val.val = c • 1 := hc.symm.trans (matrix_scalar_eq c)
  have hd : g.val.val.det = 1 := exteriorSU_det g
  rw [hA, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd
  have hs : c ^ 2 = 1 ∨ c ^ 2 = -1 := by
    apply (sq_eq_one_iff).mp
    simpa only [← pow_mul] using hd
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro i
  apply point_eq_of_sign_choices (pointImage_spec g i)
  rw [exteriorSU_apply]
  rw [hA, exteriorMap_smul, exteriorMap_one, LinearMap.id_apply]
  rcases hs with hs | hs
  · exact Or.inl (by rw [hs, one_smul, Equiv.Perm.one_apply])
  · exact Or.inr (by rw [hs, neg_one_smul, Equiv.Perm.one_apply])

/-- The exterior action descended through the original projective SU image. -/
def rho : UnitaryFourThree.Carrier 4 →* Equiv.Perm Index :=
  (UnitaryFourThree.project 4).liftOfSurjective (UnitaryFourThree.project_surjective 4)
    ⟨specialPointAction, project_ker_le_specialPointAction_ker⟩

@[simp] theorem rho_project (g : SU4) :
    rho (UnitaryFourThree.project 4 g) = specialPointAction g := by
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem rho_realizesExterior : RealizesExterior rho := by
  intro g i
  rw [rho_project]
  simpa only [exteriorSU_apply, specialPointAction_apply] using pointImage_spec g i

theorem specialPointAction_ker_le_project_ker :
    specialPointAction.ker ≤ (UnitaryFourThree.project 4).ker := by
  intro g hg
  have hfix : ∀ i, exteriorMap g.val.val (point i) = point i ∨
      exteriorMap g.val.val (point i) = -point i := by
    intro i
    have h := pointImage_spec g i
    have hi : pointImage g i = i := congrArg (fun e : Equiv.Perm Index => e i)
      (MonoidHom.mem_ker.mp hg)
    simpa only [hi, exteriorSU_apply] using h
  obtain ⟨c, hc⟩ := scalar_of_exterior_sign g.val.val
    (scalar_sign_of_fixes_points (exteriorMap g.val.val) hfix)
  apply MonoidHom.mem_ker.mpr
  apply Subtype.ext
  change ProjGenLinGroup.mk g.val = 1
  rw [ProjGenLinGroup.mk_eq_one]
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  exact ⟨c, (matrix_scalar_eq c).trans hc.symm⟩

/-- The permutation action loses exactly the original projective scalar kernel. -/
theorem specialPointAction_ker_eq_project_ker :
    specialPointAction.ker = (UnitaryFourThree.project 4).ker :=
  le_antisymm specialPointAction_ker_le_project_ker project_ker_le_specialPointAction_ker

/-- Faithfulness needs neither simplicity nor generation by a particular pair. -/
theorem rho_injective : Function.Injective rho := by
  apply (MonoidHom.ker_eq_bot_iff rho).mp
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := UnitaryFourThree.project_surjective 4 x
  have hg : g ∈ specialPointAction.ker := by
    apply MonoidHom.mem_ker.mpr
    simpa only [rho_project] using MonoidHom.mem_ker.mp hx
  exact MonoidHom.mem_ker.mp (specialPointAction_ker_le_project_ker hg)

/-- The unconditional action witness required by the concrete cover comparison. -/
theorem exists_faithful_exteriorAction :
    ∃ ρ : UnitaryFourThree.Carrier 4 →* Equiv.Perm Index,
      Function.Injective ρ ∧ RealizesExterior ρ :=
  ⟨rho, rho_injective, rho_realizesExterior⟩

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryThreeExceptional.ThreeCover.UnitaryGeometry
