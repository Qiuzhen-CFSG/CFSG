module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointQuotient
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.UnitaryFourPointRadicalSpecial

/-!
# Point-local residuals in the standard unitary-four model

For q = 2^n > 2, the nonidentity fixed-field scalar and the nontrivial
quadratic Frobenius discharge the hypotheses of the radical-commutator
calculation. The matrix vector stabilizer and its faithful projective image
are therefore perfect and equal their solvable residuals. At q = 2 both
local groups are solvable and their solvable residuals are trivial.

Every two-subgroup of the point parabolic lies in the vector stabilizer,
since its scalar image lies in the odd-order matrix-field unit group.
The resulting embedded core equalities retain the literal subgroup maps
and identify the parabolic core with the already constructed radical.
They apply, in particular, when an ambient Sylow subgroup is assembled.

These are the first local factor's residual and containment assertions in
Aschbacher--Smith F.1.12(II), printed pp. 263--264 of `refs/quasithin.pdf`.
The residual is the solvable residual; O₂ occurs only in the core statements.
The complete amalgam and its Sylow configuration are assembled separately.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
open Theory.SpecificGroups.ClassicalUnitary
variable (n : ℕ) (hn : 1 ≤ n)

include hn in
private theorem exists_fixed_scalar (hn2 : 1 < n) :
    ∃ a : FixedField n, a ≠ 0 ∧ a ≠ 1 := by
  classical
  let := Fintype.ofFinite (FixedField n)
  have hc : 2 < Nat.card (FixedField n) := by
    rw [fixedField_card n hn]
    calc
      2 = 2 ^ 1 := rfl
      _ < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn2
  by_contra! h
  have hs : (Finset.univ : Finset (FixedField n)) ⊆ {0, 1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · simp [h a ha]
  have hle : Nat.card (FixedField n) ≤ 2 := by
    have hle' : Fintype.card (FixedField n) ≤ 2 := by
      simpa using Finset.card_le_card hs
    exact Nat.card_eq_fintype_card.trans_le hle'
  omega

/-- For q > 2 the actual vector stabilizer is perfect. -/
theorem matrixLocal_isPerfect (hn2 : 1 < n) : Group.IsPerfect (MatrixLocal n hn) := by
  obtain ⟨a,ha,ha1⟩ := exists_fixed_scalar n hn hn2
  exact UnitaryFourPointResidual.localSU_isPerfect (MatrixField n) (fieldConj n)
    (fieldConj_involutive n hn) (fieldConj_nontrivial n hn) a ha ha1

/-- The first point factor equals its solvable residual when q > 2. -/
theorem matrixLocal_solvableResidual_eq_top (hn2 : 1 < n) :
    Subgroup.solvableResidual (MatrixLocal n hn) = ⊤ := by
  let : Group.IsPerfect (MatrixLocal n hn) := matrixLocal_isPerfect n hn hn2
  exact Subgroup.solvableResidual_eq_top

/-- Perfectness transported through the literal matrix-to-projective local equivalence. -/
theorem projectiveLocal_isPerfect (hn2 : 1 < n) : Group.IsPerfect (ProjectiveLocal n hn) := by
  let : Group.IsPerfect (MatrixLocal n hn) := matrixLocal_isPerfect n hn hn2
  exact Group.IsPerfect.ofSurjective (f := (localEquiv n hn).toMonoidHom)
    (localEquiv n hn).surjective

/-- The projective point factor equals its solvable residual for q > 2. -/
theorem projectiveLocal_solvableResidual_eq_top (hn2 : 1 < n) :
    Subgroup.solvableResidual (ProjectiveLocal n hn) = ⊤ := by
  let : Group.IsPerfect (ProjectiveLocal n hn) := projectiveLocal_isPerfect n hn hn2
  exact Subgroup.solvableResidual_eq_top

/-- The binary exception: the radical and the SL₂(2) quotient are both solvable. -/
theorem matrixLocal_isSolvable_two : Group.IsSolvable (MatrixLocal 1 (by decide)) := by
  exact UnitaryFourPointResidual.localSU_isSolvable_of_fixedField_card_two
    (MatrixField 1) (fieldConj 1) (fieldConj_involutive 1 (by decide))
    (fixedField_card 1 (by decide))

/-- At q = 2 the matrix point factor has trivial solvable residual. -/
theorem matrixLocal_solvableResidual_two :
    Subgroup.solvableResidual (MatrixLocal 1 (by decide)) = ⊥ := by
  let : Group.IsSolvable (MatrixLocal 1 (by decide)) := matrixLocal_isSolvable_two
  exact Subgroup.solvableResidual_eq_bot

/-- Solvability of the actual projective point factor at q = 2. -/
theorem projectiveLocal_isSolvable_two : Group.IsSolvable (ProjectiveLocal 1 (by decide)) := by
  let : Group.IsSolvable (MatrixLocal 1 (by decide)) := matrixLocal_isSolvable_two
  exact Group.isSolvable_of_isSolvable_injective
    (f := (localEquiv 1 (Nat.le_refl 1)).symm.toMonoidHom) (localEquiv 1 (Nat.le_refl 1)).symm.injective

/-- At q = 2 the projective point factor has trivial solvable residual. -/
theorem projectiveLocal_solvableResidual_two :
    Subgroup.solvableResidual (ProjectiveLocal 1 (by decide)) = ⊥ := by
  let : Group.IsSolvable (ProjectiveLocal 1 (by decide)) := projectiveLocal_isSolvable_two
  exact Subgroup.solvableResidual_eq_bot

/-- Every matrix two-subgroup in the point parabolic lies in the first local factor. -/
theorem twoSubgroup_le_matrixLocal (S : Subgroup (MatrixGroup n hn))
    (hS : IsPGroup 2 S) (hSP : S ≤ pointParabolicMatrix n hn) : S ≤ MatrixLocal n hn :=
  UnitaryFourPointResidual.twoSubgroup_le_localSU _ _ S hS hSP

/-- Every projective two-subgroup in the point parabolic lies in the first local factor. -/
theorem twoSubgroup_le_projectiveLocal (S : Subgroup (ProjectiveGroup n hn))
    (hS : IsPGroup 2 S) (hSP : S ≤ pointParabolic n hn) : S ≤ ProjectiveLocal n hn :=
  UnitaryFourPointResidual.twoSubgroup_le_localPSU _ _ S hS hSP

/-- In particular adjoining any such two-subgroup does not enlarge the matrix factor. -/
theorem matrixLocal_sup_twoSubgroup (S : Subgroup (MatrixGroup n hn))
    (hS : IsPGroup 2 S) (hSP : S ≤ pointParabolicMatrix n hn) :
    MatrixLocal n hn ⊔ S = MatrixLocal n hn :=
  sup_eq_left.mpr (twoSubgroup_le_matrixLocal n hn S hS hSP)

/-- The same adjoining statement in the actual projective model. -/
theorem projectiveLocal_sup_twoSubgroup (S : Subgroup (ProjectiveGroup n hn))
    (hS : IsPGroup 2 S) (hSP : S ≤ pointParabolic n hn) :
    ProjectiveLocal n hn ⊔ S = ProjectiveLocal n hn :=
  sup_eq_left.mpr (twoSubgroup_le_projectiveLocal n hn S hS hSP)

/-- Relative overgroups between the vector stabilizer and parabolic have the same two-core. -/
theorem matrixLocal_core_map (H : Subgroup (MatrixGroup n hn))
    (hLH : MatrixLocal n hn ≤ H) (hHP : H ≤ pointParabolicMatrix n hn) :
    (pCore 2 (MatrixLocal n hn)).map (MatrixLocal n hn).subtype =
      (pCore 2 H).map H.subtype :=
  UnitaryFourPointResidual.localSU_core_map _ _ H hLH hHP

/-- The identical core assertion for relative projective overgroups. -/
theorem projectiveLocal_core_map (H : Subgroup (ProjectiveGroup n hn))
    (hLH : ProjectiveLocal n hn ≤ H) (hHP : H ≤ pointParabolic n hn) :
    (pCore 2 (ProjectiveLocal n hn)).map (ProjectiveLocal n hn).subtype =
      (pCore 2 H).map H.subtype :=
  UnitaryFourPointResidual.localPSU_core_map _ _ H hLH hHP

/-- The concrete radical is the embedded two-core of the full matrix parabolic. -/
theorem pointParabolicMatrix_twoCore :
    (pCore 2 (pointParabolicMatrix n hn)).map (pointParabolicMatrix n hn).subtype =
      (Radical n hn).map (MatrixLocal n hn).subtype := by
  rw [radical_eq_twoCore]
  exact (matrixLocal_core_map n hn _ (matrixLocal_le_pointParabolic n hn) le_rfl).symm

/-- The intrinsic projective two-core is the radical transported by `localEquiv`. -/
theorem projectiveLocal_twoCore : pCore 2 (ProjectiveLocal n hn) =
    (Radical n hn).map (localEquiv n hn).toMonoidHom := by
  rw [radical_eq_twoCore, pCore_map_iso]

/-- The full projective parabolic has this same embedded radical as its two-core. -/
theorem pointParabolic_twoCore :
    (pCore 2 (pointParabolic n hn)).map (pointParabolic n hn).subtype =
      ((Radical n hn).map (localEquiv n hn).toMonoidHom).map
        (ProjectiveLocal n hn).subtype := by
  rw [← projectiveLocal_twoCore]
  exact (projectiveLocal_core_map n hn _ (projectiveLocal_le_pointParabolic n hn) le_rfl).symm

/-- For q > 2 the first local factor is the solvable residual of the full point parabolic. -/
theorem pointParabolicMatrix_solvableResidual (hn2 : 1 < n) :
    (Subgroup.solvableResidual (pointParabolicMatrix n hn)).map
      (pointParabolicMatrix n hn).subtype = MatrixLocal n hn := by
  let : Group.IsPerfect (MatrixLocal n hn) := matrixLocal_isPerfect n hn hn2
  exact UnitaryFourPointResidual.pointParabolic_solvableResidual_eq_of_perfect _ _

/-- The literal projective point parabolic has the first local factor as its solvable residual. -/
theorem pointParabolic_solvableResidual (hn2 : 1 < n) :
    (Subgroup.solvableResidual (pointParabolic n hn)).map
      (pointParabolic n hn).subtype = ProjectiveLocal n hn := by
  let e : pointParabolicMatrix n hn ≃* pointParabolic n hn :=
    (pointParabolicMatrix n hn).equivMapOfInjective (projection n hn)
      (projection_injective n hn)
  have he : (pointParabolic n hn).subtype.comp e.toMonoidHom =
      (projection n hn).comp (pointParabolicMatrix n hn).subtype := rfl
  calc
    _ = ((Subgroup.solvableResidual (pointParabolicMatrix n hn)).map e.toMonoidHom).map
        (pointParabolic n hn).subtype := by
      rw [Subgroup.map_solvableResidual_eq e.toMonoidHom e.surjective]
    _ = ((Subgroup.solvableResidual (pointParabolicMatrix n hn)).map
        (pointParabolicMatrix n hn).subtype).map (projection n hn) := by
      rw [Subgroup.map_map, he, Subgroup.map_map]
    _ = ProjectiveLocal n hn := by
      rw [pointParabolicMatrix_solvableResidual n hn hn2]
      rfl

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour.PointLocal
