module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.PlaneCore.Levi.Restriction
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.GroupTheory.Index

/-!
# The flag index of the unitary-five plane parabolic

The exact plane stabilizer acts on the projective line of its marked isotropic
plane. The GL₂ Levi section makes this action transitive. Scalar matrices act
trivially on lines, so the action descends to the actual projective plane
parabolic, and the stabilizer of the marked line is precisely its intersection
with the line parabolic. Orbit--stabilizer therefore gives index `|F| + 1`,
and in particular seventeen over the sixteen-element field.

Only the trace-one scalar and the identity Hermitian matrix are needed from
the unitary model; no description of the unipotent kernel is assumed.

Source: the plane-parabolic calculation underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, F.1.12(7), printed pp.263--264,
with the actual marked flag of `FiveFlag`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
open scoped LinearAlgebra.Projectivization Pointwise
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

/-- The marked line as a point of the projectivization of the marked plane. -/
noncomputable def markedPlanePoint : ℙ F (plane F) :=
  Projectivization.mk'' ((line F).comap (plane F).subtype)
    (((Submodule.comapSubtypeEquivOfLe (line_le_plane F)).finrank_eq).trans
      (finrank_line F))

@[simp] theorem markedPlanePoint_submodule :
    (markedPlanePoint (F := F)).submodule = (line F).comap (plane F).subtype :=
  Projectivization.submodule_mk'' _ _

private theorem submodule_smul (e : plane F ≃ₗ[F] plane F) (p : ℙ F (plane F)) :
    (e • p).submodule = e • p.submodule := by
  induction p using Projectivization.ind with
  | h v hv =>
    simp [Submodule.pointwise_smul_def, Submodule.map_span, LinearEquiv.smul_def]

private theorem mem_point_stabilizer (e : plane F ≃ₗ[F] plane F) (p : ℙ F (plane F)) :
    e ∈ MulAction.stabilizer (plane F ≃ₗ[F] plane F) p ↔
      ∀ v : plane F, e v ∈ p.submodule ↔ v ∈ p.submodule := by
  rw [MulAction.mem_stabilizer_iff,
    ← Projectivization.submodule_injective.eq_iff, submodule_smul]
  change e ∈ MulAction.stabilizer (plane F ≃ₗ[F] plane F) p.submodule ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

/-- The GL₂ section realizes every linear automorphism of the marked plane. -/
theorem planeLinearAction_surjective [CharP F 2] (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) : Function.Surjective (planeLinearAction J) := by
  intro e
  let E := Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F))
  let e' := (planeEquiv F).symm.trans (e.trans (planeEquiv F))
  obtain ⟨g, hg⟩ := planeRestriction_surjective J c hc hJ (E.symm e')
  have he : planeCoordinateAction J g = e' := by
    apply E.symm.injective
    exact hg
  refine ⟨g, ?_⟩
  apply LinearEquiv.ext
  intro v
  apply (planeEquiv F).injective
  have h := congrArg (fun f : (Fin 2 → F) ≃ₗ[F] (Fin 2 → F) => f (planeEquiv F v)) he
  simpa [planeCoordinateAction, e'] using h

/-- Before projectivizing the group, the point stabilizer is the exact flag stabilizer. -/
theorem markedPlanePoint_stabilizer_comap :
    (MulAction.stabilizer (plane F ≃ₗ[F] plane F) (markedPlanePoint (F := F))).comap
      (planeLinearAction J) =
        (specialStabilizer J (line F)).subgroupOf (specialStabilizer J (plane F)) := by
  ext g
  change planeLinearAction J g ∈ MulAction.stabilizer _ _ ↔
    g.val ∈ specialStabilizer J (line F)
  rw [mem_point_stabilizer, markedPlanePoint_submodule, mem_specialStabilizer_iff]
  change (∀ v : plane F, linearAction J g.val v.val ∈ line F ↔ v.val ∈ line F) ↔
    ∀ v, linearAction J g.val v ∈ line F ↔ v ∈ line F
  constructor
  · intro hg v
    constructor
    · intro hv
      have hp : v ∈ plane F :=
        ((mem_specialStabilizer_iff J _ g.val).mp g.property v).mp
          (line_le_plane F hv)
      exact (hg ⟨v, hp⟩).mp hv
    · intro hv
      exact (hg ⟨v, line_le_plane F hv⟩).mpr hv
  · intro hg v
    exact hg v.val

/-- The canonical map onto the projective plane parabolic. -/
def planeFlagProject : specialStabilizer J (plane F) →* planeParabolic J :=
  (project J).subgroupMap (specialStabilizer J (plane F))

theorem planeFlagProject_surjective : Function.Surjective (planeFlagProject J) :=
  (project J).subgroupMap_surjective (specialStabilizer J (plane F))

/-- The permutation action of the SU plane stabilizer on its lines. -/
def specialPlaneFlagPerm : specialStabilizer J (plane F) →* Equiv.Perm (ℙ F (plane F)) :=
  (MulAction.toPermHom (plane F ≃ₗ[F] plane F) (ℙ F (plane F))).comp (planeLinearAction J)

/-- Every projective scalar acts trivially on all lines of the marked plane. -/
theorem project_kernel_le_flag_kernel :
    (planeFlagProject J).ker ≤ (specialPlaneFlagPerm J).ker := by
  intro g hg
  apply Equiv.ext
  intro p
  change planeLinearAction J g • p = p
  apply (mem_point_stabilizer _ p).mpr
  intro v
  have hp : project J g.val = 1 := congrArg Subtype.val hg
  have hs : ProjGenLinGroup.mk g.val.val = 1 := congrArg Subtype.val hp
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨u, hu⟩ := hs
  have he : planeLinearAction J g v = u.val • v := by
    apply Subtype.ext
    change g.val.val.val *ᵥ v.val = u.val • v.val
    rw [← hu]
    exact Matrix.diagonal_const_mulVec _ _
  rw [he]
  exact p.submodule.smul_mem_iff u.ne_zero

/-- Descent to the genuine projective plane parabolic. -/
noncomputable def planeFlagPerm : planeParabolic J →* Equiv.Perm (ℙ F (plane F)) :=
  (planeFlagProject J).liftOfSurjective (planeFlagProject_surjective J)
    ⟨specialPlaneFlagPerm J, project_kernel_le_flag_kernel J⟩

theorem planeFlagPerm_project (g : specialStabilizer J (plane F)) :
    planeFlagPerm J (planeFlagProject J g) = specialPlaneFlagPerm J g := by
  apply MonoidHom.liftOfRightInverse_comp_apply

/-- The genuine plane-parabolic action on one-dimensional subspaces of its plane. -/
noncomputable instance planeFlagMulAction : MulAction (planeParabolic J) (ℙ F (plane F)) :=
  MulAction.compHom _ (planeFlagPerm J)

theorem planeFlag_smul_project (g : specialStabilizer J (plane F)) (p : ℙ F (plane F)) :
    planeFlagProject J g • p = planeLinearAction J g • p := by
  change planeFlagPerm J (planeFlagProject J g) p = _
  rw [planeFlagPerm_project]
  rfl

/-- Transitivity follows from the full linear action furnished by the Levi section. -/
theorem planeFlag_transitive [CharP F 2] (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) : MulAction.IsPretransitive (planeParabolic J) (ℙ F (plane F)) := by
  let : MulAction.IsPretransitive (plane F ≃ₗ[F] plane F) (ℙ F (plane F)) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  constructor
  intro p q
  obtain ⟨e, he⟩ := MulAction.exists_smul_eq (plane F ≃ₗ[F] plane F) p q
  obtain ⟨g, rfl⟩ := planeLinearAction_surjective J c hc hJ e
  exact ⟨planeFlagProject J g, (planeFlag_smul_project J g p).trans he⟩

/-- The descended marked-point stabilizer is the actual projective parabolic overlap. -/
theorem planeFlag_stabilizer :
    MulAction.stabilizer (planeParabolic J) (markedPlanePoint (F := F)) =
      (lineParabolic J ⊓ planeParabolic J).subgroupOf (planeParabolic J) := by
  apply Subgroup.comap_injective (planeFlagProject_surjective J)
  rw [Subgroup.inf_subgroupOf_right]
  ext g
  change (planeFlagProject J g) • markedPlanePoint (F := F) =
      markedPlanePoint (F := F) ↔ project J g.val ∈ lineParabolic J
  rw [planeFlag_smul_project]
  change planeLinearAction J g ∈ MulAction.stabilizer _ _ ↔
    g.val ∈ ((specialStabilizer J (line F)).map (project J)).comap (project J)
  rw [Subgroup.comap_map_eq_self (ker_project_le_specialStabilizer J (line F))]
  exact SetLike.ext_iff.mp (markedPlanePoint_stabilizer_comap J) g

/-- Orbit--stabilizer counts the lines of the marked plane. -/
theorem plane_flag_index_eq_card_add_one [Finite F] [CharP F 2]
    (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    ((lineParabolic J ⊓ planeParabolic J).subgroupOf (planeParabolic J)).index =
      Nat.card F + 1 := by
  let : MulAction.IsPretransitive (planeParabolic J) (ℙ F (plane F)) :=
    planeFlag_transitive J c hc hJ
  rw [← planeFlag_stabilizer J, MulAction.index_stabilizer_of_transitive]
  exact Projectivization.card_of_finrank_two F (plane F) (finrank_plane F)

/-- The flag overlap has index seventeen in the actual U₅(4) plane parabolic. -/
theorem plane_flag_index_seventeen [Finite F] [CharP F 2]
    (hcard : Nat.card F = 16) (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    ((lineParabolic J ⊓ planeParabolic J).subgroupOf (planeParabolic J)).index = 17 := by
  rw [plane_flag_index_eq_card_add_one J c hc hJ, hcard]

end Theory.SpecificGroups.UnitaryFive.PlaneCore
