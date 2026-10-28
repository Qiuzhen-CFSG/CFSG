module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.NormalizerCalculation.Geometry
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.UnitaryConjugation

/-!
# Lifting semilinear socle actions to coset control

An extension of the actual PGU image marks its PSU socle and hence transports
the ambient normalizer action to projective matrices. Its kernel is exactly
the ambient centralizer. When that centralizer lies in the extension image,
a unitary conjugation lifts to an element of that image.

Two compatible semilinear actions with the same field part have unitary
quotient: their Gram equations make the quotient of the conjugating matrices
an isometry. This argument works for arbitrary Hermitian forms; the matrices
in the semilinear formulas need not themselves be unitary. If the field parts
are identity or Hermitian conjugation, every two elements outside PGU have
quotient in PGU.

These are conditional algebraic reductions. The centralizer containment and
the restriction on field parts still require Ree geometry. No index bound,
normality of the PGU image, or equality of the normalizer with M is assumed.

Source: the PGU₃(q):2 case of Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; case 7 of the unconditional list in the
proof of Theorem 5, https://arxiv.org/pdf/0910.4758, p.3.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace ProjectiveExtension
variable {G : Type*} [Group G] {S : Subgroup G}
  {F : Type*} [Field F] {J : HermitianForm 3 F}

/-- The PSU marking determined by this extension, with its exact ambient image. -/
@[expose] noncomputable def socleEquiv (E : ProjectiveExtension S J) :
    ProjectiveSpecialUnitaryMatrixGroup J ≃* S :=
  (MonoidHom.ofInjective (f := E.embedding.comp (projectiveSpecialInclusion J))
    (E.injective.comp (inclusion_injective
      (map_mono J.specialSubgroup_le_unitarySubgroup)))).trans
      (MulEquiv.subgroupCongr E.socle_range_eq)

@[simp] theorem socleEquiv_apply_val (E : ProjectiveExtension S J)
    (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    (E.socleEquiv b : G) = E.embedding (projectiveSpecialInclusion J b) := rfl

/-- Conjugation on the socle, transported through the supplied extension. -/
@[expose] noncomputable def normalizerAction (E : ProjectiveExtension S J) :
    normalizer (S : Set G) →* MulAut (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (MulAut.congr E.socleEquiv.symm).toMonoidHom.comp S.normalizerMonoidHom

@[simp] theorem normalizerAction_apply (E : ProjectiveExtension S J)
    (k : normalizer (S : Set G)) (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    E.socleEquiv (E.normalizerAction k b) =
      S.normalizerMonoidHom k (E.socleEquiv b) := by
  change E.socleEquiv (E.socleEquiv.symm
    (S.normalizerMonoidHom k (E.socleEquiv b))) = _
  exact E.socleEquiv.apply_symm_apply _

@[simp] theorem normalizerAction_apply_val (E : ProjectiveExtension S J)
    (k : normalizer (S : Set G)) (b : ProjectiveSpecialUnitaryMatrixGroup J) :
    (E.socleEquiv (E.normalizerAction k b) : G) =
      (k : G) * (E.socleEquiv b : G) * (k : G)⁻¹ := by
  rw [normalizerAction_apply]
  rfl

/-- The normalizer element furnished by an actual unitary matrix. -/
@[expose] noncomputable def unitaryElement (E : ProjectiveExtension S J) (u : J.unitarySubgroup) :
    normalizer (S : Set G) :=
  ⟨E.embedding ⟨ProjGenLinGroup.mk u.val, mem_map_of_mem _ u.property⟩,
    E.range_le_normalizer ⟨_, rfl⟩⟩

@[simp] theorem normalizerAction_unitaryElement (E : ProjectiveExtension S J)
    (u : J.unitarySubgroup) :
    E.normalizerAction (E.unitaryElement u) = J.unitaryConj u := by
  apply MulEquiv.ext
  intro b
  apply E.socleEquiv.injective
  apply Subtype.ext
  rw [normalizerAction_apply_val]
  simp only [socleEquiv_apply_val, unitaryElement]
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg E.embedding
  apply Subtype.ext
  exact (J.unitaryConj_apply_val u b).symm

/-- The field part and its compatible Gram equation are retained explicitly. -/
@[expose] def HasCompatibleSemilinearAction (E : ProjectiveExtension S J)
    (k : normalizer (S : Set G)) (σ : F ≃+* F) : Prop :=
  ∃ u : GL (Fin 3) F,
    J.conjTranspose u.val * J.form * u.val = J.form.map σ ∧
    ∀ b : ProjectiveSpecialUnitaryMatrixGroup J,
      (E.normalizerAction k b).val = ProjGenLinGroup.mk u *
        ProjGenLinGroup.map σ.toRingHom b.val * (ProjGenLinGroup.mk u)⁻¹

/-- Transporting the action changes neither its kernel nor the ambient group
in which the centralizer is computed. -/
theorem normalizerAction_ker (E : ProjectiveExtension S J) :
    E.normalizerAction.ker =
      (centralizer (S : Set G)).subgroupOf (normalizer (S : Set G)) := by
  exact (MonoidHom.ker_comp_of_injective S.normalizerMonoidHom
    (MulAut.congr E.socleEquiv.symm).toMonoidHom
    (MulAut.congr E.socleEquiv.symm).injective).trans S.normalizerMonoidHom_ker

private theorem mem_range_of_action_eq (E : ProjectiveExtension S J)
    (hC : centralizer (S : Set G) ≤ E.embedding.range)
    {x y : normalizer (S : Set G)} (hy : (y : G) ∈ E.embedding.range)
    (h : E.normalizerAction x = E.normalizerAction y) :
    (x : G) ∈ E.embedding.range := by
  have hker : x * y⁻¹ ∈ E.normalizerAction.ker := by
    change E.normalizerAction (x * y⁻¹) = 1
    simp only [map_mul, map_inv, h, mul_inv_cancel]
  rw [E.normalizerAction_ker] at hker
  have hxy : (x : G) * (y : G)⁻¹ ∈ E.embedding.range := hC hker
  simpa only [inv_mul_cancel_right] using E.embedding.range.mul_mem hxy hy

theorem mem_range_of_action_eq_unitaryConj (E : ProjectiveExtension S J)
    (hC : centralizer (S : Set G) ≤ E.embedding.range)
    (k : normalizer (S : Set G)) (u : J.unitarySubgroup)
    (h : E.normalizerAction k = J.unitaryConj u) : (k : G) ∈ E.embedding.range := by
  apply E.mem_range_of_action_eq hC (y := E.unitaryElement u) ⟨_, rfl⟩
  rw [h, E.normalizerAction_unitaryElement]

theorem HasCompatibleSemilinearAction.mem_range_of_one
    {E : ProjectiveExtension S J} {k : normalizer (S : Set G)}
    (hk : E.HasCompatibleSemilinearAction k (RingEquiv.refl F))
    (hC : centralizer (S : Set G) ≤ E.embedding.range) : (k : G) ∈ E.embedding.range := by
  obtain ⟨u, hu, ha⟩ := hk
  have hu' : u ∈ J.unitarySubgroup := by
    rw [J.mem_unitarySubgroup_iff]
    simpa only [RingEquiv.coe_refl, Matrix.map_id] using hu
  apply E.mem_range_of_action_eq_unitaryConj hC k ⟨u, hu'⟩
  apply MulEquiv.ext
  intro b
  apply Subtype.ext
  rw [ha, J.unitaryConj_apply_val]
  change _ * ProjGenLinGroup.map (RingHom.id F) b.val * _ = _
  rw [ProjGenLinGroup.map_id, MonoidHom.id_apply]

private theorem adjoint_mul (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A * B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A * B)).transpose = _
  rw [map_mul, transpose_mul]
  rfl

private theorem common_gram_mul_inv_unitary {u v : GL (Fin 3) F}
    (h : J.conjTranspose u.val * J.form * u.val =
      J.conjTranspose v.val * J.form * v.val) :
    u * v⁻¹ ∈ J.unitarySubgroup := by
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val * (v⁻¹).val) * J.form *
    (u.val * (v⁻¹).val) = _
  rw [adjoint_mul]
  calc
    J.conjTranspose (v⁻¹).val * J.conjTranspose u.val * J.form *
        (u.val * (v⁻¹).val) =
      J.conjTranspose (v⁻¹).val *
        (J.conjTranspose u.val * J.form * u.val) * (v⁻¹).val := by
          simp only [mul_assoc]
    _ = J.conjTranspose (v⁻¹).val *
        (J.conjTranspose v.val * J.form * v.val) * (v⁻¹).val := by rw [h]
    _ = (J.conjTranspose (v⁻¹).val * J.conjTranspose v.val) * J.form *
        (v.val * (v⁻¹).val) := by simp only [mul_assoc]
    _ = J.form := by
      rw [← adjoint_mul]
      have hv : v.val * (v⁻¹).val = 1 := v.val_inv
      rw [hv]
      have hone : J.conjTranspose 1 = 1 := by
        change ((J.conj : F →+* F).mapMatrix 1).transpose = _
        rw [map_one, transpose_one]
      rw [hone, one_mul, mul_one]

/-- Equal field parts cancel; the compatible Gram equations make the remaining
conjugating matrix unitary, even when the form itself is not field-fixed. -/
theorem HasCompatibleSemilinearAction.mul_inv_mem_range
    {E : ProjectiveExtension S J} {x t : normalizer (S : Set G)} {σ : F ≃+* F}
    (hx : E.HasCompatibleSemilinearAction x σ)
    (ht : E.HasCompatibleSemilinearAction t σ)
    (hC : centralizer (S : Set G) ≤ E.embedding.range) :
    (x : G) * (t : G)⁻¹ ∈ E.embedding.range := by
  obtain ⟨u, hu, ha⟩ := hx
  obtain ⟨v, hv, hb⟩ := ht
  let w : J.unitarySubgroup := ⟨u * v⁻¹, common_gram_mul_inv_unitary (hu.trans hv.symm)⟩
  have heq : E.normalizerAction x = J.unitaryConj w * E.normalizerAction t := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    change (E.normalizerAction x b).val =
      (J.unitaryConj w (E.normalizerAction t b)).val
    rw [ha, J.unitaryConj_apply_val, hb]
    change _ = ProjGenLinGroup.mk (u * v⁻¹) * _ *
      (ProjGenLinGroup.mk (u * v⁻¹))⁻¹
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv]
    simp only [mul_assoc, inv_mul_cancel_left]
  apply E.mem_range_of_action_eq_unitaryConj hC (x * t⁻¹) w
  rw [map_mul, map_inv, heq, mul_inv_cancel_right]

/-- A normalizer element with trivial field part lies in the embedded PGU;
two remaining elements have the same field part, which cancels. -/
theorem outside_coset_control (E : ProjectiveExtension S J)
    (hC : centralizer (S : Set G) ≤ E.embedding.range)
    (hAction : ∀ k : normalizer (S : Set G),
      E.HasCompatibleSemilinearAction k (RingEquiv.refl F) ∨
        E.HasCompatibleSemilinearAction k J.conj)
    (t x : normalizer (S : Set G))
    (ht : (t : G) ∉ E.embedding.range) (hx : (x : G) ∉ E.embedding.range) :
    (x : G) * (t : G)⁻¹ ∈ E.embedding.range := by
  rcases hAction t with htlin | htconj
  · exact (ht (htlin.mem_range_of_one hC)).elim
  rcases hAction x with hxlin | hxconj
  · exact (hx (hxlin.mem_range_of_one hC)).elim
  exact hxconj.mul_inv_mem_range htconj hC

end ProjectiveExtension
end ReeF4.MaximalSubgroups.SimpleNormal
