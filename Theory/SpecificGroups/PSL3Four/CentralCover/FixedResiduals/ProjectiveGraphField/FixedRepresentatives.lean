module

public import Theory.SpecificGroups.PSL3Four.CentralCover.GraphField
public import Theory.GroupAction.CentralKernelFixedResidual

/-!
# Unitary representatives of the projective graph-field fixed subgroup

Inverse transpose followed by entrywise squaring fixes the scalar center of
SL₃(4). A projective fixed representative has central displacement k; the
involution identity gives k² = 1, while determinant one gives k³ = 1. Hence
k = 1: every representative is fixed. Restricting projectivization therefore
identifies the projective fixed group with the scalar quotient of the actual
unitary matrices, without an assumed fixed-group order or recognition theorem.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript, proof of 15.3.38,
printed pp.1136--1137. This supplies the matrix comparison for its E₉ residual
calculation; the residual structure is a separate assertion.
-/

public section
namespace Matrix.PSL3Four.ProjectiveGraphField
noncomputable section

@[expose] def slAction : MulAut SL := PSL3.OuterSolvable.graphSL F * slFrobenius
abbrev projectiveAction : MulAut PSL := PSL3.OuterSolvable.graph F * pslFrobenius
abbrev unitary : Subgroup SL := slAction.fixedSubgroup

@[simp] theorem slAction_apply (g : SL) :
    slAction g = (SpecialLinearGroup.transpose (slFrobenius g))⁻¹ := rfl

@[simp] theorem projectiveAction_mk (g : SL) :
    projectiveAction (g : PSL) = (slAction g : PSL) := rfl

private theorem frobenius_transpose (g : SL) :
    slFrobenius (SpecialLinearGroup.transpose g) =
      SpecialLinearGroup.transpose (slFrobenius g) := by
  ext i j
  rfl

@[simp] theorem slAction_involutive (g : SL) : slAction (slAction g) = g := by
  simp only [slAction_apply, map_inv, frobenius_transpose, slFrobenius_involutive, inv_inv]
  apply Subtype.ext
  exact Matrix.transpose_transpose _

/-- The fixed condition is the usual identity-Gram Hermitian matrix equation. -/
theorem mem_unitary_iff (g : SL) : g ∈ unitary ↔
    (g.val.map fun x => x ^ 2).transpose * g.val = 1 := by
  have he : (slFrobenius g).val = g.val.map (fun x => x ^ 2) := by
    ext i j
    exact slFrobenius_apply g i j
  rw [MulAut.mem_fixedSubgroup, slAction_apply]
  constructor
  · intro h
    have hh : SpecialLinearGroup.transpose (slFrobenius g) * g = 1 := by
      calc
        _ = SpecialLinearGroup.transpose (slFrobenius g) *
            (SpecialLinearGroup.transpose (slFrobenius g))⁻¹ :=
          congrArg (fun z => SpecialLinearGroup.transpose (slFrobenius g) * z) h.symm
        _ = 1 := mul_inv_cancel _
    have hm := congrArg Subtype.val hh
    change (slFrobenius g).val.transpose * g.val = 1 at hm
    rwa [he] at hm
  · intro h
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    change (slFrobenius g).val.transpose * g.val = 1
    rwa [he]

theorem central_cube (g : SL) (hg : g ∈ Subgroup.center SL) : g ^ 3 = 1 := by
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  apply Subtype.ext
  change g.val ^ 3 = (1 : Matrix (Fin 3) (Fin 3) F)
  rw [← he]
  change (Matrix.diagonal (fun _ : Fin 3 => r)) ^ 3 = _
  simp only [Matrix.diagonal_pow]
  congr 1
  funext i
  exact hr

theorem central_fixed (g : SL) (hg : g ∈ Subgroup.center SL) : slAction g = g := by
  obtain ⟨r, hr, he⟩ := SpecialLinearGroup.mem_center_iff.mp hg
  have hT : SpecialLinearGroup.transpose (slFrobenius g) = g ^ 2 := by
    apply SpecialLinearGroup.ext
    intro i j
    change (g.val j i) ^ 2 = (g.val ^ 2) i j
    rw [← he]
    simp [Matrix.scalar, Matrix.diagonal_apply, Matrix.diagonal_pow, eq_comm]
  rw [slAction_apply, hT]
  have hc := central_cube g hg
  have h : g ^ 2 * g = 1 := by simpa only [← pow_succ] using hc
  exact inv_eq_of_mul_eq_one_right h

/-- Every representative of a fixed projective class is already unitary. -/
theorem fixed_mk_iff (g : SL) : projectiveAction (g : PSL) = (g : PSL) ↔ slAction g = g := by
  constructor
  · intro hg
    let k := g⁻¹ * slAction g
    have hk : k ∈ Subgroup.center SL := by
      apply (QuotientGroup.eq_one_iff k).mp
      change (QuotientGroup.mk' (Subgroup.center SL)) (g⁻¹ * slAction g) = 1
      rw [map_mul, map_inv]
      change (g : PSL)⁻¹ * projectiveAction (g : PSL) = 1
      rw [hg, inv_mul_cancel]
    have hki : slAction k = k⁻¹ := by
      dsimp only [k]
      rw [map_mul, map_inv, slAction_involutive, _root_.mul_inv_rev, inv_inv]
    have hk2 : k ^ 2 = 1 := by
      calc
        k ^ 2 = slAction k * k := by rw [central_fixed k hk, pow_two]
        _ = 1 := by rw [hki, inv_mul_cancel]
    have hk1 : k = 1 := by
      have hc := central_cube k hk
      rwa [pow_succ, hk2, one_mul] at hc
    exact ((inv_mul_eq_one.mp hk1) : g = slAction g).symm
  · intro hg
    rw [projectiveAction_mk, hg]

@[expose] def fixedProjection : unitary →* projectiveAction.fixedSubgroup :=
  MulAut.fixedSubgroupMap slAction projectiveAction
    (QuotientGroup.mk' (Subgroup.center SL)) (fun g => (projectiveAction_mk g).symm)

theorem fixedProjection_surjective : Function.Surjective fixedProjection := by
  intro x
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.center SL) x.val
  refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
  rw [MulAut.mem_fixedSubgroup]
  apply (fixed_mk_iff g).mp
  rw [← QuotientGroup.mk'_apply, hg]
  exact (MulAut.mem_fixedSubgroup _ _).mp x.property

theorem mem_fixedProjection_ker (g : unitary) :
    g ∈ fixedProjection.ker ↔ g.val ∈ Subgroup.center SL := by
  change fixedProjection g = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff g.val

/-- The fixed projective group is the central quotient of the actual unitary matrices. -/
noncomputable def quotientEquiv : (unitary ⧸ fixedProjection.ker) ≃*
    projectiveAction.fixedSubgroup :=
  QuotientGroup.quotientKerEquivOfSurjective fixedProjection fixedProjection_surjective

end
end Matrix.PSL3Four.ProjectiveGraphField
