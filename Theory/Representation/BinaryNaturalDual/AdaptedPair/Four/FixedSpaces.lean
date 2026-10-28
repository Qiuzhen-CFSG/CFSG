module
public import Theory.Representation.BinaryNaturalDual.AdaptedPair.Four.Action

/-!
# The two fixed-line calculations for the adapted four-dimensional pair

Three elementary transvections force the standard fixed space into the sum
of the first natural and last dual coordinate lines; the reversal-twisted
graph actor makes their coefficients equal. In the moving module of the
nonsingular pair, two elementary transvections and I + E₂₄ + E₃₄ give the
same constraints, and the specified outer point stabilizer joins the lines.
Finally I + (e₂ + e₃)e₁* fixes the nonsingular pair and moves its fixed line.
These calculations require only the specified actual coordinate action.

Source: Aschbacher–Smith, H.9.1(4), printed p.390, corrected adapted-pair
contract; the fixed line is used in 12.1.1 and 12.1.3.
-/

@[expose] public section

open BinaryNaturalDual BinaryLinear.OuterCyclic
namespace BinaryNaturalDual.AdaptedPair.Four

private theorem mem_fixedLine_of_coordinates (v : CoordinateSpace 4)
    (hx1 : v.1 1 = 0) (hx2 : v.1 2 = 0) (hx3 : v.1 3 = 0)
    (hf0 : v.2 (axis 0) = 0) (hf1 : v.2 (axis 1) = 0) (hf2 : v.2 (axis 2) = 0)
    (he : v.2 (axis 3) = v.1 0) :
    v ∈ Submodule.span (ZMod 2) {fixedVector 4} := by
  apply Submodule.mem_span_singleton.mpr
  refine ⟨v.1 0, ?_⟩
  apply Prod.ext
  · ext i
    fin_cases i <;> simp [fixedVector, axis, hx1, hx2, hx3]
  · apply dual_ext
    intro i
    simp only [axis] at hf0 hf1 hf2 he
    fin_cases i <;> simp [fixedVector, axis, hf0, hf1, hf2, he]

/-- The standard automorphism subgroup fixes exactly the diagonal line. -/
theorem fixedVectors_standard (d : CoordinateAction 4) :
    fixedVectors (linearAction d) (standardGroup 4) =
      Submodule.span (ZMod 2) {fixedVector 4} := by
  apply le_antisymm
  · intro v hv
    have h01 := (elementary_fixes_iff d 0 1 (by decide) v).mp
      (hv _ (inner_mem_standard (elementary_mem_upperGroup 0 1 (by decide))))
    have h12 := (elementary_fixes_iff d 1 2 (by decide) v).mp
      (hv _ (inner_mem_standard (elementary_mem_upperGroup 1 2 (by decide))))
    have h23 := (elementary_fixes_iff d 2 3 (by decide) v).mp
      (hv _ (inner_mem_standard (elementary_mem_upperGroup 2 3 (by decide))))
    have he := congrArg (fun w : CoordinateSpace 4 => w.1 0) (hv _ (tau_mem_standard 4))
    rw [linearAction_tau_fst] at he
    exact mem_fixedLine_of_coordinates v h01.1 h12.1 h23.1 h01.2 h12.2 h23.2 he
  · exact Submodule.span_le.mpr (by
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst v
      exact fixedVector_mem_fixedVectors_standard d)

/-- The simultaneous transvection I + E₂₄ + E₃₄ centralizes the adapted pair. -/
def pairedTransvection : LinearGroup 4 :=
  BinaryLinear.transvection (axis 1 + axis 2) (coordinateForm 3) (by simp [axis])

theorem pairedTransvection_eq :
    pairedTransvection = elementary (1 : Fin 4) 3 (by decide) *
      elementary (2 : Fin 4) 3 (by decide) := by
  apply LinearEquiv.ext
  intro x
  rw [LinearEquiv.mul_apply, elementary_apply, elementary_apply]
  change x + x 3 • (axis 1 + axis 2) = _
  have hz : (x + x 3 • axis (2 : Fin 4)) 3 = x 3 := by simp [axis]
  rw [hz, smul_add]
  abel

theorem pairedTransvection_mem_upperGroup : pairedTransvection ∈ upperGroup 4 := by
  rw [pairedTransvection_eq]
  exact (upperGroup 4).mul_mem (elementary_mem_upperGroup _ _ _)
    (elementary_mem_upperGroup _ _ _)

theorem pairedTransvection_fixes_vectorFour (d : CoordinateAction 4) :
    linearAction d (MulAut.conj pairedTransvection) vectorFour = vectorFour := by
  rw [linearAction_inner]
  apply Prod.ext
  · rw [BinaryLinear.NaturalDualFlag.action_fst]
    change axis (2 : Fin 4) + axis (2 : Fin 4) 3 • (axis 1 + axis 2) = axis 2
    simp [axis]
  · apply LinearMap.ext
    intro x
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    change vectorFour.2 (x + x 3 • (axis 1 + axis 2)) = vectorFour.2 x
    simp [vectorFour, axis]
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

theorem pairedTransvection_fixed_form (d : CoordinateAction 4) (v : CoordinateSpace 4)
    (hv : linearAction d (MulAut.conj pairedTransvection) v = v) :
    v.2 (axis 1) + v.2 (axis 2) = 0 := by
  have he := congrArg (fun w : CoordinateSpace 4 => w.2 (axis 3)) hv
  rw [linearAction_inner, BinaryLinear.NaturalDualFlag.action_snd] at he
  change v.2 (axis 3 + axis (3 : Fin 4) 3 • (axis 1 + axis 2)) = v.2 (axis 3) at he
  simpa only [axis, Pi.single_eq_same, one_smul, map_add, add_eq_left] using he

/-- In the moving module, the point stabilizer inside the standard group
has the same fixed line as the whole standard group. -/
theorem moving_fixedVectors_intersection (d : CoordinateAction 4) :
    movingSpace vectorFour ⊓ fixedVectors (linearAction d)
      (standardGroup 4 ⊓ pointStabilizer (linearAction d) vectorFour) =
        Submodule.span (ZMod 2) {fixedVector 4} := by
  apply le_antisymm
  · rintro v ⟨hvW, hvP⟩
    have hvW' := mem_movingSpace vectorFour v |>.mp hvW
    have hx12 : v.1 1 + v.1 2 = 0 := hvW'.1
    have hf2 : v.2 (axis 2) = 0 := hvW'.2
    have h01m : MulAut.conj (elementary (0 : Fin 4) 1 (by decide)) ∈
        standardGroup 4 ⊓ pointStabilizer (linearAction d) vectorFour := by
      refine ⟨inner_mem_standard (elementary_mem_upperGroup _ _ _), ?_⟩
      apply (elementary_fixes_iff d 0 1 (by decide) vectorFour).mpr
      simp [vectorFour, axis]
    have h03m : MulAut.conj (elementary (0 : Fin 4) 3 (by decide)) ∈
        standardGroup 4 ⊓ pointStabilizer (linearAction d) vectorFour := by
      refine ⟨inner_mem_standard (elementary_mem_upperGroup _ _ _), ?_⟩
      apply (elementary_fixes_iff d 0 3 (by decide) vectorFour).mpr
      simp [vectorFour, axis]
    have h01 := (elementary_fixes_iff d 0 1 (by decide) v).mp (hvP _ h01m)
    have h03 := (elementary_fixes_iff d 0 3 (by decide) v).mp (hvP _ h03m)
    have hb := pairedTransvection_fixed_form d v (hvP _
      ⟨inner_mem_standard pairedTransvection_mem_upperGroup,
        pairedTransvection_fixes_vectorFour d⟩)
    have hf1 : v.2 (axis 1) = 0 := by simpa only [hf2, add_zero] using hb
    have hx2 : v.1 2 = 0 := by simpa only [h01.1, zero_add] using hx12
    have ho := congrArg (fun w : CoordinateSpace 4 => w.1 0)
      (hvP _ ⟨outerFour_mem_standard, outerFour_fixes_vectorFour d⟩)
    rw [outerFour_fst] at ho
    have he : v.2 (axis 3) = v.1 0 := by simpa [axis] using ho
    exact mem_fixedLine_of_coordinates v h01.1 hx2 h03.1 h01.2 hf1 hf2 he
  · apply Submodule.span_le.mpr
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst v
    exact ⟨fixedVector_mem_movingSpace_four, fun g hg =>
      fixedVector_mem_fixedVectors_standard d g hg.1⟩

/-- A specific inner point stabilizer element moving the standard fixed line. -/
def movingTransvection : LinearGroup 4 :=
  BinaryLinear.transvection (axis 1 + axis 2) (coordinateForm 0) (by simp [axis])

theorem movingTransvection_fixes_vectorFour (d : CoordinateAction 4) :
    linearAction d (MulAut.conj movingTransvection) vectorFour = vectorFour := by
  rw [linearAction_inner]
  apply Prod.ext
  · rw [BinaryLinear.NaturalDualFlag.action_fst]
    change axis (2 : Fin 4) + axis (2 : Fin 4) 0 • (axis 1 + axis 2) = axis 2
    simp [axis]
  · apply LinearMap.ext
    intro x
    rw [BinaryLinear.NaturalDualFlag.action_snd]
    change vectorFour.2 (x + x 0 • (axis 1 + axis 2)) = vectorFour.2 x
    simp [vectorFour, axis]
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

theorem movingTransvection_moves_fixedVector (d : CoordinateAction 4) :
    linearAction d (MulAut.conj movingTransvection) (fixedVector 4) ≠ fixedVector 4 := by
  intro he
  have hh := congrArg (fun w : CoordinateSpace 4 => w.1 1) he
  rw [linearAction_inner, BinaryLinear.NaturalDualFlag.action_fst] at hh
  change axis (0 : Fin 4) 1 + axis (0 : Fin 4) 0 *
    (axis (1 : Fin 4) 1 + axis (2 : Fin 4) 1) = axis (0 : Fin 4) 1 at hh
  simp [axis] at hh

theorem inner_stabilizer_moves_fixedVector (d : CoordinateAction 4) :
    ∃ a ∈ innerGroup 4, linearAction d a vectorFour = vectorFour ∧
      ∃ z ∈ fixedVectors (linearAction d) (standardGroup 4), linearAction d a z ≠ z := by
  exact ⟨MulAut.conj movingTransvection, ⟨movingTransvection, rfl⟩,
    movingTransvection_fixes_vectorFour d, fixedVector 4,
    fixedVector_mem_fixedVectors_standard d, movingTransvection_moves_fixedVector d⟩

end BinaryNaturalDual.AdaptedPair.Four
