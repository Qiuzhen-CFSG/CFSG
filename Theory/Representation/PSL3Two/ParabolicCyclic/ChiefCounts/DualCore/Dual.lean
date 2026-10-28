module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Natural
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# The dual-natural chief flag for the line-parabolic residual

In inverse-transpose coordinates the third coordinate axis is fixed. The
marked cubic generates its two-dimensional quotient from every nonzero
class, so the flag zero < axis < whole is chief and has one noncentral
section. The dot-product intertwiner transports this literal flag to the
contragredient representation, retaining the same embedded residual actor.

Source: Aschbacher–Smith 14.7.22(2), with the marked line parabolic of H.6.5
and the dual-natural constituent of H.5.3(1).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Matrix Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts
open AutomorphismAction
private abbrev D := (W.comp graph.toMonoidHom).comp actor.subtype
private def axis : Subrepresentation D where
  toSubmodule := (LinearMap.proj (R := ZMod 2) (ι := Fin 3) 0).ker ⊓
    (LinearMap.proj (R := ZMod 2) (ι := Fin 3) 1).ker
  apply_mem_toSubmodule g v hv := by
    obtain ⟨h20, h21⟩ := (Matrix.PSL3Two.mem_lineParabolicSL_iff g.val⁻¹).mp
      (actor_le_lineParabolic (actor.inv_mem g.property))
    change v 0 = 0 ∧ v 1 = 0 at hv
    change ((g.val⁻¹.val)ᵀ *ᵥ v) 0 = 0 ∧ ((g.val⁻¹.val)ᵀ *ᵥ v) 1 = 0
    simp only [mulVec, dotProduct, Fin.sum_univ_three, transpose_apply, hv.1, hv.2,
      h20, h21, mul_zero, zero_mul, add_zero, and_self]

private theorem axis_bot : (⊥ : Subrepresentation D) ⋖ axis := by
  apply covBy_of_eq_or_eq
  · apply lt_of_le_not_ge bot_le
    intro h
    have hh := h (show (![0, 0, 1] : Vector) ∈ axis from ⟨rfl, rfl⟩)
    have he : (![0, 0, 1] : Vector) = 0 := hh
    have := congrFun he 2
    exact one_ne_zero (show (1 : ZMod 2) = 0 from this)
  · intro U _ hU
    by_cases he : U ≤ ⊥
    · exact Or.inl (le_antisymm he bot_le)
    · right
      apply le_antisymm hU
      obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp he
      intro y hy
      have hspan : ∀ x y : Vector, x 0 = 0 → x 1 = 0 → x ≠ 0 →
          y 0 = 0 → y 1 = 0 → ∃ a : ZMod 2, y = a • x := by decide +kernel
      obtain ⟨a, rfl⟩ := hspan x y (hU hx).1 (hU hx).2 hxn hy.1 hy.2
      exact U.toSubmodule.smul_mem a hx

set_option synthInstance.maxSize 256 in
private theorem axis_cyclic : ∀ x y : Vector, ¬ (x 0 = 0 ∧ x 1 = 0) →
    ∃ a b c : ZMod 2, y = a • x + b • W (graph lineCycle) x + c • ![0, 0, 1] := by
  decide +kernel

private theorem axis_top : axis ⋖ (⊤ : Subrepresentation D) := by
  apply covBy_of_eq_or_eq
  · apply lt_of_le_not_ge le_top
    intro h
    have hh : (![1, 0, 0] : Vector) ∈ axis := h Submodule.mem_top
    exact one_ne_zero hh.1
  · intro U hU _
    by_cases he : U ≤ axis
    · exact Or.inl (le_antisymm he hU)
    · right
      apply top_unique
      obtain ⟨x, hx, hxn⟩ := SetLike.not_le_iff_exists.mp he
      intro y _
      obtain ⟨a, b, c, rfl⟩ := axis_cyclic x y hxn
      have hc := U.apply_mem_toSubmodule ⟨lineCycle, lineCycle_mem_actor⟩ hx
      exact U.toSubmodule.add_mem
        (U.toSubmodule.add_mem (U.toSubmodule.smul_mem a hx) (U.toSubmodule.smul_mem b hc))
        (U.toSubmodule.smul_mem c (hU ⟨rfl, rfl⟩))

private theorem axis_central : Central (⊥ : Subrepresentation D) axis := by
  intro g v hv
  obtain ⟨h20, h21⟩ := (Matrix.PSL3Two.mem_lineParabolicSL_iff g.val⁻¹).mp
    (actor_le_lineParabolic (actor.inv_mem g.property))
  have h22 := naturalPlane_central_top g⁻¹ (Pi.single 2 1 : Vector) Submodule.mem_top
  change (g.val⁻¹.val *ᵥ (Pi.single 2 1 : Vector)) 2 - (Pi.single 2 1 : Vector) 2 = 0 at h22
  rw [mulVec_single_one] at h22
  simp only [col_apply, Pi.single_eq_same] at h22
  have h22' : g.val⁻¹.val 2 2 = 1 := sub_eq_zero.mp h22
  change v 0 = 0 ∧ v 1 = 0 at hv
  change (g.val⁻¹.val)ᵀ *ᵥ v - v = 0
  ext i
  simp only [Pi.sub_apply, Pi.zero_apply, mulVec, dotProduct,
    Fin.sum_univ_three, transpose_apply, hv.1, hv.2, mul_zero, zero_add]
  fin_cases i
  · change g.val⁻¹.val 2 0 * v 2 - v 0 = 0
    rw [h20, hv.1, zero_mul, sub_self]
  · change g.val⁻¹.val 2 1 * v 2 - v 1 = 0
    rw [h21, hv.2, zero_mul, sub_self]
  · change g.val⁻¹.val 2 2 * v 2 - v 2 = 0
    rw [h22', one_mul, sub_self]

private theorem axis_noncentral : ¬ Central axis (⊤ : Subrepresentation D) := by
  intro h
  have hh := h ⟨lineCycle, lineCycle_mem_actor⟩ (![1, 0, 0] : Vector) Submodule.mem_top
  have hn : ((W (graph lineCycle) (![1, 0, 0] : Vector) - ![1, 0, 0]) : Vector) 1 ≠ 0 := by decide
  exact hn hh.2

private def dualSeries : Series D where
  length := 2
  toFun := ![⊥, axis, ⊤]
  step i := by
    fin_cases i
    · exact axis_bot
    · exact axis_top

/-- The dual natural module has exactly one noncentral chief section for
the literal embedded line-parabolic two-residual. -/
theorem dual_count : HasCount (W.dual.comp actor.subtype) 1 := by
  have hD : HasCount D 1 := by
    refine ⟨dualSeries, rfl, rfl, ?_⟩
    have h : dualSeries.count = ({1} : Finset (Fin 2)).card := by
      apply Series.count_eq_card
      intro i
      fin_cases i
      · change (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) ↔ ¬ Central ⊥ axis
        exact iff_of_false (by decide) (not_not_intro axis_central)
      · change (1 : Fin 2) ∈ ({1} : Finset (Fin 2)) ↔ ¬ Central axis ⊤
        exact iff_of_true (by decide) axis_noncentral
    exact h.trans (by decide)
  exact hD.mapEquiv (restrictEquiv graphNaturalDual actor.subtype)
end BinaryLinearThree.ParabolicCyclic.ChiefCounts
