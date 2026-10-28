module
public import Theory.SpecificGroups.HeisenbergFour.CubicIncidence.Coordinates
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.NormNum

/-!
# Cubic subgroups and the two axes

Every cubic subgroup is one of the sixteen conjugates of the complement.
An A₄ neighbor of the complement lies on one of the two nonzero coordinate
axes: a mixed coordinate produces an element whose sixth power is nontrivial,
whereas A₄ has exponent six. Each axis is a single complement orbit.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.6(1), p.264.
-/

@[expose] public section
namespace HeisenbergFour.CubicIncidence
open Subgroup

abbrev origin : Four × Four := (0, 0)

theorem gen_origin : gen origin = base := by decide +kernel

theorem gen_order (i : Four × Four) : orderOf (gen i) = 3 := by
  change orderOf (MulAut.conj (shift i) base) = 3
  rw [MulEquiv.orderOf_eq]
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem card_C (i : Four × Four) : Nat.card (C i) = 3 := by
  rw [C, Nat.card_zpowers, gen_order]

private theorem cubic_elements : ∀ x : CoordinateModel, x ^ 3 = 1 → x ≠ 1 →
    ∃ i : Four × Four, x = gen i ∨ x = (gen i)⁻¹ := by decide +kernel

/-- Completeness is established on elements, without enumerating subgroup sets. -/
theorem cubic_representative (P : Subgroup CoordinateModel) (hP : Nat.card P = 3) :
    ∃ i : Four × Four, P = C i := by
  have hcyc : IsCyclic P := isCyclic_of_prime_card hP
  obtain ⟨x, hx⟩ := P.isCyclic_iff_exists_zpowers_eq_top.mp hcyc
  have ho : orderOf x = 3 := by rw [← Nat.card_zpowers, hx, hP]
  obtain ⟨i, hi | hi⟩ := cubic_elements x
    (orderOf_eq_prime_iff.mp ho).1 (orderOf_eq_prime_iff.mp ho).2
  · exact ⟨i, hx.symm.trans (congrArg zpowers hi)⟩
  · exact ⟨i, by rw [← hx, hi, zpowers_inv]; rfl⟩

/-- A concrete conjugator moves each cubic to the distinguished complement. -/
theorem map_C_to_origin (i : Four × Four) :
    (C i).map (MulAut.conj (shift i)⁻¹).toMonoidHom = C origin := by
  rw [C, MonoidHom.map_zpowers]
  change zpowers ((shift i)⁻¹ * gen i * ((shift i)⁻¹)⁻¹) = C origin
  rw [gen, inv_inv]
  have h : (shift i)⁻¹ * (shift i * base * (shift i)⁻¹) * shift i = base := by group
  rw [h]
  exact congrArg zpowers gen_origin.symm

/-- The six possible neighbors are the two punctured coordinate axes. -/
def Axis (i : Four × Four) : Prop :=
  (i.1 ≠ 0 ∧ i.2 = 0) ∨ (i.1 = 0 ∧ i.2 ≠ 0)
instance (i : Four × Four) : Decidable (Axis i) := by unfold Axis; infer_instance

/-- An ordered pair lies on opposite axes. -/
def Cross (i j : Four × Four) : Prop :=
  (i.1 ≠ 0 ∧ i.2 = 0 ∧ j.1 = 0 ∧ j.2 ≠ 0) ∨
    (i.1 = 0 ∧ i.2 ≠ 0 ∧ j.1 ≠ 0 ∧ j.2 = 0)
instance (i j : Four × Four) : Decidable (Cross i j) := by unfold Cross; infer_instance

private theorem mixed_sixth : ∀ i : Four × Four,
    (base * (gen i)⁻¹) ^ 6 = 1 → i.1 = 0 ∨ i.2 = 0 := by decide +kernel

private theorem alternating_sixth : ∀ x : alternatingGroup (Fin 4), x ^ 6 = 1 := by
  decide +kernel

theorem axis_of_alternating (i : Four × Four)
    (e : ↥(C origin ⊔ C i) ≃* alternatingGroup (Fin 4)) : Axis i := by
  have hbase : base ∈ C origin ⊔ C i := by
    rw [← gen_origin]
    exact (show C origin ≤ C origin ⊔ C i from le_sup_left) (mem_zpowers _)
  have hgen : gen i ∈ C origin ⊔ C i  := (show C i ≤ C origin ⊔ C i from le_sup_right) (mem_zpowers _)
  have hp : (base * (gen i)⁻¹) ^ 6 = 1 := by
    let x : ↥(C origin ⊔ C i) := ⟨base * (gen i)⁻¹, mul_mem hbase (inv_mem hgen)⟩
    have hx : x ^ 6 = 1 := e.injective (by simpa only [map_pow, map_one] using alternating_sixth (e x))
    exact congrArg Subtype.val hx
  have hi : i ≠ origin := by
    intro he
    have hc := Nat.card_congr e.toEquiv
    rw [he, sup_idem, card_C, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
  rcases mixed_sixth i hp with ha | hb
  · exact Or.inr ⟨ha, fun hb => hi (Prod.ext ha hb)⟩
  · exact Or.inl ⟨fun ha => hi (Prod.ext ha hb), hb⟩

/-- The same-axis conjugating elements are literal powers of the complement. -/
theorem same_axis_conjugator (i j : Four × Four) (hi : Axis i) (hj : Axis j)
    (hc : ¬ Cross i j) :
    ∃ n : Fin 3, base ^ n.val * gen i * (base ^ n.val)⁻¹ = gen j := by
  have h : ∀ i j : Four × Four, Axis i → Axis j → ¬ Cross i j →
      ∃ n : Fin 3, base ^ n.val * gen i * (base ^ n.val)⁻¹ = gen j := by
    decide +kernel
  exact h i j hi hj hc

end HeisenbergFour.CubicIncidence
