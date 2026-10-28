module
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Field.Subfield.Basic

/-!
# Additive spans of large multiplicative subgroups of finite fields

The additive span of a multiplicative subgroup of field units is closed under
multiplication and contains one. In a finite field it also contains inverses,
so it is a subfield. A proper subfield of a field with q² elements has at most
q elements. Thus a unit subgroup with at least q elements spans the full field:
its injection into the span misses zero.

This elementary argument supports the torus-weight recovery in Steinberg's
Theorem36, including prime-power fixed fields where a proper additive subgroup
need not have order at most q.
-/

public section
namespace FiniteField.MultiplicativeSpan
variable {E : Type*} [Field E] [Finite E]

/-- A proper subfield of a finite field of square order has at most its square root in size. -/
theorem proper_subfield_card_le {q : ℕ} (hcard : Nat.card E = q ^ 2)
    (K : Subfield E) (hK : K ≠ ⊤) : Nat.card K ≤ q := by
  have hdimpos : 0 < Module.finrank K E := Module.finrank_pos
  have hc := Module.natCard_eq_pow_finrank (K := K) (V := E)
  have hdim : 2 ≤ Module.finrank K E := by
    by_contra h
    have hdim1 : Module.finrank K E = 1 := by omega
    have hsame : Nat.card K = Nat.card E := by simpa only [hdim1, pow_one] using hc.symm
    have hsurj := ((Nat.bijective_iff_injective_and_card (Subtype.val : K → E)).mpr
      ⟨Subtype.val_injective, hsame⟩).surjective
    apply hK
    apply top_unique
    intro x _
    obtain ⟨y, rfl⟩ := hsurj x
    exact y.property
  have hsquare : Nat.card K ^ 2 ≤ q ^ 2 :=
    (Nat.pow_le_pow_right (Finite.one_lt_card (α := K)).le hdim).trans_eq
      (hc.symm.trans hcard)
  nlinarith

private noncomputable def unitSpanField (U : Subgroup Eˣ) : Subfield E := by
  classical
  let S := AddSubgroup.closure (Set.range (fun u : U => (u.val : E)))
  have hmul {x y : E} (hx : x ∈ S) (hy : y ∈ S) : x * y ∈ S := by
    induction hx, hy using AddSubgroup.closure_induction₂ with
    | mem x y hx hy =>
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a * b, rfl⟩
    | zero_left => simp
    | zero_right => simp
    | add_left _ _ _ _ _ _ h₁ h₂ => simpa [add_mul] using S.add_mem h₁ h₂
    | add_right _ _ _ _ _ _ h₁ h₂ => simpa [mul_add] using S.add_mem h₁ h₂
    | neg_left _ _ _ _ h => simpa [neg_mul] using S.neg_mem h
    | neg_right _ _ _ _ h => simpa [mul_neg] using S.neg_mem h
  let R : Subring E :=
    { S with
      one_mem' := AddSubgroup.subset_closure ⟨1, rfl⟩
      mul_mem' := hmul }
  apply R.toSubfield
  intro x hx
  by_cases hx0 : x = 0
  · simp [hx0]
  let := Fintype.ofFinite E
  have he : x ^ (Fintype.card E - 2) * x = 1 := by
    rw [← pow_succ, show Fintype.card E - 2 + 1 = Fintype.card E - 1 by
      have h := Fintype.one_lt_card (α := E)
      omega]
    exact FiniteField.pow_card_sub_one_eq_one x hx0
  rw [inv_eq_of_mul_eq_one_left he]
  exact R.pow_mem hx _

private theorem unitSpanField_toAddSubgroup (U : Subgroup Eˣ) :
    (unitSpanField U).toAddSubgroup =
      AddSubgroup.closure (Set.range (fun u : U => (u.val : E))) := by rfl

/-- A multiplicative subgroup with at least q elements spans a field of order q² additively. -/
theorem additive_span_eq_top_of_large_units (U : Subgroup Eˣ) {q : ℕ}
    (hcard : Nat.card E = q ^ 2) (hU : q ≤ Nat.card U) :
    AddSubgroup.closure (Set.range (fun u : U => (u.val : E))) = ⊤ := by
  classical
  let K := unitSpanField U
  have hmem (u : U) : (u.val : E) ∈ K :=
    AddSubgroup.subset_closure ⟨u, rfl⟩
  let f : U → K := fun u => ⟨u.val, hmem u⟩
  have hinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (Units.ext (congrArg Subtype.val h))
  have hns : ¬ Function.Surjective f := by
    intro h
    obtain ⟨u, hu⟩ := h 0
    exact Units.ne_zero u.val (congrArg Subtype.val hu)
  have hlt : Nat.card U < Nat.card K := by
    let := Fintype.ofFinite U
    let := Fintype.ofFinite K
    simpa only [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_injective_not_surjective f hinj hns
  have htop : K = ⊤ := by
    by_contra h
    have := proper_subfield_card_le hcard K h
    omega
  rw [← unitSpanField_toAddSubgroup, show unitSpanField U = ⊤ from htop]
  rfl

end FiniteField.MultiplicativeSpan
