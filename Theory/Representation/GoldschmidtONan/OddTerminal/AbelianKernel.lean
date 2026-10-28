module

public import Theory.Representation.GoldschmidtONan.Basic

/-!
# The abelian kernel in the odd Goldschmidt–O'Nan argument

Suppose the fixed space is a line and the whole group is transitive on
nonzero vectors. Every nontrivial abelian normal subgroup R meets Y trivially:
an element of their intersection would force R to fix that line pointwise,
contradicting normality, transitivity, and faithfulness. A member of R fixing
the line then centralizes Y. Commuting with R provides a second fixed vector,
and transitivity of Y on the moved space forces that member to be the identity.
Thus every nonidentity member of Y acts fixed-point freely on R.

This reconstructs the Frobenius-kernel assertion at the end of GLS, Number 2,
Chapter C, Proposition 14.2 (`refs/KGroup/GLS2/ChapterC.tex`, final paragraph).
Minimality or elementary abelian structure of R is not needed. Its existence
and the fixed-line assertion remain explicit hypotheses.
-/

public section

open scoped IsMulCommutative
open Representation Representation.BinaryOffender Representation.RegularCyclicNormalClosure
namespace Representation.GoldschmidtONan
variable {X V : Type*} [Group X] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) X V} {Y : Subgroup X}

private theorem line_eq_zero_or_eq [Finite V]
    (W : Submodule (ZMod 2) V) (hd : Module.finrank (ZMod 2) W = 1)
    {v : V} (hv : v ∈ W) (hv0 : v ≠ 0) {w : V} (hw : w ∈ W) : w = 0 ∨ w = v := by
  obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hd
    (x := (⟨v, hv⟩ : W)) (by intro he; exact hv0 (congrArg Subtype.val he)) (⟨w, hw⟩ : W)
  have he := congrArg Subtype.val hc
  change c • v = w at he
  fin_cases c
  · change (0 : ZMod 2) • v = w at he
    rw [zero_smul] at he
    exact Or.inl he.symm
  · change (1 : ZMod 2) • v = w at he
    rw [one_smul] at he
    exact Or.inr he.symm

private theorem normal_eq_bot_of_fixed_nonzero
    (hf : Function.Injective ρ) (ht : NonzeroTransitive ρ)
    (R : Subgroup X) [R.Normal] {v : V} (hv : v ≠ 0)
    (hfix : ∀ r : R, ρ r v = v) : R = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro r hr
  apply Subgroup.mem_bot.mpr
  apply hf
  ext w
  by_cases hw : w = 0
  · simp [hw]
  obtain ⟨x, rfl⟩ := ht v hv w hw
  have hc : x⁻¹ * r * x ∈ R := by
    simpa using (inferInstance : R.Normal).conj_mem r hr x⁻¹
  have he := congrArg (ρ x) (hfix ⟨x⁻¹ * r * x, hc⟩)
  simpa only [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel,
    one_mul, map_one, Module.End.one_apply] using he

private theorem Input.mem_fixed_of_fixed_nontrivial [Finite X]
    (h : Input ρ Y) {y : Y} (hy : y ≠ 1) {v : V} (hv : ρ y v = v) :
    v ∈ fixedSpace ρ Y := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ fixedSpace ρ Y ⊔ displacementSpan ρ Y ⊤ by rw [h.split.sup_eq_top]; trivial)
  rw [map_add, show ρ y a = a from ha y, add_right_inj] at hv
  have hb0 := h.eq_zero_of_mem_moved_of_fixed hy hb hv
  simpa only [hb0, add_zero] using ha

private theorem Input.fix_line_of_commute [Finite X] [Finite V]
    (h : Input ρ Y) (hd : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    {v : V} (hv : v ∈ fixedSpace ρ Y) (hv0 : v ≠ 0)
    {y : Y} (hy : y ≠ 1) {r : X} (hc : r * y = y * r) : ρ r v = v := by
  have hm : ρ r v ∈ fixedSpace ρ Y := by
    apply h.mem_fixed_of_fixed_nontrivial hy
    rw [← Module.End.mul_apply, ← map_mul, ← hc, map_mul, Module.End.mul_apply,
      show ρ y v = v from hv y]
  rcases line_eq_zero_or_eq _ hd hv hv0 hm with he | he
  · exact False.elim (hv0 (action_injective r (by simpa using he)))
  · exact he

private theorem Input.normal_abelian_inf_actor_eq_bot [Finite X] [Finite V]
    (h : Input ρ Y) (ht : NonzeroTransitive ρ)
    (hd : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    (R : Subgroup X) [R.Normal] [IsMulCommutative R] (hR : R ≠ ⊥) : R ⊓ Y = ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixed_nontrivial
  apply le_antisymm ?_ bot_le
  intro y hy
  apply Subgroup.mem_bot.mpr
  by_contra hy1
  apply hR
  apply normal_eq_bot_of_fixed_nonzero h.faithful ht R hv0
  intro r
  apply h.fix_line_of_commute hd hv hv0 (y := ⟨y, hy.2⟩)
    (by intro he; exact hy1 (congrArg Subtype.val he))
  exact congrArg Subtype.val (mul_comm r (⟨y, hy.1⟩ : R))

private theorem Input.commutes_actor_of_normal_abelian_fixed [Finite X] [Finite V]
    (h : Input ρ Y) (ht : NonzeroTransitive ρ)
    (hd : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    (R : Subgroup X) [R.Normal] [IsMulCommutative R] (hR : R ≠ ⊥)
    {v : V} (hv : v ∈ fixedSpace ρ Y) (hv0 : v ≠ 0) (r : R) (hr : ρ r v = v) :
    ∀ y : Y, (r : X) * y = (y : X) * r := by
  have hpoint (w : V) (hw : w ∈ fixedSpace ρ Y) : ρ r w = w := by
    rcases line_eq_zero_or_eq _ hd hv hv0 hw with rfl | rfl
    · exact map_zero _
    · exact hr
  have hmap : (fixedSpace ρ Y).map (ρ r) = fixedSpace ρ Y := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      rw [hpoint w hw]
      exact hw
    · intro w hw
      exact ⟨w, hw, hpoint w hw⟩
  have hnorm := h.normal_in_stabilizer r hmap
  have hinter := h.normal_abelian_inf_actor_eq_bot ht hd R hR
  intro y
  have hconj : (r : X) * y * (r : X)⁻¹ ∈ Y := by
    have hm : (r : X) * y * (r : X)⁻¹ ∈ Y.map (MulAut.conj (r : X)).toMonoidHom :=
      ⟨y, y.property, rfl⟩
    exact hnorm.le hm
  have hcomm : (r : X) * y * (r : X)⁻¹ * (y : X)⁻¹ ∈ R ⊓ Y := by
    constructor
    · change (r : X) * y * (r : X)⁻¹ * (y : X)⁻¹ ∈ R
      have hc := (inferInstance : R.Normal).conj_mem (r : X)⁻¹ (R.inv_mem r.property) y
      simpa only [mul_assoc] using R.mul_mem r.property hc
    · exact Y.mul_mem hconj (Y.inv_mem y.property)
  rw [hinter, Subgroup.mem_bot] at hcomm
  have he := mul_inv_eq_one.mp hcomm
  exact mul_inv_eq_iff_eq_mul.mp he

/-- A nontrivial abelian normal subgroup has trivial stabilizers on the fixed line. -/
theorem Input.normal_abelian_fixed_eq_one [Finite X] [Finite V]
    (h : Input ρ Y) (ht : NonzeroTransitive ρ)
    (hd : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    (R : Subgroup X) [R.Normal] [IsMulCommutative R] (hR : R ≠ ⊥)
    {v : V} (hv : v ∈ fixedSpace ρ Y) (hv0 : v ≠ 0) (r : R) (hr : ρ r v = v) : r = 1 := by
  have hc := h.commutes_actor_of_normal_abelian_fixed ht hd R hR hv hv0 r hr
  have hfixF (a : V) (ha : a ∈ fixedSpace ρ Y) : ρ r a = a := by
    rcases line_eq_zero_or_eq _ hd hv hv0 ha with rfl | rfl
    · exact map_zero _
    · exact hr
  obtain ⟨s, hs⟩ : ∃ s : R, ρ s v ≠ v := by
    by_contra! hn
    exact hR (normal_eq_bot_of_fixed_nonzero h.faithful ht R hv0 hn)
  have hw0 : ρ s v ≠ 0 := fun he => hv0 (action_injective (ρ := ρ) (s : X) (by simpa using he))
  have hwF : ρ s v ∉ fixedSpace ρ Y := by
    intro hm
    exact (line_eq_zero_or_eq _ hd hv hv0 hm).elim hw0 hs
  have hrw : ρ r (ρ s v) = ρ s v := by
    have hcomm : (r : X) * s = (s : X) * r := congrArg Subtype.val (mul_comm r s)
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hr]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
    (show ρ s v ∈ fixedSpace ρ Y ⊔ displacementSpan ρ Y ⊤ by rw [h.split.sup_eq_top]; trivial)
  have hb0 : b ≠ 0 := by
    intro he
    apply hwF
    rw [he, add_zero] at hab
    exact hab ▸ ha
  have hrb : ρ r b = b := by
    rw [← hab, map_add, hfixF a ha, add_right_inj] at hrw
    exact hrw
  have hfixD (w : V) (hw : w ∈ displacementSpan ρ Y ⊤) : ρ r w = w := by
    by_cases hw0 : w = 0
    · simp [hw0]
    obtain ⟨y, rfl⟩ := h.transitive b hb hb0 w hw hw0
    rw [← Module.End.mul_apply, ← map_mul, hc y, map_mul, Module.End.mul_apply, hrb]
  apply Subtype.ext
  apply h.faithful
  change ρ (r : X) = ρ (1 : X)
  ext w
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp
    (show w ∈ fixedSpace ρ Y ⊔ displacementSpan ρ Y ⊤ by rw [h.split.sup_eq_top]; trivial)
  simp only [map_add, hfixF a ha, hfixD b hb, map_one, Module.End.one_apply]

/-- Conjugation by every nonidentity member of Y is fixed-point free on R. -/
theorem Input.fixedPointFree_on_normal_abelian [Finite X] [Finite V]
    (h : Input ρ Y) (ht : NonzeroTransitive ρ)
    (hd : Module.finrank (ZMod 2) (fixedSpace ρ Y) = 1)
    (R : Subgroup X) [R.Normal] [IsMulCommutative R] (hR : R ≠ ⊥) :
    ∀ y : Y, y ≠ 1 → ∀ r : R, (y : X) * r * (y : X)⁻¹ = r → r = 1 := by
  intro y hy r hr
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h.fixed_nontrivial
  apply h.normal_abelian_fixed_eq_one ht hd R hR hv hv0 r
  apply h.fix_line_of_commute hd hv hv0 hy
  exact (mul_inv_eq_iff_eq_mul.mp hr).symm

end Representation.GoldschmidtONan
