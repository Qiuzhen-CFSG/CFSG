module
public import Theory.SpecificGroups.PSL2.BorelCoprimeFieldAction
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Automorphism overgroups of the actual PSL₂(8)

The field automorphism quotient has prime order three. Consequently every
subgroup of Aut(PSL₂(8)) containing the inner group is either the inner
group or the full automorphism group. The field-projection kernel retains
its actual inner subgroup, and a surjective action image realizes every
specified coefficient automorphism.

Source: GLS3 2.5.12 and Aschbacher--Smith 14.2.18, printed p.987.
The arbitrary triality-centralizer application is in
`EightLargeParabolic/FieldAction.lean`.
-/

public noncomputable section
open Subgroup
namespace Theory.PSL2

/-- There is no proper intermediate automorphism overgroup at field size eight. -/
theorem eight_automorphism_overgroup (E : Subgroup (MulAut (BinaryGroup 3)))
    (hE : inner (BinaryField 3) ≤ E) : E = inner (BinaryField 3) ∨ E = ⊤ := by
  let q := QuotientGroup.mk' (inner (BinaryField 3))
  let : Fact (Nat.card (MulAut (BinaryGroup 3) ⧸ inner (BinaryField 3))).Prime :=
    ⟨by change (Nat.card (MulAut.Outer (BinaryGroup 3))).Prime
        rw [psl_eight_outer_card]; decide⟩
  have he : (E.map q).comap q = E := by
    rw [comap_map_eq]
    exact sup_eq_left.mpr (by simpa only [q,QuotientGroup.ker_mk'] using hE)
  rcases (E.map q).eq_bot_or_eq_top_of_prime_card with h | h
  · left
    rw [h] at he
    exact he.symm.trans (QuotientGroup.ker_mk' _)
  · right
    rw [h,comap_top] at he
    exact he.symm

/-- The inner group is the original centerless matrix group. -/
def eightInnerEquiv : inner (BinaryField 3) ≃* BinaryGroup 3 :=
  (MonoidHom.ofInjective (Theory.GroupTheory.conj_injective_of_center_eq_bot
    (Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot (F := BinaryField 3)))).symm

/-- Every action containing the inner automorphisms has one of the two genuine
quotient models, using its actual action kernel. -/
theorem eight_action_quotient {D : Type*} [_root_.Group D]
    (a : D →* MulAut (BinaryGroup 3)) (hi : inner (BinaryField 3) ≤ a.range) :
    Nonempty ((D ⧸ a.ker) ≃* BinaryGroup 3) ∨
      Nonempty ((D ⧸ a.ker) ≃* MulAut (BinaryGroup 3)) := by
  rcases eight_automorphism_overgroup a.range hi with h | h
  · exact Or.inl ⟨(QuotientGroup.quotientKerEquivRange a).trans
      ((MulEquiv.subgroupCongr h).trans eightInnerEquiv)⟩
  · exact Or.inr ⟨(QuotientGroup.quotientKerEquivRange a).trans
      ((MulEquiv.subgroupCongr h).trans topEquiv)⟩

/-- A nontrivial field image realizes each pure coefficient automorphism.
The lift need not have the same order until the action kernel is controlled. -/
theorem eight_action_field_lift {D : Type*} [_root_.Group D]
    (a : D →* MulAut (BinaryGroup 3)) (hi : inner (BinaryField 3) ≤ a.range)
    (hn : ((fieldProjection (BinaryField 3)).comp a).range ≠ ⊥)
    (σ : BinaryField 3 ≃+* BinaryField 3) : ∃ x : D, a x = fieldAut σ := by
  rcases eight_automorphism_overgroup a.range hi with h | h
  · exfalso
    apply hn
    apply bot_unique
    rintro _ ⟨x,rfl⟩
    have hx : a x ∈ inner (BinaryField 3) := h ▸ (show a x ∈ a.range from ⟨x,rfl⟩)
    rw [←fieldProjection_ker] at hx
    exact hx
  · exact (MonoidHom.range_eq_top.mp h) (fieldAut σ)

end Theory.PSL2
