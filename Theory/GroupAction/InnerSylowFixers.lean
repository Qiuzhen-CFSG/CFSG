module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# A two-element pointwise Sylow fixer is the inner center

In a centerless finite group, the nontrivial center of a nontrivial Sylow
two-subgroup embeds by conjugation into its pointwise fixer. If that fixer
has order at most two, these inner automorphisms exhaust it. This gives
the precise inner implementation needed for the PSL₃(3) case of
Aschbacher--Smith 2.5.8(4), printed pp.556--557.
-/

public section
open Subgroup
namespace Theory.GroupAction

/-- A pointwise Sylow fixer with at most two elements is inner by the
center of the specified Sylow subgroup. -/
theorem sylow_fixer_inner_of_card_le_two {K : Type*} [Group K] [Finite K]
    (hZ : center K = ⊥) (P : Sylow 2 K) [Nontrivial P]
    (hbound : ∀ A : Subgroup (MulAut K), (∀ a ∈ A, ∀ x ∈ P, a x = x) → Nat.card A ≤ 2)
    (a : MulAut K) (ha : ∀ x ∈ P, a x = x) :
    ∃ z : center P, a = MulAut.conj (z.val : K) := by
  let C := fixingSubgroup (MulAut K) (P : Set K)
  let f : center P →* MulAut K := MulAut.conj.comp
    ((P : Subgroup K).subtype.comp (center P).subtype)
  have hf : Function.Injective f := (Theory.GroupTheory.conj_injective_of_center_eq_bot hZ).comp
    ((P : Subgroup K).subtype_injective.comp (center P).subtype_injective)
  have hfc : f.range ≤ C := by
    rintro _ ⟨z, rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro x hx
    change (z.val : K) * x * (z.val : K)⁻¹ = x
    apply mul_inv_eq_iff_eq_mul.mpr
    exact (congrArg Subtype.val (mem_center_iff.mp z.property (⟨x, hx⟩ : P))).symm
  let : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  have hcard : 2 ≤ Nat.card f.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    exact Finite.one_lt_card
  have hCcard : Nat.card C ≤ 2 := hbound C (by
    intro b hb x hx
    exact hb ⟨x, hx⟩)
  have heq : f.range = C := eq_of_le_of_card_ge hfc (hCcard.trans hcard)
  have hac : a ∈ C := by rw [mem_fixingSubgroup_iff]; exact ha
  rw [← heq] at hac
  obtain ⟨z, hz⟩ := hac
  exact ⟨z, hz.symm⟩

end Theory.GroupAction
