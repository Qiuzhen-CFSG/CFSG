module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Automorphisms of the automorphism group of a centerless simple group

A simple normal subgroup with trivial centralizer is characteristic: its
intersection with an automorphic image is either itself or trivial; in the
latter case the image centralizes it and would be trivial.

For a centerless simple group `G`, conjugation identifies `G` with `Inn(G)`,
whose centralizer in `Aut(G)` is trivial. Hence every automorphism of `Aut(G)`
restricts to an automorphism `β` of `G`. Compatibility with conjugation shows
that the original automorphism is conjugation by `β`.

This elementary argument applies to the full automorphism group of the Tits
simple group in Aschbacher–Smith F.1.12, printed pp.263–264 of
`refs/quasithin.pdf`. It requires neither finiteness nor an assertion about
the order or solvability of `Out(G)`.
-/

public section

open Subgroup

namespace Subgroup

/-- A simple normal subgroup with trivial ambient centralizer is characteristic. -/
theorem characteristic_of_isSimpleGroup_of_centralizer_eq_bot
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [IsSimpleGroup N]
    (hc : centralizer (N : Set G) = ⊥) : N.Characteristic := by
  apply characteristic_iff_le_map.mpr
  intro α
  let M := N.map α.toMonoidHom
  have : M.Normal := (inferInstance : N.Normal).map α.toMonoidHom α.surjective
  have : IsSimpleGroup M := (α.subgroupMap N).symm.isSimpleGroup
  rcases (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup N)).2
      (N ⊓ M) inf_le_left inferInstance with h | h
  · have hcomm : ⁅M, N⁆ = ⊥ := by
      apply le_bot_iff.mp
      exact (commutator_le_inf M N).trans (by rw [inf_comm, h])
    have hM : M = ⊥ := by
      apply le_bot_iff.mp
      rw [← hc]
      exact commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact ((Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup M)).1 hM).elim
  · exact h.ge.trans inf_le_right

end Subgroup

namespace MulAut

/-- Trivial center makes the conjugation homomorphism faithful. -/
theorem conj_injective_of_center_eq_bot
    {G : Type*} [Group G] (hc : center G = ⊥) :
    Function.Injective (conj : G →* MulAut G) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro g hg
  have hz : g ∈ center G := by
    apply mem_center_iff.mpr
    intro x
    have hx := DFunLike.congr_fun hg x
    change g * x * g⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  rwa [hc] at hz

/-- For a centerless group, only the identity automorphism centralizes all
inner automorphisms. -/
theorem centralizer_innerSubgroup_eq_bot
    {G : Type*} [Group G] (hc : center G = ⊥) :
    centralizer (innerSubgroup G : Set (MulAut G)) = ⊥ := by
  apply le_bot_iff.mp
  intro α hα
  apply mem_bot.mpr
  apply MulEquiv.ext
  intro g
  apply conj_injective_of_center_eq_bot hc
  have hcomm := hα (conj g) ⟨g, rfl⟩
  have hconj : conj (α g) = α * conj g * α⁻¹ := by
    ext x
    simp
  change conj (α g) = conj g
  rw [hconj, ← hcomm, mul_inv_cancel_right]

/-- Inner automorphisms of a centerless simple group form a characteristic
subgroup of its full automorphism group. -/
theorem innerSubgroup_characteristic_of_isSimpleGroup
    {G : Type*} [Group G] [IsSimpleGroup G] (hc : center G = ⊥) :
    (innerSubgroup G).Characteristic := by
  have : IsSimpleGroup (innerSubgroup G) :=
    (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hc)).symm.isSimpleGroup
  exact characteristic_of_isSimpleGroup_of_centralizer_eq_bot _
    (centralizer_innerSubgroup_eq_bot hc)

/-- Every automorphism of the full automorphism group of a centerless simple
group is inner. -/
theorem automorphismTower_inner_of_isSimpleGroup
    {G : Type*} [Group G] [IsSimpleGroup G] (hc : center G = ⊥)
    (α : MulAut (MulAut G)) : ∃ g : MulAut G, conj g = α := by
  let e : G ≃* innerSubgroup G :=
    MonoidHom.ofInjective (conj_injective_of_center_eq_bot hc)
  have := innerSubgroup_characteristic_of_isSimpleGroup hc
  let β : MulAut G := (e.trans (MulAut.characteristic (innerSubgroup G) α)).trans e.symm
  have hβ (g : G) : conj (β g) = α (conj g) := by
    have he := e.apply_symm_apply (MulAut.characteristic (innerSubgroup G) α (e g))
    exact congrArg Subtype.val he
  refine ⟨β, ?_⟩
  apply MulEquiv.ext
  intro γ
  apply MulEquiv.ext
  intro x
  obtain ⟨g, rfl⟩ := β.surjective x
  apply conj_injective_of_center_eq_bot hc
  have hconj (δ : MulAut G) (y : G) : conj (δ y) = δ * conj y * δ⁻¹ := by
    ext z
    simp
  change conj (β (γ (β.symm (β g)))) = conj ((α γ) (β g))
  rw [β.symm_apply_apply, hβ, hconj, map_mul, map_mul, map_inv,
    hconj, hβ]

end MulAut
