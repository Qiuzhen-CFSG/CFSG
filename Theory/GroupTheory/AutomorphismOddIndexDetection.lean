module
public import Theory.GroupTheory.CentralDisplacementOddIndex
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

/-!
# Detecting automorphisms on an odd-index subgroup

A pointwise fixed normal subgroup forces every automorphism displacement
into its centralizer. If that subgroup is self-centralizing and its center
is central of order dividing two, an odd-index overgroup detects the whole
automorphism: the central displacement homomorphism has trivial image.

This supplies the local detection step in the extended unitary amalgam of
Aschbacher--Smith 13.5.17, printed p.922.
-/

public section
open Subgroup
namespace MulAut

/-- A fixed odd-index overgroup of a self-centralizing normal subgroup detects
the automorphism when the core center is central and has order dividing two. -/
theorem eq_one_of_fixed_odd_index_overgroup
    {G : Type*} [Group G] (N D : Subgroup G) [N.Normal]
    (hND : N ≤ D) (hself : centralizer (N : Set G) ≤ N)
    (hcentral : (center N).map N.subtype ≤ center G)
    (hcard : Nat.card (center N) ∣ 2) (hodd : ¬ 2 ∣ D.index)
    (α : MulAut G) (hfix : ∀ x ∈ D, α x = x) : α = 1 := by
  have hd (x : G) : x⁻¹ * α x ∈ centralizer (N : Set G) := by
    intro n hn
    have h := hfix (x * n * x⁻¹)
      (hND ((inferInstance : N.Normal).conj_mem n hn x))
    simp only [map_mul, map_inv, hfix n (hND hn)] at h
    have hh := congrArg (fun t : G => x⁻¹ * t * α x) h
    group at hh
    simpa only [mul_assoc, zpow_neg_one] using hh.symm
  have hz (x : G) : x⁻¹ * α x ∈ (center N).map N.subtype := by
    refine ⟨⟨_, hself (hd x)⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro n
    exact Subtype.ext (hd x n n.property)
  let δ := centralDisplacement ((center N).map N.subtype) hcentral α hz
  have hD : D ≤ δ.ker := by
    intro x hx
    apply Subtype.ext
    change x⁻¹ * α x = 1
    rw [hfix x hx, inv_mul_cancel]
  have hc : Nat.card ((center N).map N.subtype) ∣ 2 := by
    rw [card_map_of_injective N.subtype_injective]
    exact hcard
  ext x
  have he := congrArg Subtype.val
    (MonoidHom.eq_one_of_odd_index_kernel δ D hD hodd hc x)
  change x⁻¹ * α x = 1 at he
  exact (inv_mul_eq_one.mp he).symm

end MulAut
