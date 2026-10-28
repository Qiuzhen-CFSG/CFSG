module
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Normal-subgroup images through a two-group kernel

Suppose an odd subgroup A surjects through f, whose kernel is a two-group.
For a normal subgroup K, its image is already the image of A ∩ K. Indeed,
a lift in A of f(k) maps modulo K into both the odd image of A and the
two-group image of ker(f), and is therefore trivial there.

The actual Borel projection in the Cartan argument uses this to bound its
normal component intersection without assuming the selected Hall complement
is invariant under the inverter. Source: Aschbacher–Smith 5.1.13, p.638.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Finite G] [Group H]

theorem normal_image_eq_odd_intersection (f : G →* H) (A K : Subgroup G)
    [K.Normal] (hp : IsPGroup 2 f.ker) (ho : Odd (Nat.card A))
    (ha : A.map f = ⊤) : K.map f = (A ⊓ K).map f := by
  let q := QuotientGroup.mk' K
  have hd : Disjoint (A.map q) (f.ker.map q) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨j,hj⟩ := (hp.map q).exists_card_eq
    rw [hj]
    exact (ho.of_dvd_nat (A.card_map_dvd q)).coprime_two_right.pow_right j
  apply le_antisymm
  · rintro _ ⟨k,hk,rfl⟩
    obtain ⟨a,ha,haf⟩ := ha.ge (show f k ∈ (⊤ : Subgroup H) from trivial)
    have hm : k⁻¹ * a ∈ f.ker := by
      change f (k⁻¹ * a) = 1
      rw [map_mul,map_inv,haf,inv_mul_cancel]
    have hqa : q a ∈ f.ker.map q := by
      refine ⟨k⁻¹*a,hm,?_⟩
      rw [map_mul,map_inv,show q k = 1 from (QuotientGroup.eq_one_iff _).mpr hk]
      simp
    have he : q a = 1 := hd.le_bot ⟨mem_map_of_mem q ha,hqa⟩
    exact ⟨a,⟨ha,(QuotientGroup.eq_one_iff _).mp he⟩,haf⟩
  · exact map_mono inf_le_right
end Subgroup
