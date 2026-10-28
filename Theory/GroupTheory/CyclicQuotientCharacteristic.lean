module

public import Theory.GroupTheory.CyclicSubgroupNormalizer
public import Theory.PGroupCore
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Characteristic subgroups over a cyclic quotient

Every subgroup of a finite cyclic group is characteristic: membership is
characterized by a power equal to one. Consequently every overgroup of a
characteristic subgroup with cyclic quotient is characteristic. A cyclic
supplement supplies the cyclic quotient through its actual projection.

These facts control the prime torus preimages in the original rank-one
Borel in Aschbacher--Smith, 5.2.2, printed p.648.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Every subgroup of a finite cyclic group is characteristic. -/
theorem characteristic_of_cyclic (D : Subgroup G) [IsCyclic G] : D.Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro f x hx
  change f x ∈ D
  apply mem_of_pow_card_eq_one_in_cyclic
  rw [← map_pow]
  have he : x ^ Nat.card D = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : D)))
  rw [he, map_one]

/-- Overgroups of a characteristic subgroup with cyclic quotient are characteristic. -/
theorem characteristic_of_cyclic_quotient (N D : Subgroup G) [N.Characteristic]
    [IsCyclic (G ⧸ N)] (hND : N ≤ D) : D.Characteristic := by
  have he : (D.map (QuotientGroup.mk' N)).comap (QuotientGroup.mk' N) = D := by
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hND]
  rw [← he]
  exact Subgroup.Characteristic.comap_quotient_mk (H := N)
    (characteristic_of_cyclic (D.map (QuotientGroup.mk' N)))

omit [Finite G] in
/-- A cyclic supplement surjects onto the literal quotient. -/
theorem isCyclic_quotient_of_cyclic_supplement (N A : Subgroup G) [N.Normal]
    [IsCyclic A] (hsup : N ⊔ A = ⊤) : IsCyclic (G ⧸ N) := by
  let q := QuotientGroup.mk' N
  have hs : A.map q = ⊤ := by
    have hh := congrArg (Subgroup.map q) hsup
    rw [Subgroup.map_sup, map_top_of_surjective q (QuotientGroup.mk'_surjective N)] at hh
    have hN : N.map q = ⊥ := by
      rw [map_eq_bot_iff]
      exact le_of_eq (QuotientGroup.ker_mk' N).symm
    simpa only [hN, bot_sup_eq] using hh
  have hf : Function.Surjective (q.comp A.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype, hs]
  exact isCyclic_of_surjective (q.comp A.subtype) hf
end Subgroup
