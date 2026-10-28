module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Lifting

/-!
# Converting actual product tori into Ree Sylow configurations

Let C be a finite cyclic p-group and map C × C into the Ree group. If the
image has index prime to p, it is Sylow. A generator of C supplies two
generators of the image, and the coordinate axes commute even before applying
the map. A proved ambient pair action then gives `AbelianSylowData` and
excludes p from every finite perfect central kernel for odd p.

This construction requires the literal map and its actual image index. It
does not infer a torus embedding from a proposed order or assert a Ree torus
classification. It permits noninjective maps because the p-group and index
conditions already suffice for the conclusion.

Source context: the odd local calculation in Aschbacher–Smith I.1.1–4,
printed pp.407–408, and GLS3 §6.1; concrete twisted torus constructions use
GLS3 §2.2 and Example 2.6.3.
-/

public section

namespace ReeF4.CentralCovers.OddPrimary

open Subgroup

private theorem pair_generates_range {C G : Type*} [Group C] [Group G]
    (j : C × C →* G) (z : C) (hz : ∀ a : C, a ∈ zpowers z) :
    closure ({j (z, 1), j (1, z)} : Set G) = j.range := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact ⟨(z, 1), rfl⟩
    · exact ⟨(1, z), rfl⟩
  · rintro g ⟨⟨a, b⟩, rfl⟩
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hz a)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hz b)
    have he : j (a, b) = j (z, 1) ^ i * j (1, z) ^ k := by
      rw [← map_zpow, ← map_zpow, ← map_mul]
      congr 1
      ext <;> simp [hi, hk]
    rw [he]
    exact mul_mem (zpow_mem (subset_closure (by simp)) i)
      (zpow_mem (subset_closure (by simp)) k)

/-- A prime-to-p index product torus with the specified ambient action
supplies the complete abelian Sylow configuration. -/
theorem exists_abelianSylowData_of_product {m p : ℕ} [Fact p.Prime]
    {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (hC : IsPGroup p C) (j : C × C →* Model m)
    (hi : ¬ p ∣ j.range.index)
    (hrev : ∀ z : C, ReversesPair (j (z, 1)) (j (1, z))) :
    Nonempty (AbelianSylowData m p) := by
  obtain ⟨k, hk⟩ := hC.exists_card_eq
  have hprod : IsPGroup p (C × C) := IsPGroup.of_card (n := k + k) (by
    rw [Nat.card_prod, hk, pow_add])
  have hR : IsPGroup p j.range := hprod.of_surjective j.rangeRestrict j.rangeRestrict_surjective
  let P : Sylow p (Model m) := hR.toSylow hi
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := C)
  refine ⟨{
    sylow := P
    first := j (z, 1)
    second := j (1, z)
    generated := pair_generates_range j z hz
    generators_commute := ?_
    reverses := hrev z }⟩
  apply Commute.map _ j
  show (z, (1 : C)) * (1, z) = (1, z) * (z, 1)
  simp

/-- Application to the literal Ree covering map: the product-torus input
discharges the abelian-preimage premise of central Sylow transfer. -/
theorem not_dvd_kernel_of_product {m p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    {C : Type*} [Group C] [Finite C] [IsCyclic C]
    (hC : IsPGroup p C) (j : C × C →* Model m)
    (hi : ¬ p ∣ j.range.index)
    (hrev : ∀ z : C, ReversesPair (j (z, 1)) (j (1, z)))
    {E : Type*} [Group E] [Finite E]
    (c : PerfectCentralCovering.Cover E (Model m)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  obtain ⟨D⟩ := exists_abelianSylowData_of_product hC j hi hrev
  exact D.not_dvd_kernel hp c

end ReeF4.CentralCovers.OddPrimary
