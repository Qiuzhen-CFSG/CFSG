module

public import Theory.GroupTheory.SpecificGroups.KleinFourAut
import Mathlib.Tactic

/-!
# The point stabilizer of a four-group

An automorphism of a four-group fixing a nonidentity point can only swap
the other two nonidentity points. Thus any subgroup moving the four-group
while fixing that point supplements its centralizer in the point stabilizer.
The proof compares automorphisms on two generators.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, Lemma 12.8.12(2), printed p.855.
-/

namespace IsKleinFour
variable {A : Type*} [Group A] [IsKleinFour A]

private theorem aut_ext_on_pair {z t : A} (hz : z ≠ 1) (ht : t ≠ 1) (hzt : z ≠ t)
    {a b : MulAut A} (hzab : a z = b z) (htab : a t = b t) : a = b := by
  classical
  let : Fintype A := Fintype.ofFinite A
  apply MulEquiv.ext
  intro x
  have hx : x ∈ ({z * t, z, t, 1} : Finset A) :=
    (eq_finset_univ hz ht hzt).symm ▸ Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [map_mul, hzab, htab]
  · exact hzab
  · exact htab
  · simp

/-- The stabilizer of a nonidentity point of a four-group has at most two
elements: any nonidentity automorphism fixing that point generates it. -/
public theorem aut_eq_or_eq_one_of_fixed_point (z : A) (hz : z ≠ 1)
    (a b : MulAut A) (ha : a z = z) (hb : b z = z) (hne : a ≠ 1) :
    b = a ∨ b = 1 := by
  classical
  have hex : ∃ t, a t ≠ t := by
    by_contra! h
    apply hne
    exact MulEquiv.ext h
  obtain ⟨t, ht⟩ := hex
  have ht1 : t ≠ 1 := by intro h; apply ht; simp [h]
  have hzt : z ≠ t := by intro h; apply ht; simpa [← h] using ha
  have hat1 : a t ≠ 1 := fun h => ht1 (a.injective (h.trans (map_one a).symm))
  have hatz : a t ≠ z := by
    rw [← ha]
    exact a.injective.ne hzt.symm
  have hat : a t = z * t := eq_mul_of_ne_all hz ht1 hzt hat1 hatz ht
  by_cases hbt : b t = t
  · right
    apply aut_ext_on_pair hz ht1 hzt
    · exact hb
    · exact hbt
  · left
    apply aut_ext_on_pair hz ht1 hzt
    · exact hb.trans ha.symm
    · rw [hat]
      apply eq_mul_of_ne_all hz ht1 hzt
      · exact fun h => ht1 (b.injective (h.trans (map_one b).symm))
      · rw [← hb]
        exact b.injective.ne hzt.symm
      · exact hbt
end IsKleinFour

namespace Subgroup
variable {G : Type*} [Group G]

/-- Any subgroup moving a four-group while fixing its marked point supplements
the plane centralizer in the point-plane stabilizer. -/
public theorem kleinFour_point_stabilizer_eq_centralizer_sup
    (A U : Subgroup G) [IsKleinFour A] (z : A) (hz : z ≠ 1)
    (hUA : U ≤ normalizer (A : Set G))
    (hUz : U ≤ centralizer ({(z : G)} : Set G))
    (hmove : ¬ U ≤ centralizer (A : Set G)) :
    normalizer (A : Set G) ⊓ centralizer ({(z : G)} : Set G) =
      centralizer (A : Set G) ⊔ U := by
  classical
  have hex : ∃ u ∈ U, u ∉ centralizer (A : Set G) := by
    by_contra! h
    exact hmove h
  obtain ⟨u, hu, huc⟩ := hex
  let u' : normalizer (A : Set G) := ⟨u, hUA hu⟩
  have hune : A.normalizerMonoidHom u' ≠ 1 := by
    intro he
    apply huc
    have hk : u' ∈ A.normalizerMonoidHom.ker := he
    rwa [normalizerMonoidHom_ker] at hk
  have huz : A.normalizerMonoidHom u' z = z := by
    apply Subtype.ext
    change u * (z : G) * u⁻¹ = z
    rw [(mem_centralizer_singleton_iff.mp (hUz hu))]
    simp only [mul_inv_cancel_right]
  apply le_antisymm
  · intro h hh
    let h' : normalizer (A : Set G) := ⟨h, hh.1⟩
    have hhz : A.normalizerMonoidHom h' z = z := by
      apply Subtype.ext
      change h * (z : G) * h⁻¹ = z
      rw [mem_centralizer_singleton_iff.mp hh.2]
      simp only [mul_inv_cancel_right]
    rcases IsKleinFour.aut_eq_or_eq_one_of_fixed_point z hz
      (A.normalizerMonoidHom u') (A.normalizerMonoidHom h') huz hhz hune with he | he
    · have hc : h' * u'⁻¹ ∈ A.normalizerMonoidHom.ker := by
        change A.normalizerMonoidHom (h' * u'⁻¹) = 1
        rw [map_mul, map_inv, he, mul_inv_cancel]
      rw [normalizerMonoidHom_ker] at hc
      have hc' : h * u⁻¹ ∈ centralizer (A : Set G) := hc
      have hm := (centralizer (A : Set G) ⊔ U).mul_mem
        ((le_sup_left : centralizer (A : Set G) ≤ centralizer (A : Set G) ⊔ U) hc')
        ((le_sup_right : U ≤ centralizer (A : Set G) ⊔ U) hu)
      simpa only [inv_mul_cancel_right] using hm
    · have hc : h' ∈ A.normalizerMonoidHom.ker := he
      rw [normalizerMonoidHom_ker] at hc
      exact (le_sup_left : centralizer (A : Set G) ≤ centralizer (A : Set G) ⊔ U) hc
  · apply sup_le
    · exact le_inf (centralizer_le_normalizer _)
        (centralizer_le (Set.singleton_subset_iff.mpr z.property))
    · exact le_inf hUA hUz
end Subgroup
