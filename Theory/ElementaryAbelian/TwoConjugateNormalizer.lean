module
public import Theory.ElementaryAbelian.UniqueLift
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Sylow

/-!
# Unique elementary lifts and a two-conjugate normalizer

A fixed-space detector on a central factor extends over a central supplement.
It identifies self-centralizing elementary lifts of the same quotient image.
If a subgroup has at most two conjugates under a normalizer containing a
Sylow two-subgroup that fixes it, its stabilizer has both odd index and index
at most two, hence is the whole normalizer.

Source: the lifting argument of Aschbacher--Smith B.2.21, pp.82--83, and the
terminal step of 13.3.10(2), p.888. OriginalUnitaryBaumann.CoreConjugates
applies these facts to the literal component--Baumann core.
-/

public section
open Subgroup
open scoped Pointwise
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem central_factor_fixed_detector (V C A : Subgroup G)
    (hC : C ≤ center G) (a : G) (ha : a ∈ A)
    (hfix : V ⊓ centralizer (A : Set G) = V ⊓ centralizer ({a} : Set G)) :
    (V ⊔ C) ⊓ centralizer (A : Set G) =
      (V ⊔ C) ⊓ centralizer ({a} : Set G) := by
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ha))
  · rintro z ⟨hz,hza⟩
    have hn : V ≤ normalizer (C : Set G) :=
      (le_centralizer_iff.mp (hC.trans (center_le_centralizer _))).trans
        (centralizer_le_normalizer _)
    have hm : z ∈ (V : Set G) * (C : Set G) := by
      rw [←coe_mul_of_left_le_normalizer_right V C hn]
      exact hz
    obtain ⟨v,hv,c,hc,rfl⟩ := hm
    have hcA : c ∈ centralizer (A : Set G) := (hC.trans (center_le_centralizer _)) hc
    have hca : c ∈ centralizer ({a} : Set G) :=
      centralizer_le (Set.singleton_subset_iff.mpr ha) hcA
    have hva : v ∈ centralizer ({a} : Set G) := by
      have hh := (centralizer ({a} : Set G)).mul_mem hza ((centralizer _).inv_mem hca)
      simpa only [mul_inv_cancel_right] using hh
    exact ⟨mul_mem_sup hv hc,(centralizer _).mul_mem ((hfix.ge ⟨hv,hva⟩).2) hcA⟩

/-- Self-centralizing elementary lifts of the same image are equal if one
actor detects their entire fixed subgroup in the elementary kernel. -/
theorem elementary_lift_eq_of_self_centralizing
    (Q A B : Subgroup G) [IsElementaryAbelian 2 Q]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (q : G →* H) (hk : q.ker = Q)
    (hA : centralizer (A : Set G) ≤ A) (hB : centralizer (B : Set G) ≤ B)
    (he : A.map q = B.map q) (a : G) (ha : a ∈ A)
    (hfix : Q ⊓ centralizer (A : Set G) = Q ⊓ centralizer ({a} : Set G)) :
    B = A := by
  have hBA := IsElementaryAbelian.le_of_same_image_of_centralizer_singleton
    q Q A B hk (inf_le_right.trans hA) (inf_le_right.trans hB) he a ha hfix
  exact le_antisymm hBA
    (((le_centralizer_iff_isMulCommutative.mpr inferInstance :
      A ≤ centralizer (A : Set G)).trans (centralizer_le hBA)).trans hB)

variable [Finite G]

theorem normalizer_le_of_sylow_two_conjugates
    (T : Sylow 2 G) (S Q : Subgroup G)
    (hTS : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (x : G) (hx : x ∈ normalizer (S : Set G))
    (horbit : ∀ g ∈ normalizer (S : Set G),
      Q.conjBy g = Q ∨ Q.conjBy g = Q.conjBy x) :
    normalizer (S : Set G) ≤ normalizer (Q : Set G) := by
  by_contra hn
  obtain ⟨a,ha,haQ⟩ := SetLike.not_le_iff_exists.mp hn
  have hxQ : x ∉ normalizer (Q : Set G) := by
    intro h
    rcases horbit a ha with hh | hh
    · exact haQ (mem_normalizer_iff_map_conj_eq.mpr hh)
    · exact haQ (mem_normalizer_iff_map_conj_eq.mpr
        (hh.trans (mem_normalizer_iff_map_conj_eq.mp h)))
  have hi : (normalizer (Q : Set G)).relIndex (normalizer (S : Set G)) = 2 := by
    apply relIndex_eq_two_iff_exists_notMem_and'.mpr
    refine ⟨x⁻¹,(normalizer _).inv_mem hx,?_,?_⟩
    · simpa only [inv_mem_iff] using hxQ
    · intro b hb
      rcases horbit b hb with hfix | hmove
      · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr hfix)
      · left
        apply mem_normalizer_iff_map_conj_eq.mpr
        exact Q.conjBy_inv_mul_cancel hmove.symm
  have hd : 2 ∣ ((T : Subgroup G).index) := by
    have hm := relIndex_dvd_index_of_le
      (show normalizer (Q : Set G) ⊓ normalizer (S : Set G) ≤
        normalizer (S : Set G) from inf_le_right)
    rw [inf_relIndex_right,hi] at hm
    exact hm.trans (index_dvd_of_le (le_inf hTQ hTS))
  exact T.not_dvd_index hd
end Subgroup
