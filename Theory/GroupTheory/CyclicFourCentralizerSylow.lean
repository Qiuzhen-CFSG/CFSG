module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

/-!
# Detecting a cyclic Sylow subgroup in an element centralizer

Let `u` have order four and commute with `r`. If every two-element
centralizing both `u²` and `r` lies in `⟨u⟩`, then `⟨u⟩` is a Sylow
two-subgroup of `C(r)`. Its normalizer fixes the unique involution `u²`;
the normalizer condition in a Sylow overgroup then forces equality.
This is the final local-to-global step of Fong's order-three construction
(J. Algebra 6 (1967), p.75).
-/

namespace Subgroup

public theorem normalizer_zpowers_four_le_centralizer_square
    {G : Type*} [Group G] (u : G) (hu : orderOf u = 4) :
    normalizer (zpowers u : Set G) ≤ centralizer ({u ^ 2} : Set G) := by
  classical
  have hu4 : u ^ 4 = 1 := hu ▸ pow_orderOf_eq_one u
  have hu2 : u ^ 2 ≠ 1 := by
    intro hh
    have hd := orderOf_dvd_of_pow_eq_one hh
    rw [hu] at hd
    norm_num at hd
  intro g hg
  let f := MulAut.conj g
  have hm : f (u ^ 2) ∈ zpowers u :=
    (hg (u ^ 2)).mp ((zpowers u).pow_mem (mem_zpowers u) 2)
  have hne : f (u ^ 2) ≠ 1 := by
    intro h
    exact hu2 (f.injective (h.trans (map_one f).symm))
  have hs : (f (u ^ 2)) ^ 2 = 1 := by
    rw [← map_pow, ← pow_mul, hu4, map_one]
  rw [(orderOf_pos_iff.mp (by omega : 0 < orderOf u)).mem_zpowers_iff_mem_range_orderOf,
    hu] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hn4 := Finset.mem_range.mp hn
  have hfix : f (u ^ 2) = u ^ 2 := by
    interval_cases n
    · exact (hne (by simpa using he.symm)).elim
    · exact (hu2 (by simpa only [← he, pow_one] using hs)).elim
    · exact he.symm
    · have hh : (u ^ 3) ^ 2 = u ^ 2 := by
        rw [← pow_mul, show 3 * 2 = 4 + 2 from rfl, pow_add, hu4, one_mul]
      exact (hu2 (hh.symm.trans (by simpa only [he] using hs))).elim
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix)

public theorem exists_sylow_centralizer_eq_zpowers_four
    {G : Type*} [Group G] [Finite G] (u r : G) (hu : orderOf u = 4)
    (hur : Commute u r)
    (hbound : ∀ t : G, Commute t (u ^ 2) → Commute t r →
      (∃ n : ℕ, t ^ (2 ^ n) = 1) → t ∈ zpowers u) :
    ∃ T : Sylow 2 (centralizer ({r} : Set G)),
      (T : Subgroup (centralizer ({r} : Set G))).map
        (centralizer ({r} : Set G)).subtype = zpowers u := by
  let C := centralizer ({r} : Set G)
  let U := zpowers u
  have hUC : U ≤ C := zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hur.eq)
  let K := U.subgroupOf C
  have hmap : K.map C.subtype = U := map_subgroupOf_eq_of_le hUC
  have hp : IsPGroup 2 U := IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu]; decide)
  have hKp : IsPGroup 2 K := hp.comap_subtype
  obtain ⟨T, hKT⟩ := hKp.exists_le_sylow
  have hTK : (T : Subgroup C) ≤ K := by
    by_contra hh
    have hproper : K.subgroupOf (T : Subgroup C) < ⊤ := by
      rwa [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    let : Group.IsNilpotent T := T.isPGroup'.isNilpotent
    obtain ⟨t, htN, htK⟩ := SetLike.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (K.subgroupOf (T : Subgroup C)) hproper)
    have htNK : (t : C) ∈ normalizer (K : Set C) := by
      rw [← subgroupOf_normalizer_eq hKT] at htN
      exact htN
    have htNU : ((t : C) : G) ∈ normalizer (U : Set G) := by
      rw [← hmap]
      exact K.le_normalizer_map C.subtype (mem_map_of_mem C.subtype htNK)
    apply htK
    apply hbound
    · exact mem_centralizer_singleton_iff.mp
        (normalizer_zpowers_four_le_centralizer_square u hu htNU)
    · exact mem_centralizer_singleton_iff.mp (t : C).property
    · obtain ⟨n, hn⟩ := isPGroup_iff_pow_pow_eq_one.mp T.isPGroup' t
      exact ⟨n, congrArg (fun a : T => ((a : C) : G)) hn⟩
  exact ⟨T, by rw [le_antisymm hTK hKT]; exact hmap⟩

end Subgroup
