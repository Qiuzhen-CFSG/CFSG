module
public import ABG.ChapterII.Section1.MaximalModels
public import ABG.ChapterII.Section1.Center
public import ABG.ChapterII.Section1.OrderFourClasses
public import ABG.ChapterII.Section1.WreathedDefs
public import Theory.GroupTheory.SpecificGroups.QuaternionContainment

/-!
# The largest quaternion subgroup of a quasi-dihedral group

A semidihedral group has a generalized quaternion subgroup of index two
containing every generalized quaternion subgroup. The order-eight quaternion
group is included. No additional ambient finiteness hypothesis is needed:
the semidihedral predicate retains the exact order and presentation.

For generators a,b, the explicit subgroup Y = <a^2,ab> is quaternion and
has index two by MaximalModels, hence is normal. Outside the cyclic subgroup
<a>, the square formula gives central squares, while each order-four element
is conjugate to ab and therefore lies in Y. The general quaternion containment
lemma now places every generalized quaternion subgroup in Y.

This is the containment consequence of ABG Chapter II Section 1 Lemma 1(iii),
article p.9 of `refs/latex/alperin-brauer-gorenstein.tex`, proved from the
presentation of article p.2. It supplies the largest quaternion subgroup used
in the subsequent Q-group definition, independently of Section 2 vocabulary.
-/

namespace ABG.QuasiDihedral
variable {G : Type*} [Group G]

/-- A semidihedral group has an index-two generalized quaternion subgroup
containing every generalized quaternion subgroup. -/
public theorem exists_largest_quaternion (hG : Stellmacher.IsSemidihedralGroup G) :
    ∃ Y : Subgroup G, IsGeneralizedQuaternionGroup Y ∧ Y.index = 2 ∧
      ∀ Q : Subgroup G, IsGeneralizedQuaternionGroup Q → Q ≤ Y := by
  obtain ⟨n, a, b, hn, hcard, ha, hb, hab, hgen, hnf⟩ := exists_normal_form hG
  let U := Subgroup.zpowers a
  let Y := Subgroup.closure ({a^2, a*b} : Set G)
  obtain ⟨_, _, hYindex, _, _, hYmodel⟩ :=
    explicit_subgroup_models hn a b hcard ha hb hab hgen
  have hY : Y.index = 2 := hYindex
  have hYnormal : Y.Normal := Y.normal_of_index_eq_two hY
  refine ⟨Y, ⟨n-3, by omega, hYmodel⟩, hY, ?_⟩
  intro Q hQ
  obtain ⟨m, hm, ⟨e⟩⟩ := hQ
  have hm2 : 2 ≤ 2^m := by
    simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hm
  apply QuaternionGroup.subgroup_le_of_outer_order_four U Y Q ?_ ?_ ?_ hm2 e
  · rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact Commute.zpow_zpow_self a i j
  · intro x hx y
    obtain ⟨i, _, rfl | rfl⟩ := hnf x
    · exact (hx (U.pow_mem (Subgroup.mem_zpowers a) i)).elim
    · have hc : (a^i*b)^2 ∈ Subgroup.center G := by
        rw [outer_square hn a b hb hab, pow_mul]
        exact (Subgroup.center G).pow_mem
          (half_order_pow_mem_center hn a b ha hb hab hgen) i
      exact (Subgroup.mem_center_iff.mp hc y).symm
  · intro x hx hx4
    obtain ⟨i, _, rfl | rfl⟩ := hnf x
    · exact (hx (U.pow_mem (Subgroup.mem_zpowers a) i)).elim
    · have hc := outer_order_four_isConj a b (2^(n-2)) i
        (by rw [ha, show n-1=n-2+1 by omega, pow_succ, Nat.mul_comm])
        (outer_square hn a b hb hab) (outer_even_shift_isConj hn a b ha hab) hx4
      obtain ⟨g, hg⟩ := isConj_iff.mp hc.symm
      rw [← hg]
      exact hYnormal.conj_mem (a*b) (Subgroup.subset_closure (by simp)) g
end ABG.QuasiDihedral
