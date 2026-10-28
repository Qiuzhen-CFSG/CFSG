module

public import Theory.SpecificGroups.Suzuki.SubgroupContainment
public import Theory.GroupTheory.SolvableNormalAbelian

/-!
# Standard containment of solvable Suzuki subgroups

A nontrivial solvable subgroup has a nontrivial abelian normal subgroup.
The latter lies in a unique root or torus partition member, whose normalizer
therefore contains the original subgroup. These normalizers are exactly the
four standard alternatives. The trivial subgroup is contained in the Borel.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), printed p. 194;
Suzuki, *On a class of doubly transitive groups*, Ann. Math. 75 (1962), 104--145.
-/

namespace BenderSuzuki.MatrixGroups

/-- Every solvable Suzuki subgroup is conjugate into one of the four
standard solvable subgroups. -/
public theorem suzukiStandardContainment_of_isSolvable {m : ℕ} (hm : 0 < m)
    (T : SuzukiNonsplitTorusPair m) (H : Subgroup (SuzukiMatrixGroup m))
    [Group.IsSolvable H] : SuzukiStandardContainment T H := by
  by_cases hH : H = ⊥
  · subst H
    exact suzukiStandardContainment_bot T
  have : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  obtain ⟨A, hAn, hAc, hA⟩ := Group.exists_nontrivial_abelian_normal H
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let B := A.map H.subtype
  have hB : B ≠ ⊥ := by
    intro hB
    apply hA
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxB : (x : SuzukiMatrixGroup m) ∈ B := ⟨x, hx, rfl⟩
    rw [hB] at hxB
    exact Subtype.ext (Subgroup.mem_bot.mp hxB)
  obtain ⟨U, ⟨hU, hBU⟩, _⟩ := suzukiAbelianSubgroup_partition_existsUnique hm B hB
  apply suzukiStandardContainment_of_normal_partition_subgroup hm T hB hBU hU
  rw [Subgroup.le_normalizer_iff]
  intro h hh b hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨(⟨h, hh⟩ : H) * a * (⟨h, hh⟩ : H)⁻¹,
    hAn.conj_mem a ha ⟨h, hh⟩, rfl⟩

end BenderSuzuki.MatrixGroups
