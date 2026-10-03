module

public import Theory.SpecificGroups.Suzuki.SubgroupContainment
public import Theory.SpecificGroups.Suzuki.SolvableSubgroups
public import Theory.GroupTheory.SolvableNormalAbelian

/-!
# Solvable normal subgroups of Suzuki subgroups

A nontrivial solvable normal subgroup has a nontrivial characteristic
abelian subgroup. The root/torus partition puts its image in a unique
partition member, whose solvable normalizer contains the whole group.
Consequently a nonsolvable Suzuki subgroup has no nontrivial solvable
normal subgroup.

This uses the partition in Huppert--Blackburn, *Finite Groups III*, XI.3.10,
and is an elementary preliminary to the subgroup theorem XI.3.12(e).
-/

namespace BenderSuzuki.MatrixGroups

/-- A nontrivial abelian normal subgroup forces a Suzuki subgroup to be solvable. -/
public theorem suzukiSubgroup_isSolvable_of_abelian_normal
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (A : Subgroup H) [A.Normal] [IsMulCommutative A] (hA : A ≠ ⊥) :
    Group.IsSolvable H := by
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
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm
  apply T.isSolvable_of_conjugate_le_alternative hm H
  apply suzukiStandardContainment_of_normal_partition_subgroup hm T hB hBU hU
  rw [Subgroup.le_normalizer_iff]
  intro h hh b hb
  obtain ⟨a, ha, rfl⟩ := hb
  exact ⟨(⟨h, hh⟩ : H) * a * (⟨h, hh⟩ : H)⁻¹,
    (inferInstance : A.Normal).conj_mem a ha ⟨h, hh⟩, rfl⟩

/-- A Suzuki subgroup with a nontrivial solvable normal subgroup is solvable. -/
public theorem suzukiSubgroup_isSolvable_of_solvable_normal
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (N : Subgroup H) [N.Normal] [Group.IsSolvable N] (hN : N ≠ ⊥) :
    Group.IsSolvable H := by
  let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN
  obtain ⟨A, hAc, hAa, hA⟩ := Group.exists_nontrivial_abelian_characteristic N
  let : A.Characteristic := hAc
  let : IsMulCommutative A := hAa
  let B := A.map N.subtype
  have hB : B ≠ ⊥ := by
    intro h
    apply hA
    apply le_antisymm ?_ bot_le
    intro x hx
    have hmem : (x : H) ∈ B := ⟨x, hx, rfl⟩
    rw [h] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  exact suzukiSubgroup_isSolvable_of_abelian_normal hm H B hB

/-- Nonsolvable Suzuki subgroups have trivial solvable normal subgroups. -/
public theorem suzukiSubgroup_solvable_normal_eq_bot
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (hH : ¬ Group.IsSolvable H) (N : Subgroup H)
    [N.Normal] [Group.IsSolvable N] : N = ⊥ := by
  by_contra hN
  exact hH (suzukiSubgroup_isSolvable_of_solvable_normal hm H N hN)

end BenderSuzuki.MatrixGroups
