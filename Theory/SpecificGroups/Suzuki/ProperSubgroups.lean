module

public import BenderSuzuki.External.Huppert.XI.SubgroupNonsolvable
public import Theory.SpecificGroups.Suzuki.SubgroupParameters

/-!
# Proper subgroups of Suzuki groups at prime field degree

Every proper subgroup of `SuzukiMatrixGroup m` is solvable when `2 * m + 1`
is prime. A nonsolvable subgroup would itself be a positive-parameter Suzuki
group by the involution-action recognition theorem. Parameter exclusion at
prime ambient degree rules out such a proper subgroup.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.12(e), using XI.11.15
for nonsolvable-subgroup recognition and XI.3.3 for parameter exclusion.
-/

namespace BenderSuzuki.MatrixGroups

/-- At prime field degree, every proper subgroup of a Suzuki group is solvable. -/
public theorem suzukiMatrixGroup_proper_subgroup_isSolvable
    {m : ℕ} (hm : Nat.Prime (2 * m + 1))
    (H : Subgroup (SuzukiMatrixGroup m)) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  have hmpos : 0 < m := by have := hm.two_le; omega
  by_contra hsolv
  obtain ⟨k, hk, he⟩ :=
    External.suzukiSubgroup_exists_mulEquiv_of_not_isSolvable hmpos H hsolv
  exact suzukiMatrixGroup_proper_subgroup_not_equiv hm H hH hk he

end BenderSuzuki.MatrixGroups
