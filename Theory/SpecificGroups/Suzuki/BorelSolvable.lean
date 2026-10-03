module

public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.GroupTheory.SolvableNormalSup

/-!
# Solvability of the standard Suzuki Borel subgroup

The root group is a finite `2`-group, hence solvable. The split torus is
cyclic and normalizes the root group. Their product is therefore solvable,
by the solvability of extensions. This is the root-by-torus argument used
for the point stabilizer in XI.3.6, expressed through the standard subgroups.

Source: Huppert--Blackburn, *Finite Groups III*, XI.3.1, XI.3.3 and
XI.3.12(e), printed pp. 182--188 and 194.
-/

namespace BenderSuzuki.MatrixGroups

/-- The standard Borel subgroup is solvable. -/
public theorem suzukiBorelSubgroup_isSolvable (m : ℕ) (hm : 0 < m) :
    Group.IsSolvable (SuzukiBorelSubgroup m) := by
  let F := SuzukiRootSubgroup m
  let H := SuzukiSplitTorus m
  let B := SuzukiBorelSubgroup m
  have hF : F ≤ B := by
    dsimp only [F, B]
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_left
  have hH : H ≤ B := by
    dsimp only [H, B]
    rw [suzukiBorelSubgroup_eq_sup]
    exact le_sup_right
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsNilpotent F := (suzukiRootSubgroup_isPGroup m hm).isNilpotent
  let : IsCyclic H := suzukiSplitTorus_isCyclic m hm
  let := IsCyclic.commGroup (α := H)
  let : (F.subgroupOf B).Normal := suzukiRootSubgroup_normal_in_borel m
  let eF := Subgroup.subgroupOfEquivOfLe hF
  let eH := Subgroup.subgroupOfEquivOfLe hH
  let : Group.IsSolvable (F.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := eF.toMonoidHom) eF.injective
  let : Group.IsSolvable (H.subgroupOf B) :=
    Group.isSolvable_of_isSolvable_injective (f := eH.toMonoidHom) eH.injective
  apply Group.isSolvable_of_normal_sup_eq_top (F.subgroupOf B) (H.subgroupOf B)
  rw [← Subgroup.subgroupOf_sup hF hH]
  change (SuzukiRootSubgroup m ⊔ SuzukiSplitTorus m).subgroupOf B = ⊤
  rw [← suzukiBorelSubgroup_eq_sup, Subgroup.subgroupOf_self]

end BenderSuzuki.MatrixGroups
