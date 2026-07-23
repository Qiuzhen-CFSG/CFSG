module

public import Submission.FeitThompson.BGsection4.Defs

section Main

public theorem lemma_4_1 {G : Type*} [Group G] (hcyc : IsCyclic (G ⧸ Subgroup.center G)) :
    IsMulCommutative G := by
  letI : IsCyclic (G ⧸ Subgroup.center G) := hcyc
  exact (QuotientGroup.mk' (Subgroup.center G)).isMulCommutative_of_isCyclic_of_ker_le_center
    (by simp [QuotientGroup.ker_mk'])

end Main
