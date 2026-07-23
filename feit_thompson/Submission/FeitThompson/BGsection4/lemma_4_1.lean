module

public import Submission.FeitThompson.BGsection4.Defs

section Main

public theorem lemma_4_1 {G : Type*} [Group G] (hcyc : IsCyclic (G ⧸ Subgroup.center G)) :
    IsMulCommutative G := by
  letI : IsCyclic (G ⧸ Subgroup.center G) := hcyc
  refine ⟨⟨fun a b =>
    commutative_of_cyclic_center_quotient
      (QuotientGroup.mk' (Subgroup.center G))
      (by simp [QuotientGroup.ker_mk'])
      a b⟩⟩

end Main
