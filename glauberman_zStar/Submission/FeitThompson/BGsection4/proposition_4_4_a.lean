module

public import Submission.FeitThompson.BGsection4.Defs
public import Submission.FeitThompson.BGsection3.theorem_3_4

section Main

public theorem proposition_4_4_a {R : Type*} [Group R] [Finite R] {p : Nat} [Fact p.Prime] :
    IsPGroup p R -> selfCentralizingAbelianSubgroups R = maximalNormalAbelianSubgroups R := by
  intro hRp
  classical
  letI : Fact (IsPGroup p R) := ⟨hRp⟩
  ext A
  constructor
  · intro hA
    rcases hA with ⟨hAnorm, hAcent⟩
    refine ⟨hAnorm, ?_, ?_⟩
    · exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).1 <|
        by simp [hAcent]
    · intro B hAB hBcomm
      apply le_antisymm
      · intro b hb
        have hbcent : b ∈ Subgroup.centralizer (A : Set R) := by
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          exact congrArg Subtype.val
            ((IsMulCommutative.is_comm (M := B)).comm ⟨a, hAB ha⟩ ⟨b, hb⟩)
        simpa [hAcent] using hbcent
      · exact hAB
  · intro hA
    rcases hA with ⟨hAnorm, hAcomm, hAmax⟩
    have hcent_le :
        Subgroup.centralizer (A : Set R) ≤ A :=
      maximal_normal_abelian_selfCentralizing_local_weak (G := R) (p := p) A hAnorm hAcomm hAmax
    refine ⟨hAnorm, le_antisymm hcent_le ?_⟩
    exact (Subgroup.le_centralizer_iff_isMulCommutative (K := A)).2 hAcomm


end Main
