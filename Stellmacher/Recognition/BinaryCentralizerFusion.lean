module

public import Stellmacher.Recognition.BinaryCentralizerRankOne
public import Theory.GroupTheory.BinaryCentralizerRankTwo
public import Theory.GroupTheory.ElementaryCommutingStabilizer

/-!
# Binary centralizer component transport

Under the binary weak-core hypotheses in a finite nonsolvable simple N₂ group,
the centralizer of Q preserves the commuting component of the elementary
subgroup A of order at least eight in the chosen Sylow two-subgroup S.

If the centralizer contains an elementary four-group, use rank-two centralizer
transport. Otherwise, an elementary subgroup D of order at least eight in Q
connects to A inside S and is fixed by the centralizer. The remaining case is
the rank-one centralizer theorem, using solvability of two-local subgroups.

Source: the binary simple-group remark following GLS2, Proposition 22.4
(`refs/KGroup/GLS2/ChapterF.tex`). This supplies the centralizer step for the
Frattini reduction in `Theory.GroupTheory.BinaryWeakCoreFusion`; the displayed
odd-prime argument in the source does not establish this binary step.
-/

namespace Stellmacher.Recognition
open Subgroup

/-- Centralizer transport under the original binary weak-core hypotheses. -/
public theorem binaryCentralizer_transport
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (A Q E B : Subgroup G)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 E] [IsElementaryAbelian 2 B]
    (hAS : A ≤ S) (hA : 8 ≤ Nat.card A) (hQS : Q ≤ S)
    (hEQ : E ≤ Q) (hE : 4 ≤ Nat.card E)
    (hBQC : B ≤ Q ⊔ ((S : Subgroup G) ⊓ centralizer (Q : Set G)))
    (hB : 8 ≤ Nat.card B)
    (c : G) (hc : c ∈ centralizer (Q : Set G)) :
    ElementaryCommutingConnected 2 A (A.map (MulAut.conj c).toMonoidHom) := by
  by_cases hC : ∃ F : Subgroup G, F ≤ centralizer (Q : Set G) ∧
      IsElementaryAbelian 2 F ∧ 4 ≤ Nat.card F
  · obtain ⟨F, hFC, hF, hFcard⟩ := hC
    let : IsElementaryAbelian 2 F := hF
    exact elementaryCommutingConnected_conj_of_centralizer_rank_two
      (S : Subgroup G) A Q E B F S.isPGroup' hAS hQS hEQ hBQC hFC hA hE hB hFcard c hc
  have hrank : ∀ F : Subgroup G, F ≤ centralizer (Q : Set G) →
      IsElementaryAbelian 2 F → Nat.card F < 4 := by
    intro F hFC hF
    exact Nat.lt_of_not_ge (fun hFcard => hC ⟨F, hFC, hF, hFcard⟩)
  by_cases hQ : ∃ D : Subgroup G, D ≤ Q ∧
      IsElementaryAbelian 2 D ∧ 8 ≤ Nat.card D
  · obtain ⟨D, hDQ, hD, hDcard⟩ := hQ
    let : IsElementaryAbelian 2 D := hD
    have hAD := elementaryCommutingConnected_of_le_twoGroup
      (S : Subgroup G) A D S.isPGroup' hA hDcard hAS (hDQ.trans hQS)
    exact normalizer_le_elementaryCommutingComponentStabilizer A D inferInstance
      (by omega) hAD ((centralizer_le hDQ).trans (Subgroup.centralizer_le_normalizer _) hc)
  have hQrank : ∀ D : Subgroup G, D ≤ Q →
      IsElementaryAbelian 2 D → Nat.card D < 8 := by
    intro D hDQ hD
    exact Nat.lt_of_not_ge (fun hDcard => hQ ⟨D, hDQ, hD, hDcard⟩)
  exact binaryCentralizerRankOne_transport hG hN S A Q E B
    hAS hA hQS hEQ hE hBQC hB hrank hQrank c hc

end Stellmacher.Recognition
