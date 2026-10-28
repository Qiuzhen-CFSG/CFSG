module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.OddThreeRank
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank

/-!
# Excluding the odd Theorem C models from the deleted-five branch

The elementary layer of the original alternating-five block has order sixteen.
Every odd-characteristic alternative in Theorem C has two-rank at most two:
PSL₂ embeds into the odd-field PGL₂, while the degree-three linear and unitary
bounds follow from their determinant-one representations and odd central kernels.
Transporting those proved bounds through the literal model equivalences rules
out all three alternatives.

Source: Aschbacher–Smith 13.5.15, printed p.921, applying Theorem C, p.33.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
variable {G : Type*} [Group G] [Finite G]

/-- The elementary layer of order sixteen excludes every odd Theorem C model. -/
theorem not_oddModel_of_elementary_sixteen
    (E : Subgroup G) (hE : IsElementaryAbelian 2 E) (hc : Nat.card E = 16) :
    ¬ ChapterA.Section02.IsTheoremCOddModel G := by
  intro hm
  have hr : primeRank 2 G ≤ 2 := by
    cases hm with
    | linear_two p n hp ho _ hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      have hn : 1 ≤ n := by
        have hlarge : 1 < Nat.card F := Finite.one_lt_card
        by_contra hn
        have hz : n = 0 := by omega
        simp only [hz, pow_zero] at hF
        omega
      let : Finite PGL(2,F) :=
        Finite.of_surjective Matrix.ProjGenLinGroup.mk
          Matrix.ProjGenLinGroup.mk_surjective
      rw [primeRank_equiv 2 e]
      exact (primeRank_le_of_injective 2
        Matrix.ProjectiveSpecialLinearGroup.toPGL
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
          (Theory.PSL2.odd_pgl_two_rank F ⟨p, n, hp, ho, hn, hF⟩)
    | linear_three p hp ho hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      rw [primeRank_equiv 2 e]
      exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
    | unitary_three p hp ho hm =>
      obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hm
      let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Finite.of_equiv G e.toEquiv
      rw [primeRank_equiv 2 e]
      exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hconj
  have hbound := (primeRank_le_iff_elementary_card_le G).mp hr E hE
  rw [hc] at hbound
  norm_num at hbound

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.DeletedFive
