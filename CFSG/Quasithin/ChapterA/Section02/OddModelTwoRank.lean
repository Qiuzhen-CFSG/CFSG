module

public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.OddThreeRank

/-!
# Two-rank of the odd-characteristic Theorem C models

Odd-field PSL₂ embeds in PGL₂, whose Sylow two-subgroups are dihedral.
The degree-three linear and unitary models have two-rank at most two by
their actual special-to-projective comparisons and faithful sign actions.
Thus every odd-characteristic row of Theorem C has two-rank at most two.

Source: Aschbacher--Smith A.2.3, printed p.33, and the exclusion in C.3.1,
printed p.151. The field and quotient markings are those in the catalogue.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section02

/-- Every actual odd-characteristic model in Theorem C has two-rank at most two. -/
theorem IsTheoremCOddModel.twoRank_le_two
    {S : Type*} [Group S] [Finite S] (hm : IsTheoremCOddModel S) :
    primeRank 2 S ≤ 2 := by
  cases hm with
  | linear_two p n hp ho _ hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hn : 0 < n := by
      by_contra! hn
      have hcard := Finite.one_lt_card (α := F)
      simp only [Nat.le_zero.mp hn,pow_zero] at hF
      omega
    let : Finite (GorensteinWalter.PGL2 F) :=
      Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    rw [primeRank_equiv 2 e]
    exact (Theory.GroupTheory.primeRank_le_of_injective 2
      Matrix.ProjectiveSpecialLinearGroup.toPGL
      Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (Theory.PSL2.odd_pgl_two_rank F ⟨p,n,hp,ho,hn,hF⟩)
  | linear_three p hp ho hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psl3_primeRank_two_le hp ho hF
  | unitary_three p hp ho hm =>
    obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv S e.toEquiv
    rw [primeRank_equiv 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J hp ho hF hconj

end CFSG.Quasithin.ChapterA.Section02
