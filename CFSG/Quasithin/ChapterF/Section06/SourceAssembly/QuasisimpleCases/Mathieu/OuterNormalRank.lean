module

public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.NormalElementaryRank
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.M12.Aut

/-!
# The marked outer Mathieu normal-rank obstruction

Transport the normal elementary rank bound and the second vertex's trivial
center through the literal marked Aut(M₁₂) amalgam isomorphism. Thus a source
vertex with nontrivial center is the involution-centralizer vertex, and its
normal elementary abelian two-subgroups have rank at most three.

This supplies the local model obstruction used for I_z in Aschbacher--Smith,
14.6.10(4), printed p.1028; compare 14.5.5, printed p.1014, refs/quasithin.pdf.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
open Subgroup Theory.GroupTheory Sporadic.Mathieu.M12ExceptionalExtension
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- The first marked Aut(M₁₂) vertex has no normal elementary subgroup
of rank four. -/
theorem outer_first_normal_elementary_rank_le_three
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (E : Subgroup G₁) [E.Normal] [IsElementaryAbelian 2 E] : Group.rank E ≤ 3 := by
  obtain ⟨j⟩ := hM
  let e := (j.trans GreenBook.AutMathieuTwelve.ambientIso.symm).trans
    GreenBook.AutMathieuTwelve.concreteIso
  exact FirstParabolic.normal_elementary_rank_le_three_of_equiv e.left E

/-- The first marked vertex bound in the source's prime-rank convention. -/
theorem outer_first_normal_elementary_primeRank_le_three
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (E : Subgroup G₁) [E.Normal] [IsElementaryAbelian 2 E] : primeRank 2 E ≤ 3 := by
  obtain ⟨j⟩ := hM
  let e := (j.trans GreenBook.AutMathieuTwelve.ambientIso.symm).trans
    GreenBook.AutMathieuTwelve.concreteIso
  exact FirstParabolic.normal_elementary_primeRank_le_three_of_equiv e.left E

omit [Finite G] in
/-- Triviality of the second vertex center fixes the orientation when a
source vertex centralizes its distinguished nonidentity involution. -/
theorem outer_second_center_eq_bot
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)) :
    center G₂ = ⊥ := by
  obtain ⟨j⟩ := hM
  let e := (j.trans GreenBook.AutMathieuTwelve.ambientIso.symm).trans
    GreenBook.AutMathieuTwelve.concreteIso
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply e.right.injective
  have hm : e.right x ∈ center secondParabolic := (centerCongr e.right ⟨x,hx⟩).property
  rw [secondParabolic_center_eq_bot] at hm
  exact (mem_bot.mp hm).trans (map_one e.right).symm

/-- The normal-rank bound for either marked vertex with nontrivial center.
This is the orientation test used by the original I_z application. -/
theorem outer_centered_parabolic_normal_elementary_rank_le_three
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (P : Subgroup G) (hP : P = G₁ ∨ P = G₂) (hZ : center P ≠ ⊥)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] : Group.rank E ≤ 3 := by
  rcases hP with rfl | rfl
  · exact outer_first_normal_elementary_rank_le_three hM E
  · exact False.elim (hZ (outer_second_center_eq_bot hM))

/-- The source prime-rank bound with orientation selected by nontrivial center. -/
theorem outer_centered_parabolic_normal_elementary_primeRank_le_three
    (hM : GreenBook.AutMathieuTwelve.IsAutM12Amalgam
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right))
    (P : Subgroup G) (hP : P = G₁ ∨ P = G₂) (hZ : center P ≠ ⊥)
    (E : Subgroup P) [E.Normal] [IsElementaryAbelian 2 E] : primeRank 2 E ≤ 3 := by
  rcases hP with rfl | rfl
  · exact outer_first_normal_elementary_primeRank_le_three hM E
  · exact False.elim (hZ (outer_second_center_eq_bot hM))

end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
