module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion.Local
public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.BinaryParabolicThreeRank
public import Theory.SpecificGroups.Triality.Model.QTKE

/-!
# Excluding the genuine binary triality model

The local component intersection has a nontrivial two-core and three-rank
at least two. Transport its core through the actual ³D₄(2) equivalence.
The checked hexagon normalizer theorem embeds the whole local intersection
in a conjugate root parabolic. Both binary parabolics have three-rank at
most one, giving the contradiction. The triality carrier is the genuine
D₄ graph-field construction throughout.

Source: Aschbacher--Smith, initial parabolic selection, printed p.1139;
the local rank calculation also occurs in the proof of 1.3.4, p.511,
using the Levi factors described in F.1.11--12, pp.262--264.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
open SmallModelExclusion
variable {G : Type*} [Group G] [Finite G]
variable {L MI Y S : Subgroup G} [L.Normal]
private instance component_normal : (centralizerQuotientComponent L).Normal :=
  (inferInstance : L.Normal).map (centralizerQuotientMap L) (QuotientGroup.mk'_surjective _)

/-- The genuine ³D₄(2) carrier cannot realize the full rank-two local shadow. -/
theorem Setup.not_triality_two (d : Setup L MI Y S)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (centralizerQuotientComponent L)) : False := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_two_iff _).mp hm
  let H := (MI.map (centralizerQuotientMap L)).subgroupOf (centralizerQuotientComponent L)
  let j := e.toMonoidHom.comp H.subtype
  have hj : Function.Injective j := e.injective.comp H.subtype_injective
  let R := (pCore 2 H).map j
  have hR : R ≠ ⊥ := by
    intro he
    exact local_core_ne_bot d.quotient_local (quotient_two d)
      (((pCore 2 H).map_eq_bot_iff_of_injective hj).mp he)
  obtain ⟨g, a, hplace⟩ := Triality.Standard.TwoLocalCover.normalizer_cover
    1 (by decide) R hR (pCore_isPGroup.map j)
  let f := (MulAut.conj g).toMonoidHom.comp j
  have hnormal (h : H) : j h ∈ normalizer (R : Set _) := by
    apply (pCore 2 H).le_normalizer_map j
    exact ⟨h, by rw [normalizer_eq_top]; trivial, rfl⟩
  let P := Triality.Standard.Parabolics.parabolic (Triality.Standard.binaryParameters 1 (by decide)) a
  have hfP (h : H) : f h ∈ P := hplace ⟨j h, hnormal h, rfl⟩
  have hr : primeRank 3 H ≤ 1 :=
    (primeRank_le_of_injective 3 (f.codRestrict P hfP)
      (fun x y h => hj ((MulAut.conj g).injective (congrArg Subtype.val h)))).trans
        (Triality.Standard.Parabolics.parabolic_threeRank_le_one_of_q_eq_two _ rfl a)
  have hl : 2 ≤ primeRank 3 H := local_threeRank d.quotient_local (quotient_two d)
  omega

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
