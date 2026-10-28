module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.RankOneExclusion.Borels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.RankOneExclusion.Shadow

/-!
# Excluding rank one in the initial parabolic selection

For an actual PSL₂(2^f), PSU₃(2^f), or Suzuki component, the proper
intersection M⁺ ∩ L⁺ lies in the Borel over S⁺ ∩ L⁺. Every three-subgroup
of that Borel is cyclic, as follows from its concrete cyclic torus supplement.
Since L⁺ is normal and I⁺/L⁺ is a two-group, every three-subgroup of Y₊⁺S⁺
lies in this Borel. This contradicts the genuine quotient onto S₃ × S₃.

The source action is retained in the selection interface, but no further
action fact is required for this exclusion. Recognition remains the explicit
`QuotientParabolic` hypothesis, to be discharged by the parent selection proof.
All three model cases use their actual group equivalences.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Theorem C
and Remark A.2.4, printed p.33; 1.1.5(3), pp.501--502; 15.3.41, p.1138;
and the first paragraph of the final proof of 15.3.35, p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

/-- The complete rank-one branch of the parabolic selection, with recognition
explicit and every concrete Borel obstruction discharged. -/
theorem Setup.not_rank_one (d : Setup L MI Yplus S)
    {z : G} {α : MulAut L} (_a : SourceAction L S z α)
    (hp : QuotientParabolic L MI S)
    (hm : ClassificationModels.IsBenderModel (centralizerQuotientComponent L)) : False := by
  let q := centralizerQuotientMap L
  let D := centralizerQuotientComponent L
  let : D.Normal := (inferInstance : L.Normal).map q (QuotientGroup.mk'_surjective _)
  refine RankOne.no_shadow_of_borel_three_cyclic D (MI.map q) (Yplus.map q) (S.map q)
      ?_ d.quotient_local hp.proper ?_
  · change L.map q ⊔ S.map q = ⊤
    rw [← Subgroup.map_sup, d.generated]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  · intro T
    exact ⟨(RankOne.bender_borel_facts hm T).unique_maximal,
      RankOne.bender_borel_three_cyclic hm T⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
