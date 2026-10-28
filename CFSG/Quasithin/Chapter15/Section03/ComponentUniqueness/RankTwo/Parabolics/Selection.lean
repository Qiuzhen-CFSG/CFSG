module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.QuotientModels
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.OrderObstruction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.RankOneExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.SmallModelExclusion
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.LargerFieldBorel

/-!
# Assembly of the initial parabolic alternatives

The source action catalogue is transported to the actual centralizer-quotient
component. The maximal invariant parabolic recognition and concrete model
inspections exclude every rank-one and small-derived case. In each surviving
larger-field case, the quotient Borel containment lifts to a genuinely marked
Borel in L, including when L has a nontrivial center.

The theorem `alternatives` discharges all the local inspections from `Setup`
and `SourceAction`, the preceding source inputs of 15.3.39--42 and
1.1.5(3)(a)--(c). It proves the initial alternatives on p.1139; the subsequent
larger-field contradiction and binary parabolic recognition are separate steps.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), first
paragraph of the final proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection

variable {G : Type*} [Group G] [Finite G]
variable {L MI Yplus S : Subgroup G} [L.Normal]

/-- Conditional assembly with all three geometric obligations explicit.
The source-theorem owner must construct each premise before claiming the
parabolic selection on p.1139. The catalogue and upstairs Borel are proved here. -/
theorem alternatives_of_local_inspections (d : Setup L MI Yplus S)
    {z : G} {α : MulAut L} (a : SourceAction L S z α)
    (hp : QuotientParabolic L MI S)
    (hexclude : QuotientParabolic L MI S →
      ExceptionalModel (centralizerQuotientComponent L) → False)
    (hborel : QuotientParabolic L MI S →
      LargerFieldRankTwoModel (centralizerQuotientComponent L) →
      Yplus.map (centralizerQuotientMap L) ≤
        sylowBorel (centralizerQuotientComponent L) (S.map (centralizerQuotientMap L))) :
    ParabolicAlternatives L Yplus S := by
  let := d.quasisimple
  rcases component_model_cases L a.alternatives with hsmall | hlarge | hexceptional
  · exact Or.inl hsmall
  · obtain ⟨P, hP⟩ := d.sylow
    exact Or.inr ⟨hlarge, sylowBorel L S, borelOverSylow L S P hP,
      le_borel_of_image_le L S P hP d.yplus_le (hborel hp hlarge)⟩
  · exact (hexclude hp hexceptional).elim

/-- Every exceptional case retained by the complete action catalogue is excluded
by the source local configuration and the recognized parabolic. The model
equivalences, including the separate A₆ case, are used without family tags. -/
theorem Setup.not_exceptional (d : Setup L MI Yplus S)
    {z : G} {α : MulAut L} (a : SourceAction L S z α)
    (hp : QuotientParabolic L MI S)
    (hm : ExceptionalModel (centralizerQuotientComponent L)) : False := by
  cases hm with
  | rank_one hm => exact d.not_rank_one a hp hm
  | linear_three_two hm => exact d.not_linear_three_two hm
  | triality_two hm => exact d.not_triality_two hm
  | symplectic_derived hm => exact d.not_symplectic_derived hp hm
  | g2_derived hm => exact d.not_g2_derived hm
  | tits hm => exact d.not_tits hp hm
  | alternating_six hm => exact d.not_alternating_six hp hm

/-- The initial parabolic alternatives in the final proof of 15.3.35, p.1139.
Only the preceding component, local and action inputs remain: recognition,
exceptional-model exclusion and larger-field Borel containment are all proved.
The Borel is in the original L and is marked by an actual Sylow two-subgroup. -/
theorem alternatives (d : Setup L MI Yplus S)
    {z : G} {α : MulAut L} (a : SourceAction L S z α) :
    ParabolicAlternatives L Yplus S := by
  exact alternatives_of_local_inspections d a (quotientParabolic d a)
    (fun hp => d.not_exceptional a hp) (largerField_borel d)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection
