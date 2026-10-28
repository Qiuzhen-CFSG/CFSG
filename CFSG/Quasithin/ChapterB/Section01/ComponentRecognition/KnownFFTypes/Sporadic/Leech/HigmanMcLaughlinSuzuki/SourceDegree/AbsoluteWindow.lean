module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.Inputs
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup.RationalFusion
public import Theory.Representation.BinaryCoprimeDegree.RationalExtraspecial
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.Contracts

/-!
# The lower endpoint and conditional assembly of the HS absolute degree window

The actual degree-100 HS carrier contains an extraspecial group of order 125
whose nonidentity central elements are conjugate in HS. Over an algebraic
closure, the four nontrivial central eigenvalues each have multiplicity at
least five. Scalar extension preserves dimension and faithfulness, giving
degree at least twenty over every characteristic-two coefficient field.

The exact restriction calculation in `FiveCenter` gives dimension f + 20a,
where f is the actual center's fixed dimension and a is positive. The two
remaining calculations are fixed-point-freeness of that center in the window
and exclusion of absolute degree forty. Their conditional assembly below uses
the literal subgroup restriction and keeps both premises explicit. This module
does not assert `absoluteDegreeWindow` or the full book theorem.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 5.1,
HS paragraph on author-preprint p.16; Aschbacher--Smith K.4, printed p.457.
The corrected Hiss--Malle table lists degree twenty and then degree fifty-six
in characteristic two. The present proof supplies the lower endpoint by a
local subgroup calculation, rather than treating the table as a premise.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims

universe v

/-- Every faithful characteristic-two action of the literal HS carrier has
degree at least twenty. Finiteness of the coefficient field, simplicity, and
absolute irreducibility are unnecessary for this lower endpoint. -/
theorem twenty_le_finrank
    {K W : Type*} [Field K] [CharP K 2]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K KnownSimple.SporadicName.hs.Carrier W)
    (hf : Function.Injective τ) : 20 ≤ Module.finrank K W := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Finite KnownSimple.SporadicName.hs.Carrier :=
    inferInstanceAs (Finite _root_.Sporadic.LeechRelated.HS.Carrier)
  exact Representation.BinaryCoprimeDegree.finrank_ge_of_rational_extraspecial
    (by decide : 5 ≠ 2) τ hf
    _root_.Sporadic.LeechRelated.HS.FiveSubgroup.RationalFusion.rational_five_subgroup

/-- Assembly of the actual degree window from the two remaining representation
calculations. The extraspecial multiplicity calculation is already discharged;
the fixed-space and absolute degree-forty premises still need their producers. -/
theorem absoluteDegreeWindow_of_fiveCenter_of_forty_excluded
    (hfixed : AbsoluteWindow.FiveCenterFixedFreeInWindow.{v})
    (hforty : AbsoluteWindow.FixedFreeAbsoluteDegreeFortyExcluded.{v}) :
    AbsoluteDegreeWindow.{v} := by
  intro hs K _ _ _ W _ _ _ τ hf hi hd
  have hfix := hfixed hs K W τ hf hi hd
  have he := AbsoluteWindow.finrank_eq_twenty_or_forty_of_fiveCenter_fixed_eq_bot
    τ hf hd hfix
  exact he.resolve_right (hforty hs K W τ hf hi hfix)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
