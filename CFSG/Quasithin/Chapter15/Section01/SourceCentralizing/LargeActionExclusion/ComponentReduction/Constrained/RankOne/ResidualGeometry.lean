module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Geometry

/-!
# The source two-residual of the orbit Borel

Clause (ii) of 15.1.21 moves O²(B), not O₂(B). This companion to the
legacy geometry record uses the literal image of the two-residual under
B's inclusion. The actual S-orbit B remains in place throughout. The
legacy record and its conditional consumers retain their public types.

Source: Aschbacher--Smith 15.1.21(ii), printed p.1098, PDF page1115.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The embedded two-residual of the actual orbit Borel. -/
def rankOneBorelResidual (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (pResidual 2 d.rankOneBorelClosure).map d.rankOneBorelClosure.subtype

/-- The genuine exceptional source conclusion, separate from the legacy
`RankOneExceptionalGeometry.core_moved` condition. -/
structure RankOneExceptionalResidualGeometry (d : CaseIComponentData T M Mc V) : Prop where
  block : ChapterC.IsAlternatingBlock d.L 5
  residual_moved : ⁅d.rankOneBorelResidual, elementaryAbelianMaxJ d.S⁆ =
    d.rankOneBorelResidual

/-- The row's moved-component identity implies relative normalization by
J(S); it does not imply normalization by all of S. -/
theorem ConstrainedRankOneAlternative.thompson_normalizes
    {d : CaseIComponentData T M Mc V} (r : d.ConstrainedRankOneAlternative) :
    elementaryAbelianMaxJ d.S ≤ normalizer (d.L : Set G) :=
  le_normalizer_iff_commutator_le_left.mpr r.thompson.le

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
