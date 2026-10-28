module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Frattini

/-!+# Literal geometry for the constrained rank-one argument

The Borel of the S-orbit is the S-conjugate span of M_L. Its containment
in M_Z follows from the original T-normalization, without assuming that
S normalizes L. The remaining Thompson/Baumann and automorphism facts are
stated as conclusion contracts for the model proofs, not asserted here.

The exceptional contract concerns the A₅ permutation block. The ordinary
group L₂(4) also occurs in 15.1.21(ii), but the natural L₂(4)-block belongs
to the other branch. The prime actor retains the actual local normalizer,
the set product SY=YS, and the original moving commutator.
Source: Aschbacher--Smith 15.1.21, printed pp.1097--1098.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- The literal orbit Borel, once M_L is identified as the Borel of L. -/
def rankOneBorelClosure (d : CaseIComponentData T M Mc V) : Subgroup G :=
  conjugateSpanBy d.ML d.S

theorem PreExclusionSource.rankOneBorelClosure_le
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p) : d.rankOneBorelClosure ≤ d.MZ :=
  conjugateSpanBy_le d.ML_le_MZ (d.S_le_T.trans s.sylow_normalizes_MZ)

theorem sylow_normalizes_rankOneBorelClosure (d : CaseIComponentData T M Mc V) :
    d.S ≤ normalizer (d.rankOneBorelClosure : Set G) :=
  le_normalizer_conjugateSpanBy d.ML d.S

/-- Model conclusions used in case (i); their proof is not part of this record. -/
structure RankOneBorelGeometry (d : CaseIComponentData T M Mc V) : Prop where
  perfect : IsPPerfect 2 d.rankOneBorelClosure
  thompson : d.rankOneBorelClosure ≤ normalizer (elementaryAbelianMaxJ d.S : Set G)
  centralizers : d.S ⊓ centralizer (d.rankOneBorelClosure : Set G) ≤
    d.S ⊓ centralizer (d.L : Set G)

/-- The block clause of case (ii), with the actual embedded two-core. -/
structure RankOneExceptionalGeometry (d : CaseIComponentData T M Mc V) : Prop where
  block : ChapterC.IsAlternatingBlock d.L 5
  core_moved : ⁅d.rankOneBorelClosure.pCoreIn 2, elementaryAbelianMaxJ d.S⁆ =
    d.rankOneBorelClosure.pCoreIn 2

/-- The Frattini actor required by both the ordinary and constrained proofs.
This is a construction target; no existence is assumed in the source data. -/
structure RankOnePrimeActor (d : CaseIComponentData T M Mc V) (p : ℕ)
    (Y : Subgroup G) : Prop where
  prime_group : IsPGroup p Y
  normalizer_le : Y ≤ d.rankOneThompsonNormalizer
  permutes : (d.S : Set G) * (Y : Set G) = (Y : Set G) * (d.S : Set G)
  moves : ⁅⁅V, (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆, Y⁆ =
    ⁅V, (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
