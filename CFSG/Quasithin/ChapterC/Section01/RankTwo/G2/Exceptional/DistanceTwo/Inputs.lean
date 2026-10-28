module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Inputs

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# The two stages of the G₂ critical-distance exclusion

MS93 (3.8) first verifies (2.3)(c,d) from the G₂ row of (3.2), then
excludes the resulting distance-four configuration by studying the actual
radius-two group. These contracts separate those arguments. They impose no
bound on the whole core and do not identify the radius-two group with it.

The auxiliary subgroup is retained as a witness on the actual first edge of
a critical path. In the printed G₂ argument its initial choice is
C_{U_alpha}(Q_2), with Q_2 the parabolic two-core from the source, not the
holomorph kernel T_beta. No such identification is built into these contracts.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*,
(2.3), (3.2)(vii), (3.8), printed pp.857--859,863--866,877--879.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.G2Exceptional
open ChapterC BinaryMS.MS93
namespace Reconstruction.DistanceTwo
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}

local notation "T" => R.subgroupOf (L ⊔ R)

/-- The literal local hypotheses (c,d) of MS93 (2.3). The critical-distance
conclusion of that theorem is not part of this record. -/
structure LocalControl (h : Pair KnownSimple.IsKnownSimple L R) : Prop where
  commutator : CriticalCriterion.CommutatorControl T (geometry h)
  auxiliary : ∀ a (ha : color T a = false) a',
    CriticalPair T a a' ((geometry h).exists_critical a ha) →
    ∀ t, Adjacent T a t →
      (cosetGraph T).dist t a' + 1 = (cosetGraph T).dist a a' →
      ∃ A, CriticalCriterion.EdgeWitness T (geometry h) a t A

/-- The first paragraph of MS93 (3.8) specialized to the G₂ initial module. -/
def LocalControlInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
    (h : Pair KnownSimple.IsKnownSimple L R),
    ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    2 < (geometry h).b (R.subgroupOf (L ⊔ R)) → LocalControl h

/-- The remaining radius-two argument at distance four. It may consume the
local hypotheses while their independent producer is still being proved. -/
def DistanceFourExclusionInput : Prop :=
  ∀ (J : Type u) [Group J] [Finite J] (L R : Subgroup J)
    (h : Pair KnownSimple.IsKnownSimple L R),
    ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) →
    (geometry h).b (R.subgroupOf (L ⊔ R)) = 4 → LocalControl h → False

end Reconstruction.DistanceTwo
end CFSG.Quasithin.ChapterC.G2Exceptional
