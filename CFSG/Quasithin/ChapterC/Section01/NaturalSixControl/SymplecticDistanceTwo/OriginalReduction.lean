module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.NaturalReduction
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NaturalLayerOriginal

/-!
# Original C.1.37 applications of the symplectic distance-two reduction

Both applications use the actual component--Baumann product and its genuine
characteristic replacement. The specified S6 projection, fixed vector and
natural coordinates remain those of the original source. All central-layer
and edge-centralizer inputs have been discharged upstream. Only the stated
critical-distance case and its remaining symplectic calculation are open.

Source: MS93 (3.6), printed pp.870–871, applied in C.1.37.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {K : Type*} [Group K] [Finite K]
  {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L V T) (h : IntrinsicMSPair d)
include d h
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The actual original-J source enters the two branches of (3.6). -/
theorem SourceData.original_distance_two_reduction
    (hb : (SourceData.originalSource d h).geometry.b R = 2) :
    core R (alpha R) = (V.subgroupOf J).map (embedM R) ∨
      ∀ c, CriticalPair R (alpha R) c
        ((SourceData.originalSource d h).geometry.exists_critical (alpha R) rfl) →
        ¬ ⁅Q R (alpha R),Z R c⁆ ≤
          ⁅Q R (alpha R),X R c ⊓ Q R (alpha R)⁆ ⊔ ⁅X R (alpha R),X R c⁆ :=
  (SourceData.originalSource d h).distance_two_core_or_critical (d.sqtk.subgroup J) hb

/-- The characteristic replacement enters precisely the same two branches,
with its original module restriction and free-amalgam embedding. -/
theorem SourceData.reduced_distance_two_reduction
    (c : CharacteristicReduction (L.subgroupOf J) R)
    (hb : ((SourceData.originalSource d h).reduce c).geometry.b c.radical = 2) :
    core c.radical (alpha c.radical) =
        ((V.subgroupOf J).subgroupOf c.overgroup).map (embedM c.radical) ∨
      ∀ a, CriticalPair c.radical (alpha c.radical) a
        (((SourceData.originalSource d h).reduce c).geometry.exists_critical
          (alpha c.radical) rfl) →
        ¬ ⁅Q c.radical (alpha c.radical),Z c.radical a⁆ ≤
          ⁅Q c.radical (alpha c.radical),X c.radical a ⊓ Q c.radical (alpha c.radical)⁆ ⊔
            ⁅X c.radical (alpha c.radical),X c.radical a⁆ :=
  ((SourceData.originalSource d h).reduce c).distance_two_core_or_critical
    ((d.sqtk.subgroup J).subgroup c.overgroup) hb

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
