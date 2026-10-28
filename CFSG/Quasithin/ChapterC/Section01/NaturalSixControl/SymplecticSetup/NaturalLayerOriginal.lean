module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NaturalLayer
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Original
/-!
# The native moving layer at both actual source pairs

The original marked S6 source and its minimum characteristic replacement
both satisfy the common natural-layer theorem. The local SQTK hypothesis
comes from the actual source data; all other moving-layer premises have
already been discharged. These are the literal original and replacement
consumers for MS93 (3.2)(vi), printed pp.863–864.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {K : Type*} [Group K] [Finite K]
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
variable (d : NaturalSixControl.SourceData L V T) (h : IntrinsicMSPair d)
include d h
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- Actual original-J source: the native full layer is its marked module. -/
theorem SourceData.original_natural_layer :
    ⁅X R (alpha R),Ltilde R (alpha R)⁆ = U R (alpha R) ∧
      U R (alpha R) = (V.subgroupOf J).map (embedM R) :=
  (SourceData.originalSource d h).natural_moving_layer (d.sqtk.subgroup J)

/-- The same literal conclusion survives the actual characteristic replacement. -/
theorem SourceData.reduced_natural_layer
    (c : CharacteristicReduction (L.subgroupOf J) R) :
    ⁅X c.radical (alpha c.radical),Ltilde c.radical (alpha c.radical)⁆ =
      U c.radical (alpha c.radical) ∧
      U c.radical (alpha c.radical) =
        ((V.subgroupOf J).subgroupOf c.overgroup).map (embedM c.radical) :=
  ((SourceData.originalSource d h).reduce c).natural_moving_layer
    ((d.sqtk.subgroup J).subgroup c.overgroup)

#print axioms SourceData.original_natural_layer
#print axioms SourceData.reduced_natural_layer
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
