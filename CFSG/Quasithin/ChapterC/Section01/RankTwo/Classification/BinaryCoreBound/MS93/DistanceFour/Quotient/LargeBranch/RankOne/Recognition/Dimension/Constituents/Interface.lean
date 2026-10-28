module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Head

/-!
# The two literal SL3(2) factors needed in the starred calculation

The intermediate conclusion on the last line of printed p.911 is a natural
submodule with natural quotient in the actual starred module. Either natural
orientation is permitted for each factor. No splitting or arbitrary change
of the supplied quotient action is built into this interface.

The dimension conclusion follows by adding the two factor dimensions.
Producing these factors from Estimates, and constructing the two natural
rank-one copies from them, are separate obligations of the constituent proof.
This file does not assert either source implication.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), printed pp.911--912.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
open AbelianCore.QuotientRecognition.ExtensionControl
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Actual constituent coordinates on a submodule and its literal quotient.
This is an intermediate conclusion to be proved from the source estimates. -/
structure TwoNaturalFactors (d : LayerModule source (V R (alpha R))) where
  lower : Subrepresentation (starRepresentation (geometry := geometry) d).toRepresentation
  lower_natural : NaturalOrDual lower.toRepresentation
  upper_natural : NaturalOrDual lower.quotientRepresentation

/-- The two actual three-dimensional factors give starred dimension six. -/
theorem TwoNaturalFactors.finrank_eq_six
    {d : LayerModule source (V R (alpha R))}
    (h : TwoNaturalFactors (geometry := geometry) d) :
    Module.finrank (ZMod 2) (d.subspace (VStar R geometry (alpha R) (beta R))) = 6 := by
  have hl := h.lower_natural.finrank
  have hu := h.upper_natural.finrank
  have hadd := h.lower.toSubmodule.finrank_quotient_add_finrank
  change Module.finrank (ZMod 2) (h.lower.toSubmodule) = 3 at hl
  change Module.finrank (ZMod 2) (_ ⧸ h.lower.toSubmodule) = 3 at hu
  change Module.finrank (ZMod 2) (_ ⧸ h.lower.toSubmodule) +
    Module.finrank (ZMod 2) h.lower.toSubmodule =
      Module.finrank (ZMod 2) (d.subspace (VStar R geometry (alpha R) (beta R))) at hadd
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
