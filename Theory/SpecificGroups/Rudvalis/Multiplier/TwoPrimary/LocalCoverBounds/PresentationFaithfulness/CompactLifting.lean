module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations000
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations008
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations016
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations024
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations032
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations040
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations048
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations056
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations064
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations072
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations080
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations088
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations096
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations104
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations112
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations120
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations128
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations136
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations144
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Relations152
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.PresentationFaithfulness.CompactLifting.Generation

/-!
# Compact relations and generation for the literal Rudvalis max4 edge group

All 325 elementary eliminations are certified from original raw relations by
acyclic substitution, inversion, conjugation and free cancellation. The same
rules certify all 159 frozen compact relators and explicit expansions of all
336 raw edges in the eleven retained edges. No order bound or model identity
is used.

Source: the original seven marked max4 words supporting Aschbacher--Smith
I.1.3(1), printed p.407; see `CompactLifting/source/README.md`.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness
open Subgroup.CosetWordCertificate CompactReplay

/-- All frozen compact relators hold on their prescribed raw edge images. -/
theorem compactRelator_eval (r : Fin 159) : eval compactImage (compactRelator r) = 1 := by
  by_cases h8 : r.val < 8
  · exact Relations000.holds r (by omega) h8
  by_cases h16 : r.val < 16
  · exact Relations008.holds r (by omega) h16
  by_cases h24 : r.val < 24
  · exact Relations016.holds r (by omega) h24
  by_cases h32 : r.val < 32
  · exact Relations024.holds r (by omega) h32
  by_cases h40 : r.val < 40
  · exact Relations032.holds r (by omega) h40
  by_cases h48 : r.val < 48
  · exact Relations040.holds r (by omega) h48
  by_cases h56 : r.val < 56
  · exact Relations048.holds r (by omega) h56
  by_cases h64 : r.val < 64
  · exact Relations056.holds r (by omega) h64
  by_cases h72 : r.val < 72
  · exact Relations064.holds r (by omega) h72
  by_cases h80 : r.val < 80
  · exact Relations072.holds r (by omega) h80
  by_cases h88 : r.val < 88
  · exact Relations080.holds r (by omega) h88
  by_cases h96 : r.val < 96
  · exact Relations088.holds r (by omega) h96
  by_cases h104 : r.val < 104
  · exact Relations096.holds r (by omega) h104
  by_cases h112 : r.val < 112
  · exact Relations104.holds r (by omega) h112
  by_cases h120 : r.val < 120
  · exact Relations112.holds r (by omega) h120
  by_cases h128 : r.val < 128
  · exact Relations120.holds r (by omega) h128
  by_cases h136 : r.val < 136
  · exact Relations128.holds r (by omega) h136
  by_cases h144 : r.val < 144
  · exact Relations136.holds r (by omega) h144
  by_cases h152 : r.val < 152
  · exact Relations144.holds r (by omega) h152
  exact Relations152.holds r (by omega) r.isLt

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.PresentationFaithfulness
