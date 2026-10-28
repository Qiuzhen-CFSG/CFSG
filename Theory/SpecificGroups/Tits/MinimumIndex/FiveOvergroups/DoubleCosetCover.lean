module

public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Base
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.MapsChecked
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max8.Checked
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.MapsChecked
public import Theory.SpecificGroups.Tits.MinimumIndex.FiveOvergroups.DoubleCosetCover.Max4.Checked

/-!
# The max8 and max4 double-coset covers of the actual Tits group

The certificates list 14976 and 2304 right-coset representatives, each a fixed
source double-coset word times a word in the corresponding candidate subgroup.
Kernel-checked transitions under the two ATLAS generators prove that these
right cosets cover the generated group. The certified base at points 0, 1, 2
turns the finite point computations into group equalities.

These are the two coverage premises of `FiveOvergroups.coverage_of_certificates`.
They use the literal candidate generators and unchanged shared representatives,
with no maximal-subgroup catalogue or candidate-order premise.
Source: primary ATLAS Tits max4/max8 programs and the fixed candidate calculation
in `FiveOvergroups/source/`; reproducible witness generation is in
`DoubleCosetCover/source/`. GAP output supplies data, never proof assumptions.
-/

namespace Tits.MinimumIndexFiveOvergroups
open DoubleCosetCertificate MinimumIndexCandidates

/-- Every actual Atlas Tits element lies in one of the 25 fixed max8 double cosets. -/
public theorem max8_doubleCoset_cover (x : Atlas1600Group) :
    ∃ (a b : MinimumIndexCandidates.max8) (i : Fin 25),
      x = a.val * max8Rep i * b.val := by
  simpa only [MinimumIndexCandidates.max8] using
    doubleCoset_cover_of_tests max8Generators max8Rep Max8.genMaps Max8.repMaps
      Max8.genMaps_spec Max8.repMaps_spec Max8.nodes Max8.steps 0 rfl max8Rep_zero
      Max8.transitions_checked x

/-- Every actual Atlas Tits element lies in one of the seven fixed max4 double cosets. -/
public theorem max4_doubleCoset_cover (x : Atlas1600Group) :
    ∃ (a b : MinimumIndexCandidates.max4) (i : Fin 7),
      x = a.val * max4Rep i * b.val := by
  simpa only [MinimumIndexCandidates.max4] using
    doubleCoset_cover_of_tests max4Generators max4Rep Max4.genMaps Max4.repMaps
      Max4.genMaps_spec Max4.repMaps_spec Max4.nodes Max4.steps 0 rfl max4Rep_zero
      Max4.transitions_checked x

end Tits.MinimumIndexFiveOvergroups
