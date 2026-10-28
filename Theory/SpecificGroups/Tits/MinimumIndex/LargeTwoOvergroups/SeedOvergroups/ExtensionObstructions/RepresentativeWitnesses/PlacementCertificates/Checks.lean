module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.PlacementCertificates.Data

/-!
# Kernel verification of rectangular placement data

The Boolean certificates are reduced in Lean's kernel. The anchor-and-ratio
lemma supplies every literal representative, and generator membership supplies
seed containment. The masks certify only which already proved rectangles to use.
Source: the literal Parrott (1972), §5, p.683 words and the adjacent emitter.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.Placement

set_option Elab.async false

private theorem certificates_checked_00 :
    (certificates00).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_01 :
    (certificates01).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_02 :
    (certificates02).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_03 :
    (certificates03).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_04 :
    (certificates04).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_05 :
    (certificates05).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_06 :
    (certificates06).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_07 :
    (certificates07).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_08 :
    (certificates08).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_09 :
    (certificates09).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_10 :
    (certificates10).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_11 :
    (certificates11).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_12 :
    (certificates12).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_13 :
    (certificates13).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_14 :
    (certificates14).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_15 :
    (certificates15).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_16 :
    (certificates16).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_17 :
    (certificates17).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_18 :
    (certificates18).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_19 :
    (certificates19).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_20 :
    (certificates20).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_21 :
    (certificates21).all certificateTest = true := by
  decide +kernel

private theorem certificates_checked_22 :
    (certificates22).all certificateTest = true := by
  decide +kernel

theorem certificates_checked (t : Fin 23) :
    (certificates t).all certificateTest = true := by
  fin_cases t
  · exact certificates_checked_00
  · exact certificates_checked_01
  · exact certificates_checked_02
  · exact certificates_checked_03
  · exact certificates_checked_04
  · exact certificates_checked_05
  · exact certificates_checked_06
  · exact certificates_checked_07
  · exact certificates_checked_08
  · exact certificates_checked_09
  · exact certificates_checked_10
  · exact certificates_checked_11
  · exact certificates_checked_12
  · exact certificates_checked_13
  · exact certificates_checked_14
  · exact certificates_checked_15
  · exact certificates_checked_16
  · exact certificates_checked_17
  · exact certificates_checked_18
  · exact certificates_checked_19
  · exact certificates_checked_20
  · exact certificates_checked_21
  · exact certificates_checked_22

private theorem generators_checked_00 :
    (generatorIndices 0).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 0) = true := by
  decide +kernel

private theorem generators_checked_01 :
    (generatorIndices 1).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 1) = true := by
  decide +kernel

private theorem generators_checked_02 :
    (generatorIndices 2).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 2) = true := by
  decide +kernel

private theorem generators_checked_03 :
    (generatorIndices 3).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 3) = true := by
  decide +kernel

private theorem generators_checked_04 :
    (generatorIndices 4).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 4) = true := by
  decide +kernel

private theorem generators_checked_05 :
    (generatorIndices 5).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 5) = true := by
  decide +kernel

private theorem generators_checked_06 :
    (generatorIndices 6).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 6) = true := by
  decide +kernel

private theorem generators_checked_07 :
    (generatorIndices 7).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 7) = true := by
  decide +kernel

private theorem generators_checked_08 :
    (generatorIndices 8).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 8) = true := by
  decide +kernel

private theorem generators_checked_09 :
    (generatorIndices 9).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 9) = true := by
  decide +kernel

private theorem generators_checked_10 :
    (generatorIndices 10).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 10) = true := by
  decide +kernel

private theorem generators_checked_11 :
    (generatorIndices 11).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 11) = true := by
  decide +kernel

private theorem generators_checked_12 :
    (generatorIndices 12).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 12) = true := by
  decide +kernel

private theorem generators_checked_13 :
    (generatorIndices 13).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 13) = true := by
  decide +kernel

private theorem generators_checked_14 :
    (generatorIndices 14).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 14) = true := by
  decide +kernel

private theorem generators_checked_15 :
    (generatorIndices 15).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 15) = true := by
  decide +kernel

private theorem generators_checked_16 :
    (generatorIndices 16).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 16) = true := by
  decide +kernel

private theorem generators_checked_17 :
    (generatorIndices 17).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 17) = true := by
  decide +kernel

private theorem generators_checked_18 :
    (generatorIndices 18).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 18) = true := by
  decide +kernel

private theorem generators_checked_19 :
    (generatorIndices 19).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 19) = true := by
  decide +kernel

private theorem generators_checked_20 :
    (generatorIndices 20).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 20) = true := by
  decide +kernel

private theorem generators_checked_21 :
    (generatorIndices 21).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 21) = true := by
  decide +kernel

private theorem generators_checked_22 :
    (generatorIndices 22).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 22) = true := by
  decide +kernel

private theorem generators_checked_23 :
    (generatorIndices 23).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 23) = true := by
  decide +kernel

private theorem generators_checked_24 :
    (generatorIndices 24).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 24) = true := by
  decide +kernel

private theorem generators_checked_25 :
    (generatorIndices 25).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 25) = true := by
  decide +kernel

private theorem generators_checked_26 :
    (generatorIndices 26).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 26) = true := by
  decide +kernel

private theorem generators_checked_27 :
    (generatorIndices 27).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 27) = true := by
  decide +kernel

private theorem generators_checked_28 :
    (generatorIndices 28).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 28) = true := by
  decide +kernel

private theorem generators_checked_29 :
    (generatorIndices 29).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 29) = true := by
  decide +kernel

private theorem generators_checked_30 :
    (generatorIndices 30).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 30) = true := by
  decide +kernel

private theorem generators_checked_31 :
    (generatorIndices 31).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 31) = true := by
  decide +kernel

private theorem generators_checked_32 :
    (generatorIndices 32).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 32) = true := by
  decide +kernel

private theorem generators_checked_33 :
    (generatorIndices 33).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 33) = true := by
  decide +kernel

private theorem generators_checked_34 :
    (generatorIndices 34).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 34) = true := by
  decide +kernel

private theorem generators_checked_35 :
    (generatorIndices 35).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 35) = true := by
  decide +kernel

private theorem generators_checked_36 :
    (generatorIndices 36).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 36) = true := by
  decide +kernel

private theorem generators_checked_37 :
    (generatorIndices 37).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) 37) = true := by
  decide +kernel

theorem generators_checked (j : Fin 38) :
    (generatorIndices j).all (fun n => Fast.test (Geometry.RepresentativeProducts.normalForm n) j) = true := by
  fin_cases j
  · exact generators_checked_00
  · exact generators_checked_01
  · exact generators_checked_02
  · exact generators_checked_03
  · exact generators_checked_04
  · exact generators_checked_05
  · exact generators_checked_06
  · exact generators_checked_07
  · exact generators_checked_08
  · exact generators_checked_09
  · exact generators_checked_10
  · exact generators_checked_11
  · exact generators_checked_12
  · exact generators_checked_13
  · exact generators_checked_14
  · exact generators_checked_15
  · exact generators_checked_16
  · exact generators_checked_17
  · exact generators_checked_18
  · exact generators_checked_19
  · exact generators_checked_20
  · exact generators_checked_21
  · exact generators_checked_22
  · exact generators_checked_23
  · exact generators_checked_24
  · exact generators_checked_25
  · exact generators_checked_26
  · exact generators_checked_27
  · exact generators_checked_28
  · exact generators_checked_29
  · exact generators_checked_30
  · exact generators_checked_31
  · exact generators_checked_32
  · exact generators_checked_33
  · exact generators_checked_34
  · exact generators_checked_35
  · exact generators_checked_36
  · exact generators_checked_37

private theorem generator_routes (i : Fin 122) :
    (placeIds i).all (fun j => (seedIndices i).all fun n => decide (n ∈ generatorIndices j)) = true := by
  revert i
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

theorem seed_le_place (i : Fin 122) (j : Fin 38) (hj : j ∈ placeIds i) :
    seed i ≤ place j := by
  apply seed_le_of_tests
  intro n hn
  have hj' := List.all_eq_true.mp (generator_routes i) j hj
  have hn' : n ∈ generatorIndices j := by
    simpa only [decide_eq_true_eq] using List.all_eq_true.mp hj' n hn
  exact List.all_eq_true.mp (generators_checked j) n hn'

theorem mask_coverage (i : Fin 122) :
    (placeMasks (placeSelector i)) &&& coverMask i = placeMasks (placeSelector i) := by
  revert i
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.Placement
