module
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.WordGeometry.Certificates
/-!
# Bounded kernel certificates for the complete cover enumeration

The 1080 original products are checked in blocks of 24. Each block certifies its
matrix keys and the consecutive strict inequalities in the sorted witness list.
Separate, sequential declarations bound reduction memory and elaboration cost;
no global heartbeat or thread limit is changed. `Enumeration` uses these checks
to prove injectivity and applies the independently proved cover order.

Source application: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464.
See `source/README.md` for provenance and measured certificate costs.
-/

@[expose] public section

namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry

def BlockCheck (b : Fin 45) : Prop := ∀ c : Fin 24,
  let n := blockIndex b c
  matrixKey (productMatrix (sortedIndex n)) = sortedKey n ∧
    ∀ h : n.val + 1 < 1080, sortedKey n < sortedKey ⟨n.val + 1,h⟩

-- Serialize the measured finite reductions; each block has its own elaboration budget.
set_option Elab.async false

private theorem check_00 : BlockCheck 0 := by
  unfold BlockCheck
  decide +kernel

private theorem check_01 : BlockCheck 1 := by
  unfold BlockCheck
  decide +kernel

private theorem check_02 : BlockCheck 2 := by
  unfold BlockCheck
  decide +kernel

private theorem check_03 : BlockCheck 3 := by
  unfold BlockCheck
  decide +kernel

private theorem check_04 : BlockCheck 4 := by
  unfold BlockCheck
  decide +kernel

private theorem check_05 : BlockCheck 5 := by
  unfold BlockCheck
  decide +kernel

private theorem check_06 : BlockCheck 6 := by
  unfold BlockCheck
  decide +kernel

private theorem check_07 : BlockCheck 7 := by
  unfold BlockCheck
  decide +kernel

private theorem check_08 : BlockCheck 8 := by
  unfold BlockCheck
  decide +kernel

private theorem check_09 : BlockCheck 9 := by
  unfold BlockCheck
  decide +kernel

private theorem check_10 : BlockCheck 10 := by
  unfold BlockCheck
  decide +kernel

private theorem check_11 : BlockCheck 11 := by
  unfold BlockCheck
  decide +kernel

private theorem check_12 : BlockCheck 12 := by
  unfold BlockCheck
  decide +kernel

private theorem check_13 : BlockCheck 13 := by
  unfold BlockCheck
  decide +kernel

private theorem check_14 : BlockCheck 14 := by
  unfold BlockCheck
  decide +kernel

private theorem check_15 : BlockCheck 15 := by
  unfold BlockCheck
  decide +kernel

private theorem check_16 : BlockCheck 16 := by
  unfold BlockCheck
  decide +kernel

private theorem check_17 : BlockCheck 17 := by
  unfold BlockCheck
  decide +kernel

private theorem check_18 : BlockCheck 18 := by
  unfold BlockCheck
  decide +kernel

private theorem check_19 : BlockCheck 19 := by
  unfold BlockCheck
  decide +kernel

private theorem check_20 : BlockCheck 20 := by
  unfold BlockCheck
  decide +kernel

private theorem check_21 : BlockCheck 21 := by
  unfold BlockCheck
  decide +kernel

private theorem check_22 : BlockCheck 22 := by
  unfold BlockCheck
  decide +kernel

private theorem check_23 : BlockCheck 23 := by
  unfold BlockCheck
  decide +kernel

private theorem check_24 : BlockCheck 24 := by
  unfold BlockCheck
  decide +kernel

private theorem check_25 : BlockCheck 25 := by
  unfold BlockCheck
  decide +kernel

private theorem check_26 : BlockCheck 26 := by
  unfold BlockCheck
  decide +kernel

private theorem check_27 : BlockCheck 27 := by
  unfold BlockCheck
  decide +kernel

private theorem check_28 : BlockCheck 28 := by
  unfold BlockCheck
  decide +kernel

private theorem check_29 : BlockCheck 29 := by
  unfold BlockCheck
  decide +kernel

private theorem check_30 : BlockCheck 30 := by
  unfold BlockCheck
  decide +kernel

private theorem check_31 : BlockCheck 31 := by
  unfold BlockCheck
  decide +kernel

private theorem check_32 : BlockCheck 32 := by
  unfold BlockCheck
  decide +kernel

private theorem check_33 : BlockCheck 33 := by
  unfold BlockCheck
  decide +kernel

private theorem check_34 : BlockCheck 34 := by
  unfold BlockCheck
  decide +kernel

private theorem check_35 : BlockCheck 35 := by
  unfold BlockCheck
  decide +kernel

private theorem check_36 : BlockCheck 36 := by
  unfold BlockCheck
  decide +kernel

private theorem check_37 : BlockCheck 37 := by
  unfold BlockCheck
  decide +kernel

private theorem check_38 : BlockCheck 38 := by
  unfold BlockCheck
  decide +kernel

private theorem check_39 : BlockCheck 39 := by
  unfold BlockCheck
  decide +kernel

private theorem check_40 : BlockCheck 40 := by
  unfold BlockCheck
  decide +kernel

private theorem check_41 : BlockCheck 41 := by
  unfold BlockCheck
  decide +kernel

private theorem check_42 : BlockCheck 42 := by
  unfold BlockCheck
  decide +kernel

private theorem check_43 : BlockCheck 43 := by
  unfold BlockCheck
  decide +kernel

private theorem check_44 : BlockCheck 44 := by
  unfold BlockCheck
  decide +kernel

theorem block_checks (b : Fin 45) : BlockCheck b := by
  fin_cases b
  · exact check_00
  · exact check_01
  · exact check_02
  · exact check_03
  · exact check_04
  · exact check_05
  · exact check_06
  · exact check_07
  · exact check_08
  · exact check_09
  · exact check_10
  · exact check_11
  · exact check_12
  · exact check_13
  · exact check_14
  · exact check_15
  · exact check_16
  · exact check_17
  · exact check_18
  · exact check_19
  · exact check_20
  · exact check_21
  · exact check_22
  · exact check_23
  · exact check_24
  · exact check_25
  · exact check_26
  · exact check_27
  · exact check_28
  · exact check_29
  · exact check_30
  · exact check_31
  · exact check_32
  · exact check_33
  · exact check_34
  · exact check_35
  · exact check_36
  · exact check_37
  · exact check_38
  · exact check_39
  · exact check_40
  · exact check_41
  · exact check_42
  · exact check_43
  · exact check_44

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification.WordGeometry
