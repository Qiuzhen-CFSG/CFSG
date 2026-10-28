module

public import Theory.SpecificGroups.Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeWitnesses.ShortCertificates.ArithmeticData

/-!
# Certified arithmetic of the marked Sylow normal forms

Every stored fingerprint and every inverse decoding entry is checked. Existing
normal-form surjectivity then proves multiplication for arbitrary pairs, using
only two forward evaluations. There is no 2048-by-2048 multiplication-table
assumption. Word induction recovers actual seed members from positive words;
the final equation lemma uses exactly q*u = v*n with left products.

Source: Parrott (1972), section 5, p.683; the certified Atlas normal forms and
`source/README.md`. Blocks of 64 keep each kernel check small.
-/

@[expose] public section
namespace Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates

set_option Elab.async false

private theorem arithmetic_check_00 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 0 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_01 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 1 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_02 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 2 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_03 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 3 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_04 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 4 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_05 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 5 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_06 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 6 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_07 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 7 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_08 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 8 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_09 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 9 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_10 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 10 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_11 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 11 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_12 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 12 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_13 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 13 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_14 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 14 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_15 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 15 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_16 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 16 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_17 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 17 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_18 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 18 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_19 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 19 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_20 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 20 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_21 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 21 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_22 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 22 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_23 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 23 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_24 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 24 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_25 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 25 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_26 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 26 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_27 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 27 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_28 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 28 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_29 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 29 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_30 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 30 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

private theorem arithmetic_check_31 : ∀ j : Fin 64,
    arithmeticTest (blockIndex 31 j) = true := by
  apply Atlas1600OrderCertificate.allFin
  decide +kernel

theorem arithmetic_checks (n : Fin 2048) : arithmeticTest n = true := by
  have blocks : ∀ b j, arithmeticTest (blockIndex b j) = true := by
    intro b
    fin_cases b
    · exact arithmetic_check_00
    · exact arithmetic_check_01
    · exact arithmetic_check_02
    · exact arithmetic_check_03
    · exact arithmetic_check_04
    · exact arithmetic_check_05
    · exact arithmetic_check_06
    · exact arithmetic_check_07
    · exact arithmetic_check_08
    · exact arithmetic_check_09
    · exact arithmetic_check_10
    · exact arithmetic_check_11
    · exact arithmetic_check_12
    · exact arithmetic_check_13
    · exact arithmetic_check_14
    · exact arithmetic_check_15
    · exact arithmetic_check_16
    · exact arithmetic_check_17
    · exact arithmetic_check_18
    · exact arithmetic_check_19
    · exact arithmetic_check_20
    · exact arithmetic_check_21
    · exact arithmetic_check_22
    · exact arithmetic_check_23
    · exact arithmetic_check_24
    · exact arithmetic_check_25
    · exact arithmetic_check_26
    · exact arithmetic_check_27
    · exact arithmetic_check_28
    · exact arithmetic_check_29
    · exact arithmetic_check_30
    · exact arithmetic_check_31
  have hn : n = blockIndex ⟨n.val / 64, by omega⟩ ⟨n.val % 64, by omega⟩ := by
    apply Fin.ext
    simp only [blockIndex]
    omega
  rw [hn]
  exact blocks _ _

end Tits.MinimumIndex.LargeTwoOvergroups.SeedOvergroups.ExtensionObstructions.RepresentativeCertificates.ShortCertificates
