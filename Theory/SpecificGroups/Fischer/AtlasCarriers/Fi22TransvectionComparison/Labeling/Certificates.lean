module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Labeling.Data

/-!
# Finite certificates for Fi22 unitary coordinates

Checked base-four encoding, validity of every fixed-point row, and coverage of
every normalized isotropic vector give mutually inverse coordinate tables.
Each kernel certificate covers at most 256 inputs to bound reduction memory.
`Labeling.Coordinates` assembles these facts into the actual projective bijection.

Source: ATLAS F22G1-p3510B0 and GLS3 Table 5.3t,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
open KernelCertificate

private def encodingCheck (n : Nat) : Bool := decide (encodeVector (vector n) = n)
set_option maxRecDepth 2048 in
private theorem encodingCheck0 : BitNetwork.check encodingCheck 0 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck1 : BitNetwork.check encodingCheck 256 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck2 : BitNetwork.check encodingCheck 512 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck3 : BitNetwork.check encodingCheck 768 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck4 : BitNetwork.check encodingCheck 1024 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck5 : BitNetwork.check encodingCheck 1280 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck6 : BitNetwork.check encodingCheck 1536 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck7 : BitNetwork.check encodingCheck 1792 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck8 : BitNetwork.check encodingCheck 2048 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck9 : BitNetwork.check encodingCheck 2304 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck10 : BitNetwork.check encodingCheck 2560 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck11 : BitNetwork.check encodingCheck 2816 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck12 : BitNetwork.check encodingCheck 3072 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck13 : BitNetwork.check encodingCheck 3328 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck14 : BitNetwork.check encodingCheck 3584 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem encodingCheck15 : BitNetwork.check encodingCheck 3840 256 = true := by
  decide +kernel

private theorem encodingCheck_all : BitNetwork.check encodingCheck 0 4096 = true :=
  (BitNetwork.check_append encodingCheck 0 256 3840 encodingCheck0
    (BitNetwork.check_append encodingCheck 256 256 3584 encodingCheck1
    (BitNetwork.check_append encodingCheck 512 256 3328 encodingCheck2
    (BitNetwork.check_append encodingCheck 768 256 3072 encodingCheck3
    (BitNetwork.check_append encodingCheck 1024 256 2816 encodingCheck4
    (BitNetwork.check_append encodingCheck 1280 256 2560 encodingCheck5
    (BitNetwork.check_append encodingCheck 1536 256 2304 encodingCheck6
    (BitNetwork.check_append encodingCheck 1792 256 2048 encodingCheck7
    (BitNetwork.check_append encodingCheck 2048 256 1792 encodingCheck8
    (BitNetwork.check_append encodingCheck 2304 256 1536 encodingCheck9
    (BitNetwork.check_append encodingCheck 2560 256 1280 encodingCheck10
    (BitNetwork.check_append encodingCheck 2816 256 1024 encodingCheck11
    (BitNetwork.check_append encodingCheck 3072 256 768 encodingCheck12
    (BitNetwork.check_append encodingCheck 3328 256 512 encodingCheck13
    (BitNetwork.check_append encodingCheck 3584 256 256 encodingCheck14
    encodingCheck15)))))))))))))))

theorem encode_vector (n : Fin 4096) : encodeVector (vector n.val) = n.val := by
  have h := BitNetwork.check_sound encodingCheck 0 4096 encodingCheck_all n.val
    (Nat.zero_le _) n.isLt
  exact of_decide_eq_true h

private def fixedCheck (n : Nat) : Bool :=
  let x : Fin 3510 := ⟨n % 3510, Nat.mod_lt _ (by decide)⟩
  decide (fastA x = x → norm (representative x) = 0 ∧ Normalized (representative x) ∧
    decodeLabel (encodeVector (representative x)) = x)

set_option maxRecDepth 2048 in
private theorem fixedCheck0 : BitNetwork.check fixedCheck 0 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck1 : BitNetwork.check fixedCheck 256 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck2 : BitNetwork.check fixedCheck 512 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck3 : BitNetwork.check fixedCheck 768 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck4 : BitNetwork.check fixedCheck 1024 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck5 : BitNetwork.check fixedCheck 1280 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck6 : BitNetwork.check fixedCheck 1536 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck7 : BitNetwork.check fixedCheck 1792 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck8 : BitNetwork.check fixedCheck 2048 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck9 : BitNetwork.check fixedCheck 2304 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck10 : BitNetwork.check fixedCheck 2560 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck11 : BitNetwork.check fixedCheck 2816 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck12 : BitNetwork.check fixedCheck 3072 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem fixedCheck13 : BitNetwork.check fixedCheck 3328 182 = true := by
  decide +kernel

private theorem fixedCheck_all : BitNetwork.check fixedCheck 0 3510 = true :=
  (BitNetwork.check_append fixedCheck 0 256 3254 fixedCheck0
    (BitNetwork.check_append fixedCheck 256 256 2998 fixedCheck1
    (BitNetwork.check_append fixedCheck 512 256 2742 fixedCheck2
    (BitNetwork.check_append fixedCheck 768 256 2486 fixedCheck3
    (BitNetwork.check_append fixedCheck 1024 256 2230 fixedCheck4
    (BitNetwork.check_append fixedCheck 1280 256 1974 fixedCheck5
    (BitNetwork.check_append fixedCheck 1536 256 1718 fixedCheck6
    (BitNetwork.check_append fixedCheck 1792 256 1462 fixedCheck7
    (BitNetwork.check_append fixedCheck 2048 256 1206 fixedCheck8
    (BitNetwork.check_append fixedCheck 2304 256 950 fixedCheck9
    (BitNetwork.check_append fixedCheck 2560 256 694 fixedCheck10
    (BitNetwork.check_append fixedCheck 2816 256 438 fixedCheck11
    (BitNetwork.check_append fixedCheck 3072 256 182 fixedCheck12
    fixedCheck13)))))))))))))

theorem representative_spec (x : Fin 3510) (hx : fastA x = x) :
    norm (representative x) = 0 ∧ Normalized (representative x) ∧
      decodeLabel (encodeVector (representative x)) = x := by
  have h := BitNetwork.check_sound fixedCheck 0 3510 fixedCheck_all x.val
    (Nat.zero_le _) x.isLt
  have h' : fastA x = x → norm (representative x) = 0 ∧ Normalized (representative x) ∧
      decodeLabel (encodeVector (representative x)) = x := by
    simpa only [fixedCheck, Nat.mod_eq_of_lt x.isLt, decide_eq_true_eq] using h
  exact h' hx

private def coverageCheck (n : Nat) : Bool :=
  decide (norm (vector n) = 0 ∧ Normalized (vector n) →
    fastA (decodeLabel n) = decodeLabel n ∧ representative (decodeLabel n) = vector n)

set_option maxRecDepth 2048 in
private theorem coverageCheck0 : BitNetwork.check coverageCheck 0 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck1 : BitNetwork.check coverageCheck 256 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck2 : BitNetwork.check coverageCheck 512 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck3 : BitNetwork.check coverageCheck 768 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck4 : BitNetwork.check coverageCheck 1024 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck5 : BitNetwork.check coverageCheck 1280 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck6 : BitNetwork.check coverageCheck 1536 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck7 : BitNetwork.check coverageCheck 1792 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck8 : BitNetwork.check coverageCheck 2048 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck9 : BitNetwork.check coverageCheck 2304 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck10 : BitNetwork.check coverageCheck 2560 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck11 : BitNetwork.check coverageCheck 2816 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck12 : BitNetwork.check coverageCheck 3072 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck13 : BitNetwork.check coverageCheck 3328 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck14 : BitNetwork.check coverageCheck 3584 256 = true := by
  decide +kernel

set_option maxRecDepth 2048 in
private theorem coverageCheck15 : BitNetwork.check coverageCheck 3840 256 = true := by
  decide +kernel

private theorem coverageCheck_all : BitNetwork.check coverageCheck 0 4096 = true :=
  (BitNetwork.check_append coverageCheck 0 256 3840 coverageCheck0
    (BitNetwork.check_append coverageCheck 256 256 3584 coverageCheck1
    (BitNetwork.check_append coverageCheck 512 256 3328 coverageCheck2
    (BitNetwork.check_append coverageCheck 768 256 3072 coverageCheck3
    (BitNetwork.check_append coverageCheck 1024 256 2816 coverageCheck4
    (BitNetwork.check_append coverageCheck 1280 256 2560 coverageCheck5
    (BitNetwork.check_append coverageCheck 1536 256 2304 coverageCheck6
    (BitNetwork.check_append coverageCheck 1792 256 2048 coverageCheck7
    (BitNetwork.check_append coverageCheck 2048 256 1792 coverageCheck8
    (BitNetwork.check_append coverageCheck 2304 256 1536 coverageCheck9
    (BitNetwork.check_append coverageCheck 2560 256 1280 coverageCheck10
    (BitNetwork.check_append coverageCheck 2816 256 1024 coverageCheck11
    (BitNetwork.check_append coverageCheck 3072 256 768 coverageCheck12
    (BitNetwork.check_append coverageCheck 3328 256 512 coverageCheck13
    (BitNetwork.check_append coverageCheck 3584 256 256 coverageCheck14
    coverageCheck15)))))))))))))))

theorem normalizedCode_spec (n : Fin 4096)
    (hn : norm (vector n.val) = 0 ∧ Normalized (vector n.val)) :
    fastA (decodeLabel n.val) = decodeLabel n.val ∧
      representative (decodeLabel n.val) = vector n.val := by
  have h := BitNetwork.check_sound coverageCheck 0 4096 coverageCheck_all n.val
    (Nat.zero_le _) n.isLt
  exact of_decide_eq_true h hn

end Sporadic.Fischer.Fi22.TransvectionComparison.Labeling
