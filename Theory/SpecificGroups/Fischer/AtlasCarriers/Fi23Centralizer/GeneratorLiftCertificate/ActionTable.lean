module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.GeneratorLiftCertificate.Predicates

/-!
# Kernel certificate for both coordinate actions, including the extra fixed point

Every displayed Boolean block is reduced by Lean's kernel. The checker soundness
lemma then covers all 3511 indices. No native or external evaluator proves any
of these assertions. `source/checks.py` reproduces the certificate source.
The intended source application is the Fi23 centralizer in GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate

-- Each bounded reduction releases its cache before the next one is checked.
set_option Elab.async false

set_option maxRecDepth 1000 in
private theorem block_0 : checkRange (checkAt actionCheck) 7 0 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_1 : checkRange (checkAt actionCheck) 7 128 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_2 : checkRange (checkAt actionCheck) 7 256 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_3 : checkRange (checkAt actionCheck) 7 384 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_4 : checkRange (checkAt actionCheck) 7 512 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_5 : checkRange (checkAt actionCheck) 7 640 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_6 : checkRange (checkAt actionCheck) 7 768 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_7 : checkRange (checkAt actionCheck) 7 896 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_8 : checkRange (checkAt actionCheck) 7 1024 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_9 : checkRange (checkAt actionCheck) 7 1152 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_10 : checkRange (checkAt actionCheck) 7 1280 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_11 : checkRange (checkAt actionCheck) 7 1408 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_12 : checkRange (checkAt actionCheck) 7 1536 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_13 : checkRange (checkAt actionCheck) 7 1664 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_14 : checkRange (checkAt actionCheck) 7 1792 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_15 : checkRange (checkAt actionCheck) 7 1920 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_16 : checkRange (checkAt actionCheck) 7 2048 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_17 : checkRange (checkAt actionCheck) 7 2176 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_18 : checkRange (checkAt actionCheck) 7 2304 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_19 : checkRange (checkAt actionCheck) 7 2432 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_20 : checkRange (checkAt actionCheck) 7 2560 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_21 : checkRange (checkAt actionCheck) 7 2688 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_22 : checkRange (checkAt actionCheck) 7 2816 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_23 : checkRange (checkAt actionCheck) 7 2944 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_24 : checkRange (checkAt actionCheck) 7 3072 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_25 : checkRange (checkAt actionCheck) 7 3200 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_26 : checkRange (checkAt actionCheck) 7 3328 = true := by
  decide +kernel

set_option maxRecDepth 1000 in
private theorem block_27 : checkRange (checkAt actionCheck) 7 3456 = true := by
  decide +kernel

private theorem blocks (b : Fin 28) :
    checkRange (checkAt actionCheck) 7 (2^7 * b.val) = true := by
  rcases b with ⟨b, hb⟩
  interval_cases b
  · exact block_0
  · exact block_1
  · exact block_2
  · exact block_3
  · exact block_4
  · exact block_5
  · exact block_6
  · exact block_7
  · exact block_8
  · exact block_9
  · exact block_10
  · exact block_11
  · exact block_12
  · exact block_13
  · exact block_14
  · exact block_15
  · exact block_16
  · exact block_17
  · exact block_18
  · exact block_19
  · exact block_20
  · exact block_21
  · exact block_22
  · exact block_23
  · exact block_24
  · exact block_25
  · exact block_26
  · exact block_27

theorem action_checks (i : Fin 3511) : actionCheck i :=
  of_check_blocks actionCheck (by decide : 3511 ≤ 2^7 * 28) blocks i

end Sporadic.Fischer.Fi23.CentralizerSection.GeneratorLiftCertificate
