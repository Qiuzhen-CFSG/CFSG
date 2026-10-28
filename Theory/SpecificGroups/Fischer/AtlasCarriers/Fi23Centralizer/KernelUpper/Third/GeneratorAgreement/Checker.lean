module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleListDecoding
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelData
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.SourceActions.Checker

/-!
# Assembling the third-stage generator comparisons

The original strings are decoded block by block. Disjoint support certificates
then identify the inverse cycle product from its action on each short cycle and
its fixed complement. This retains the right-action inversion in `CycleEncoding`.
The seven concrete consumers are the `Generator0`–`Generator6` extensions.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u, with the Fischer paragraph in
`refs/KGroup/GLS3/Chapter5(sec3-).tex`, near line 1042.
-/

public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
open AtlasCarriers KernelCertificate KernelCertificate.FixedLetterCheck
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck

/-- Reassemble checked decodings of the original string blocks. -/
theorem decode_of_blocks {blocks : List String} {parts : List (List (List (Fin 31671)))}
    (h : List.Forall₂ (fun b p => decodeCycleBlocks 31671 [b] = p) blocks parts) :
    decodeCycleBlocks 31671 blocks = parts.flatten := by
  induction h with
  | nil => rfl
  | @cons b p bs ps hb _ ih =>
    change _ = p ++ ps.flatten
    rw [← hb, ← ih]
    simp only [decodeCycleBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The checked cycle actions and fixed complement determine the literal map. -/
theorem map_eq_of_certificates (f : Fin 31671 → Fin 31671)
    (blocks : List String) (parts : List (List (List (Fin 31671)))) (ms : List Nat)
    (hdecode : decodeCycleBlocks 31671 blocks = parts.flatten)
    (hcert : List.Forall₂ (fun cs m => Certificate cs.flatten m) parts ms)
    (hdisjoint : disjointMasks ms = true)
    (hcycle : parts.all (cycleTest f) = true)
    (hfix : ∀ x : Fin 31671, (unionMasks ms).testBit x.val = false → f x = x)
    (x : Fin 31671) : f x = permutationFromCycleBlocks 31671 blocks x := by
  rw [permutationFromCycleBlocks, hdecode]
  exact (cyclesInv_eq_of_tests f parts.flatten (unionMasks ms)
    (certify_blocks parts ms hcert hdisjoint)
    (blockTests_sound f parts hcycle) hfix x).symm.trans (cyclesInv_eq _ _)

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.GeneratorAgreement
