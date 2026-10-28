module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.InvolutionBlock0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.InvolutionBlock1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.InvolutionBlock2
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.InvolutionBlock3
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.InvolutionBlock4
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.InvolutionBlock5
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleInvolutions
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleNodup

/-!
# The exact ATLAS Fi22 generator is a nontrivial involution

The decoded source cycles are disjoint pairs. Scanning their flattened list
certifies disjointness, and the disjoint-transposition theorem gives square one.
The image of point zero supplies the nonidentity witness.
Source: ATLAS F22G1-p3510B0 and GLS3 Table 5.3t.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.KernelCertificate
open AtlasCarriers

/-- The source table decoded into explicit finite points. -/
def cyclesA : List (List (Fin 3510)) :=
  cyclesA0 ++ cyclesA1 ++ cyclesA2 ++ cyclesA3 ++ cyclesA4 ++ cyclesA5

theorem cyclesA_spec : decodeCycleBlocks 3510 cycleBlocksA = cyclesA := by
  have h0 := cyclesA0_spec
  have h1 := cyclesA1_spec
  have h2 := cyclesA2_spec
  have h3 := cyclesA3_spec
  have h4 := cyclesA4_spec
  have h5 := cyclesA5_spec
  simp only [decodeCycleBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    cycleBlocksA, List.getElem!_cons_zero, List.getElem!_cons_succ] at h0 h1 h2 h3 h4 h5
  simp only [decodeCycleBlocks, cycleBlocksA, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [h0, h1, h2, h3, h4, h5]
  simp only [cyclesA, List.append_assoc]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cyclesA_nodup : cyclesA.flatten.Nodup := by
  apply nodup_of_checkFreshPoints
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem cyclesA_pairs : ∀ l ∈ cyclesA, l.length = 2 := by decide +kernel

theorem generatorA_sq : generatorA ^ 2 = 1 := by
  apply permutationFromCycleBlocks_sq_eq_one
  · rw [cyclesA_spec]
    exact cyclesA_nodup
  · rw [cyclesA_spec]
    exact cyclesA_pairs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem generatorA_zero : generatorA (0 : Fin 3510) = 523 := by
  simp only [generatorA, permutationFromCycleBlocks, cyclesA_spec]
  decide +kernel

end Sporadic.Fischer.Fi22.KernelCertificate
