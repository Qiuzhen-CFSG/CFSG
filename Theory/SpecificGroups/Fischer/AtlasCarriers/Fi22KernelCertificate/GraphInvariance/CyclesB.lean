module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.CyclesB0
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.CyclesB1
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleNodup

/-!
# The decoded second Fi22 generator

The two exact character certificates give the complete cycle table. A bit-set
scan certifies that all its cycles are disjoint. The source is the second
ATLAS F22G1-p3510B0 permutation, with the inverse convention of `Fi22.lean`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.KernelCertificate
open AtlasCarriers

def cyclesB : List (List (Fin 3510)) := cyclesB0 ++ cyclesB1

theorem cyclesB_spec : decodeCycleBlocks 3510 cycleBlocksB = cyclesB := by
  have h0 := cyclesB0_spec
  have h1 := cyclesB1_spec
  simp only [decodeCycleBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    cycleBlocksB, List.getElem!_cons_zero, List.getElem!_cons_succ] at h0 h1
  simp only [decodeCycleBlocks, cycleBlocksB, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [h0, h1]
  rfl

set_option maxRecDepth 100000 in
theorem cyclesB_nodup : cyclesB.flatten.Nodup := by
  apply nodup_of_checkFreshPoints
  decide +kernel

end Sporadic.Fischer.Fi22.KernelCertificate
