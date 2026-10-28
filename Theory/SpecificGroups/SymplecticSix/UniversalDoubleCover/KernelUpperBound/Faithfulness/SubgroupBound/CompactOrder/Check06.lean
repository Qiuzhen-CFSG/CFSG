module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.Faithfulness.SubgroupBound.CompactOrder.Tables

/-! Kernel-checked deductions for the literal compact ATLAS S62G1-P1 subgroup presentation.
Chunks bound the reduction cache; each scan uses previously proved equations. -/

public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
open Subgroup.CosetWordCertificate

set_option Elab.async false

set_option maxRecDepth 4096 in
theorem checked_98304 : Scan.checkChunk context facts instructions 98304 1024 = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem checked_99328 : Scan.checkChunk context facts instructions 99328 655 = true := by
  decide +kernel

theorem sound_98304 (prior : ∀ n, n < 98304 →
    Holds smallSubgroup generator (definitions.repr generator) (facts n)) :
    ∀ n, n < 99983 → Holds smallSubgroup generator (definitions.repr generator) (facts n) := by
  have h99328 := Scan.chunk_sound context_valid facts instructions 98304 1024
    prior checked_98304
  have h99983 := Scan.chunk_sound context_valid facts instructions 99328 655
    h99328 checked_99328
  exact h99983

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.Faithfulness.SubgroupBound.CompactOrder
