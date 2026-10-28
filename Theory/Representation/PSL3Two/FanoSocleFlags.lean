module
public import Theory.Representation.PSL3Two.FanoCoreStructure
public import Theory.Representation.PSL3Two.FanoLocalStructure.ParabolicSpaces
public import Theory.Representation.PSL3Two.FanoLocalStructure.Orbits
public import Theory.Representation.BinaryOffender.MovedDimension

/-!
# Socle and fixed-line tests in the marked Fano core

The line-parabolic fixed line is contained in the dual-natural socle; the
point-parabolic fixed line is outside it. The previously proved orbit
partition separates the point and line complements. Together with the
literal flag commutators this gives the four tests used in the point-core
row of Aschbacher–Smith 13.4.14, printed p.911 (H.5, pp.385–386).
-/

public noncomputable section
open Representation Representation.BinaryOffender Matrix.PSL3Two
namespace BinaryLinearThree.FanoLocalStructure
open FanoDecomposition FanoCoreStructure ParabolicSpaces

/-- The marked line fixed space is in the actual socle of the point core. -/
theorem line_fixed_le_socle : fixedSpace U₂ lineParabolicSL ≤
    (sSup {N : Subrepresentation U₂ | IsAtom N}).toSubmodule := by
  rw [←pointKernel_eq_socle,fixedSpace_lineParabolic]
  apply Submodule.span_le.mpr
  rintro v (rfl : v = ul)
  exact (mem_pointKernel_iff ul).mpr (Or.inr ⟨flagLine,rfl⟩)

/-- The marked point fixed space is outside the actual socle of the point core. -/
theorem point_fixed_not_le_socle : ¬ fixedSpace U₂ pointParabolicSL ≤
    (sSup {N : Subrepresentation U₂ | IsAtom N}).toSubmodule := by
  rw [←pointKernel_eq_socle]
  intro h
  have hu : up ∈ fixedSpace U₂ pointParabolicSL := by
    rw [fixedSpace_pointParabolic]
    exact Submodule.mem_span_singleton_self _
  have hp : up ∈ pointComplements := ⟨flagPoint,rfl⟩
  rcases (mem_pointKernel_iff up).mp (h hu) with he | he
  · exact ((nonzero_iff_mem_four_families up).mpr (Or.inl hp)) he
  · exact Set.disjoint_left.mp four_families_disjoint.1 hp he

/-- Under the standard flag, the point core has exactly the two directional
fixed-line and commutator properties used in 13.4.14. -/
theorem point_core_flag_tests :
    fixedSpace U₂ lineParabolicSL ≤
      subspaceCommutator U₂ (fixedSpace U₂ borelSL) pointParabolicSL ∧
    ¬ fixedSpace U₂ pointParabolicSL ≤
      subspaceCommutator U₂ (fixedSpace U₂ borelSL) lineParabolicSL ∧
    fixedSpace U₂ lineParabolicSL ≤
      (sSup {N : Subrepresentation U₂ | IsAtom N}).toSubmodule ∧
    ¬ fixedSpace U₂ pointParabolicSL ≤
      (sSup {N : Subrepresentation U₂ | IsAtom N}).toSubmodule := by
  have h₁ := fixedSpace_line_le_flag_pointCommutator
  have h₂ := fixedSpace_point_not_le_flag_lineCommutator
  rw [flagSylow_coe,markedFlag_stabilizer] at h₁ h₂
  exact ⟨h₁,h₂,line_fixed_le_socle,point_fixed_not_le_socle⟩
end BinaryLinearThree.FanoLocalStructure
