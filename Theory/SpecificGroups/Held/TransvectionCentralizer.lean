module
public import Theory.SpecificGroups.Held.TransvectionCentralizer.CoreFusion
public import Theory.SpecificGroups.Held.TransvectionCentralizer.FusionCounts

/-! The native Held example for the transvection-centralizer recognition
retains the actual centralWord, its whole centralizer, and its literal
point-core fusion. Both rectangle fusion sets have 45 elements. -/

namespace Held.TransvectionCentralizer
open Theory.GroupTheory.TransvectionFive

/-- An actual native Held marked centralizer with point-core fusion and
the two source Held fusion counts. -/
public theorem exists_native_example : ∃ z : He, ∃ F : MarkedCentralizer z,
    PointCoreFusion z ∧ (F.fusion F.plane).ncard = 45 ∧
      (F.fusion F.threeSpace).ncard = 45 := by
  obtain ⟨F, _⟩ := exists_marking
  exact ⟨_, F, point_core_fusion, fusion_counts F point_core_fusion⟩

end Held.TransvectionCentralizer
