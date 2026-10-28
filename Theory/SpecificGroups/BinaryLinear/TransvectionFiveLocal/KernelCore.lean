module

public import Theory.SpecificGroups.BinaryLinear.TransvectionFiveLocal.KernelStructure
public import Theory.GroupTheory.PCoreLocalSetup
import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceColumn
import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.CoreFusion.Shape
import all Theory.SpecificGroups.BinaryLinear.TransvectionFiveLocal.KernelStructure

/-!
# The literal kernel is the full model two-core

The row and column root groups are normal in the full transvection centralizer;
their join is precisely the seven-root subgroup. Its order is a power of two.
Conversely, middle-coordinate reversal forces every element of the full two-core
to have the seven-coordinate matrix shape, which lies in that subgroup.

The internal import of KernelStructure deliberately reuses its private matrix
parametrization only inside the proof. The public equality concerns the original
literal subgroups, with no parametrization or recognition premise.

Source: Aschbacher, Sporadic Groups,39.1(1),(5), pp.213--214.
-/

namespace BinaryLinear.TransvectionFiveLocal
open Subgroup
open Theory.GroupTheory.TransvectionFive

private def identityMarking : MarkedCentralizer transvection where
  equiv := MulEquiv.refl _
  on_point := rfl

private theorem identity_pullback (A : Subgroup SL) (hA : A ≤ centralizer) :
    identityMarking.pullback A=A := by
  change ((A.subgroupOf centralizer).map (MonoidHom.id _)).map centralizer.subtype=A
  rw [Subgroup.map_id,map_subgroupOf_eq_of_le hA]

private theorem kernel_join : kernel=dualFactor⊔naturalFactor := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨i,j,h,hij,rfl⟩
    rcases hij with rfl | rfl
    · exact (show dualFactor ≤ dualFactor⊔naturalFactor from le_sup_left)
        (subset_closure ⟨j,h,rfl⟩)
    · exact (show naturalFactor ≤ dualFactor⊔naturalFactor from le_sup_right)
        (subset_closure ⟨i,h,rfl⟩)
  · exact sup_le dualFactor_le_kernel naturalFactor_le_kernel

private theorem centralizer_normalizes_kernel :
    centralizer ≤ normalizer (kernel : Set SL) := by
  have hr : centralizer ≤ normalizer (dualFactor : Set SL) := by
    simpa only [MarkedCentralizer.row,identity_pullback _ Model.row_le_centralizer,Model.row,centralizer] using
      UniquenessLinear.point_centralizer_le_row_normalizer identityMarking
  have hc : centralizer ≤ normalizer (naturalFactor : Set SL) := by
    simpa only [MarkedCentralizer.column,identity_pullback _ Model.column_le_centralizer,Model.column,centralizer] using
      UniquenessLinear.point_centralizer_le_column_normalizer identityMarking
  rw [kernel_join]
  exact (le_inf hr hc).trans
    (normalizer_inf_normalizer_le_normalizer_sup dualFactor naturalFactor)

/-- The seven-root extraspecial kernel is exactly the embedded full two-core
of the literal transvection centralizer in SL₅(2). -/
public theorem kernel_eq_twoCore : kernel=centralizer.pCoreIn 2 := by
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes
      (IsPGroup.of_card (p := 2) (n := 7) kernel_card)
      (kernel_le_upper.trans upper_le_centralizer) centralizer_normalizes_kernel
  · rintro x ⟨q,hq,rfl⟩
    let c : Coordinates := ⟨q.val 0 4,q.val 0 1,q.val 0 2,q.val 0 3,
      q.val 1 4,q.val 2 4,q.val 3 4⟩
    have he : (q : SL)=embedding c := by
      apply Subtype.ext
      exact UniquenessMathieu.SourceNormalizer.CoreFusion.core_shape q hq
    change (q : SL) ∈ kernel
    rw [he]
    exact embedding_mem c

end BinaryLinear.TransvectionFiveLocal
