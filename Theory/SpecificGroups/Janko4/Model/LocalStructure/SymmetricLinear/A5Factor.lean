module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient

/-!
# Marking the A₅ factor of J₄ max4

A normal subgroup of max4 has two-core equal to its intersection with the
ambient two-core. In particular a normal overgroup of that core has the
same core. The actual preimage of A₅ × 1 under the certified five-point and
three-dimensional quotient actions is such an overgroup.

This retains the actual `max4Projection`; it does not assert that an arbitrary
A₅-containing subgroup of J₄ is conjugate to this marked preimage.
Source: Aschbacher–Smith A.3.12(17) and A.3.14(10).
-/

public section
open Subgroup
namespace Janko4.LocalStructure.SymmetricLinear

/-- A normal subgroup has two-core equal to the restriction of the ambient core. -/
theorem normal_subgroup_twoCore (H : Subgroup max4Subgroup) [H.Normal]
    :
    pCore 2 H = (pCore 2 max4Subgroup).subgroupOf H := by
  apply le_antisymm
  · have hm : ((pCore 2 H).map H.subtype).Normal := inferInstance
    have hl : (pCore 2 H).map H.subtype ≤ pCore 2 max4Subgroup :=
      le_sSup ⟨hm, pCore_isPGroup.map H.subtype⟩
    intro x hx
    exact hl (mem_map_of_mem _ hx)
  · exact le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩

/-- The normal-overgroup identification keeps the literal subgroup inclusions. -/
noncomputable def normalOvergroupCoreEquiv (H : Subgroup max4Subgroup) [H.Normal]
    (hQ : pCore 2 max4Subgroup ≤ H) :
    pCore 2 H ≃* pCore 2 max4Subgroup :=
  (MulEquiv.subgroupCongr (normal_subgroup_twoCore H)).trans
    (subgroupOfEquivOfLe hQ)

/-- The actual A₅ factor in the certified max4 quotient S₅ × SL₃(2). -/
def a5Factor : Subgroup QuotientModel := (alternatingGroup (Fin 5)).prod ⊥

instance : a5Factor.Normal := by
  unfold a5Factor
  infer_instance

/-- Its literal full preimage retains both certified max4 quotient actions. -/
noncomputable def a5Preimage : Subgroup max4Subgroup := a5Factor.comap max4Projection

instance : a5Preimage.Normal := by
  unfold a5Preimage
  infer_instance

theorem twoCore_le_a5Preimage : pCore 2 max4Subgroup ≤ a5Preimage := by
  rw [← max4Projection_kernel_eq_twoCore]
  intro x hx
  change max4Projection x ∈ a5Factor
  rw [MonoidHom.mem_ker.mp hx]
  exact one_mem _

noncomputable def a5PreimageCoreEquiv : pCore 2 a5Preimage ≃* pCore 2 max4Subgroup :=
  normalOvergroupCoreEquiv a5Preimage twoCore_le_a5Preimage
end Janko4.LocalStructure.SymmetricLinear
