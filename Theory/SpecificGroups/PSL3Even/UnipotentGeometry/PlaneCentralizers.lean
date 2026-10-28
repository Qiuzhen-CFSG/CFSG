module
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.CommutatorRows
public import Theory.GroupTheory.TwoPlaneCover.Rows
/-! # Plane centralizers and full commutator rows
Each actual linear root plane is self-centralizing. An involution outside it
has the opposite plane as centralizer, so the common centralizer is central.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Matrix.PSL3Even.UnipotentGeometry
variable {F:Type*} [Field F] [CharP F 2]
theorem plane₁_self_centralizer : centralizer (V₁ F:Set (U F))=V₁ F := by
  apply Subgroup.TwoPlaneCover.self_centralizer_of_witness (V₁ F) (⟨1,0,0⟩:U F) (by simp)
  have h:=centralizer_involution F (⟨1,0,0⟩:U F)
    ((square_eq_one_iff F _).mpr (Or.inr rfl)) (by simp)
  rcases h with h|h
  · exact h
  · have hh:(⟨1,0,0⟩:U F)∈V₂ F:=h ▸ (show (⟨1,0,0⟩:U F)∈centralizer ({⟨1,0,0⟩}:Set (U F)) from mem_centralizer_singleton_iff.mpr rfl)
    simp at hh
theorem plane₂_self_centralizer : centralizer (V₂ F:Set (U F))=V₂ F := by
  apply Subgroup.TwoPlaneCover.self_centralizer_of_witness (V₂ F) (⟨0,1,0⟩:U F) (by simp)
  have h:=centralizer_involution F (⟨0,1,0⟩:U F)
    ((square_eq_one_iff F _).mpr (Or.inl rfl)) (by simp)
  rcases h with h|h
  · have hh:(⟨0,1,0⟩:U F)∈V₁ F:=h ▸ (show (⟨0,1,0⟩:U F)∈centralizer ({⟨0,1,0⟩}:Set (U F)) from mem_centralizer_singleton_iff.mpr rfl)
    simp at hh
  · exact h

theorem plane_involution_geometry (P:Subgroup (U F)) (hP:P=V₁ F∨P=V₂ F)
    (t:U F) (ht:t^2=1) (hn:t∉P) :
    centralizer (P:Set (U F))=P ∧
      P⊔centralizer ({t}:Set (U F))=⊤ ∧
      P⊓centralizer ({t}:Set (U F))≤center (U F) := by
  have hz:t∉Z F:=by
    intro hz
    exact hn (hP.elim (fun h=>h.symm ▸ ((mem_V₁ F t).mpr ((mem_Z F t).mp hz).2))
      (fun h=>h.symm ▸ ((mem_V₂ F t).mpr ((mem_Z F t).mp hz).1)))
  have hct:=centralizer_involution F t ht hz
  rcases hP with rfl|rfl
  · refine ⟨plane₁_self_centralizer,?_,?_⟩
    · rcases hct with h|h
      · exact False.elim (hn (h ▸ (show t∈centralizer ({t}:Set (U F)) from mem_centralizer_singleton_iff.mpr rfl)))
      · rw [h,planes_generate]
    · exact Subgroup.TwoPlaneCover.centralizer_inter_plane_le_center _ _
        (by rw [root_planes_inter,Z_eq_center]) t hn hct
  · refine ⟨plane₂_self_centralizer,?_,?_⟩
    · rcases hct with h|h
      · rw [h,sup_comm,planes_generate]
      · exact False.elim (hn (h ▸ (show t∈centralizer ({t}:Set (U F)) from mem_centralizer_singleton_iff.mpr rfl)))
    · exact Subgroup.TwoPlaneCover.centralizer_inter_plane_le_center _ _
        (by rw [inf_comm,root_planes_inter,Z_eq_center]) t hn hct.symm
end Matrix.PSL3Even.UnipotentGeometry
