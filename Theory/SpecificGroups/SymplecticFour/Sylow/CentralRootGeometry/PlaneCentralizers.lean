module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CommutatorRows
public import Theory.GroupTheory.TwoPlaneCover.Rows
/-! # Plane centralizers and full commutator rows
Each actual symplectic wing is self-centralizing. An involution outside it
has the opposite wing as centralizer, so the common centralizer is central.
Source: Aschbacher--Smith 2.5.7, printed pp.555--556.
-/
public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F:Type*} [Field F] [Finite F] [CharP F 2]
theorem wings_inf : wing (F:=F) false⊓wing true=center (unipotent (F:=F)) := by
  ext a
  obtain ⟨⟨b,u,w,v⟩,rfl⟩:=element_surjective a
  simp only [mem_inf,element_mem_wing,mem_center_iff_coordinates,Bool.false_eq_true,↓reduceIte,and_comm]
theorem wing_self_centralizer (i:Bool) : centralizer (wing (F:=F) i:Set (unipotent (F:=F)))=wing i := by
  let :=wing_elementary (F:=F) i
  let a:unipotent (F:=F):=if i then element 0 0 0 1 else element 1 0 0 0
  have ha:a∈wing i:=by cases i <;> simp [a,element_mem_wing]
  have han:a∉wing (!i):=by cases i <;> simp [a,element_mem_wing]
  have hz:a∉center (unipotent (F:=F)):=by cases i <;> simp [a,mem_center_iff_coordinates]
  have hp:a^2=1:=by
    cases i
    · change (element (1:F) 0 0 0)^2=1
      rw [element_square]
      simpa only [mul_zero,theta] using (element_zero (F:=F))
    · change (element (0:F) 0 0 1)^2=1
      rw [element_square]
      simpa only [zero_pow (by decide:2≠0),zero_mul,theta] using (element_zero (F:=F))
  have hct:=centralizer_involution a hp hz
  apply Subgroup.TwoPlaneCover.self_centralizer_of_witness _ a ha
  have hmem:a∈centralizer ({a}:Set (unipotent (F:=F))):=mem_centralizer_singleton_iff.mpr rfl
  cases i
  · rcases hct with h|h
    · exact h
    · exact False.elim (han (h ▸ hmem))
  · rcases hct with h|h
    · exact False.elim (han (h ▸ hmem))
    · exact h

theorem wing_involution_geometry (i:Bool) (t:unipotent (F:=F)) (ht:t^2=1) (hn:t∉wing i) :
    centralizer ((wing (F:=F) i:Set (unipotent (F:=F))))=wing i ∧
      wing i⊔centralizer ({t}:Set (unipotent (F:=F)))=⊤ ∧
      wing i⊓centralizer ({t}:Set (unipotent (F:=F)))≤center (unipotent (F:=F)) := by
  have hz:t∉center (unipotent (F:=F)):=by
    intro hz
    have h:=center_le_wings hz
    cases i
    · exact hn h.1
    · exact hn h.2
  have hct:=centralizer_involution t ht hz
  have htC:t∈centralizer ({t}:Set (unipotent (F:=F))):=mem_centralizer_singleton_iff.mpr rfl
  cases i
  · refine ⟨wing_self_centralizer _,?_,?_⟩
    · rcases hct with h|h
      · exact False.elim (hn (h ▸ htC))
      · rw [h,wings_generate]
    · exact Subgroup.TwoPlaneCover.centralizer_inter_plane_le_center _ _ wings_inf.le t hn hct
  · refine ⟨wing_self_centralizer _,?_,?_⟩
    · rcases hct with h|h
      · rw [h,sup_comm,wings_generate]
      · exact False.elim (hn (h ▸ htC))
    · exact Subgroup.TwoPlaneCover.centralizer_inter_plane_le_center _ _
        (by rw [inf_comm,wings_inf]) t hn hct.symm
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
