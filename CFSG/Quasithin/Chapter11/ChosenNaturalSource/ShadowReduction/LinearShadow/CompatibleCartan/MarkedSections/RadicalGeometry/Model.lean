module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Model
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores

/-!
# The two SL₃ radical planes and their intersection

In the aligned natural basis, the line radical has only entries (0,2) and
(1,2) off the diagonal. Its intersection with the point radical is the
highest root group, of order q. A vector outside the flag plane detects
this intersection through its displacement into the flag point.

Source: Aschbacher--Smith, the complement paragraph after 11.3.8,
printed p.775; the ambient transport is in RadicalGeometry.Transport.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry
open Matrix.PSL3.LinearThree
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem line_core_matrix (g : SL(3,F)) (hg : g ∈ (lineLocalSL F).pCoreIn 2) :
    g.val = !![1,0,g.val 0 2;0,1,g.val 1 2;0,0,1] := by
  obtain ⟨l,hl,rfl⟩ := hg
  rw [lineLocalSL_twoCore_eq] at hl
  obtain ⟨h00,h01,h10,h11⟩ := (mem_lineRadicalSL_iff F l).mp hl
  obtain ⟨h20,h21,h22⟩ := (mem_lineLocalSL_iff F l).mp l.property
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00,h01,h10,h11,h20,h21,h22]

theorem line_core_mem_point_core_iff (g : SL(3,F))
    (hg : g ∈ (lineLocalSL F).pCoreIn 2) :
    g ∈ (pointLocalSL F).pCoreIn 2 ↔ g.val 1 2 = 0 := by
  constructor
  · rintro ⟨p,hp,rfl⟩
    rw [pointLocalSL_twoCore_eq] at hp
    exact ((mem_pointRadicalSL_iff F p).mp hp).2.1
  · intro h12
    have hm := line_core_matrix g hg
    have hpt : g ∈ pointLocalSL F := by
      rw [mem_pointLocalSL_iff]
      rw [hm]
      simp
    refine ⟨⟨g,hpt⟩,?_,rfl⟩
    rw [pointLocalSL_twoCore_eq]
    apply (mem_pointRadicalSL_iff F ⟨g,hpt⟩).mpr
    change g.val 1 1 = 1 ∧ g.val 1 2 = 0 ∧ g.val 2 1 = 0 ∧ g.val 2 2 = 1
    rw [hm]
    simp [h12]

/-- For a vector outside the invariant plane, the displacement detects
membership in the opposite radical. -/
theorem line_core_displacement (g : SL(3,F))
    (hg : g ∈ (lineLocalSL F).pCoreIn 2) (v : Fin 3 → F) (hv : v 2 ≠ 0) :
    v - g.val.mulVec v ∈ Model.point ↔ g ∈ (pointLocalSL F).pCoreIn 2 := by
  rw [line_core_mem_point_core_iff g hg]
  have hm := line_core_matrix g hg
  change (v - g.val.mulVec v) 1 = 0 ∧ (v - g.val.mulVec v) 2 = 0 ↔ _
  rw [hm]
  simp [dotProduct,Fin.sum_univ_three,hv]

/-- The intersection of the two literal model radicals is the highest root. -/
def radicalIntersectionEquiv :
    ((lineLocalSL F).pCoreIn 2 ⊓ (pointLocalSL F).pCoreIn 2 : Subgroup SL(3,F)) ≃ F where
  toFun g := g.val.val 0 2
  invFun a := by
    let g := SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a
    have hline : g ∈ lineLocalSL F := by
      rw [mem_lineLocalSL_iff]
      simp [g,SpecialLinearGroup.transvection_coe]
    have hg : g ∈ (lineLocalSL F).pCoreIn 2 := by
      refine ⟨⟨g,hline⟩,?_,rfl⟩
      rw [lineLocalSL_twoCore_eq]
      apply (mem_lineRadicalSL_iff F ⟨g,hline⟩).mpr
      simp [g,SpecialLinearGroup.transvection_coe]
    exact ⟨g,hg,(line_core_mem_point_core_iff g hg).mpr
      (by simp [g,SpecialLinearGroup.transvection_coe])⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    have hm := line_core_matrix g.val g.property.1
    have h12 := (line_core_mem_point_core_iff g.val g.property.1).mp g.property.2
    rw [h12] at hm
    rw [hm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [SpecialLinearGroup.transvection_coe]
  right_inv a := by simp [SpecialLinearGroup.transvection_coe]

theorem card_radical_intersection :
    Nat.card ((lineLocalSL F).pCoreIn 2 ⊓ (pointLocalSL F).pCoreIn 2 : Subgroup SL(3,F)) =
      Nat.card F := Nat.card_congr radicalIntersectionEquiv
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections.RadicalGeometry
