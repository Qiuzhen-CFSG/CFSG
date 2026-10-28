module
public import Theory.GroupTheory.MinusExtraspecialOddCentralizer.Calculation
/-!
# Generator form of the checked centralizer identities

Translate membership in the checked automorphism list into generator
relations. This is the computational interface consumed by the model
transport; every finite identity is supplied by `Calculation`.
Source application: Aschbacher–Smith 14.2.17(1), printed p.987.
-/
@[expose] public section
namespace MinusExtraspecial.FixedFourCalculation.OddCentralizer
open Outside OddInvolution

private theorem all_mem : ∀ x : B, x ∈ all := by decide +kernel

theorem mem_row (u v r s : B) (h : relations u v r s) : (v,r,s) ∈ row u := by
  rw [←generatedRow_eq]
  simp only [relations, Bool.and_eq_true,bne_iff_ne,beq_iff_eq,and_assoc] at h
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := h
  have hb1 : (mul u u != 0) = true := bne_iff_ne.mpr h1
  simp only [generatedRow,hb1,↓reduceIte,List.mem_flatMap]
  refine ⟨v,all_mem v,?_⟩
  simp only [h2,h3,beq_self_eq_true,Bool.and_self,↓reduceIte,List.mem_flatMap]
  refine ⟨r,all_mem r,?_⟩
  simp only [h4,h5,h6,beq_self_eq_true,Bool.and_self,↓reduceIte,List.mem_filterMap]
  exact ⟨s,all_mem s,by simp only [h7,h8,h9,h10,beq_self_eq_true,Bool.and_self,↓reduceIte]⟩

end MinusExtraspecial.FixedFourCalculation.OddCentralizer
