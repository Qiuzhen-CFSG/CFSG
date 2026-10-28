/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianReflectionUnipotentImage.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionGlueElements
public import Theory.AtlasPort.Janko2.Conway.IcosianReflectionSwaps

/-!
# IcosianReflectionUnipotentImage

Reductions of the verified edge words yield the first and paired unipotents. Their
products supply the remaining independent unipotent direction.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianReflectionUnipotentImage.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway
open Atlas.Algebra Atlas.Codes

theorem icosianReflectionEdge_reduction_mem (k : Fin 3) (p : Fin 2) :
    icosianMonomialReduction (icosianReflectionEdgeMonomial k p)∈icosianReflectionGlueImage :=
  icosianReflectionGlueImage_mem_of_actual_word _ _
    (icosianReflectionEdgeWord_mem_reflections k p) (icosianReflectionEdgeWord_linear k p)

theorem icosianReflectionEdge_reduction_zero (k : Fin 3) :
    icosianMonomialReduction (icosianReflectionEdgeMonomial k 0)=
      icosianGlueUnipotent (icosianReflectionEdgeParameter k) (icosianReflectionEdgeParameter k) := by
  apply SemidirectProduct.ext
  · funext i
    apply Subtype.ext
    rw [icosianReflectionEdgeMonomial_reduction]
    change _=(icosianGlueBlockParameter 1 (icosianReflectionEdgeParameter k)
      (icosianReflectionEdgeParameter k) i).val
    fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;> fin_cases k <;> decide +kernel
  · rfl

theorem icosianReflectionEdge_reduction_one (k : Fin 3) :
    icosianMonomialReduction (icosianReflectionEdgeMonomial k 1)=
      icosianGlueUnipotent (icosianReflectionEdgeParameter k) 0 := by
  apply SemidirectProduct.ext
  · funext i
    apply Subtype.ext
    rw [icosianReflectionEdgeMonomial_reduction]
    change _=(icosianGlueBlockParameter 1 (icosianReflectionEdgeParameter k) 0 i).val
    fin_cases i <;> ext r c <;> fin_cases r <;> fin_cases c <;> fin_cases k <;> decide +kernel
  · rfl

theorem icosianReflection_unipotent_first (a : GoldenFour) :
    icosianGlueUnipotent a 0∈icosianReflectionGlueImage := by
  have hk (k : Fin 3) : icosianGlueUnipotent (icosianReflectionEdgeParameter k) 0∈
      icosianReflectionGlueImage := by
    rw [← icosianReflectionEdge_reduction_one]
    exact icosianReflectionEdge_reduction_mem k 1
  rcases icosianReflectionEdgeParameters_span a with rfl | rfl | rfl | rfl
  · exact hk 0
  · exact hk 1
  · exact hk 2
  · simpa [icosianGlueUnipotent_mul,icosianReflectionEdgeParameter] using
      icosianReflectionGlueImage.mul_mem (hk 1) (hk 2)

theorem icosianReflection_unipotent_paired (a : GoldenFour) :
    icosianGlueUnipotent a a∈icosianReflectionGlueImage := by
  have hk (k : Fin 3) : icosianGlueUnipotent (icosianReflectionEdgeParameter k)
      (icosianReflectionEdgeParameter k)∈icosianReflectionGlueImage := by
    rw [← icosianReflectionEdge_reduction_zero]
    exact icosianReflectionEdge_reduction_mem k 0
  rcases icosianReflectionEdgeParameters_span a with rfl | rfl | rfl | rfl
  · exact hk 0
  · exact hk 1
  · exact hk 2
  · simpa [icosianGlueUnipotent_mul,icosianReflectionEdgeParameter] using
      icosianReflectionGlueImage.mul_mem (hk 1) (hk 2)

theorem icosianReflection_unipotent_second (b : GoldenFour) :
    icosianGlueUnipotent 0 b∈icosianReflectionGlueImage := by
  have h := icosianReflectionGlueImage.mul_mem
    (icosianReflection_unipotent_paired b) (icosianReflection_unipotent_first b)
  rw [icosianGlueUnipotent_mul,add_zero] at h
  have hz : ∀ z : GoldenFour, z + z = 0 := by decide +kernel
  have hb : b+b=0 := hz b
  rwa [hb] at h

end Atlas.Conway
