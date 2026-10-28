module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ClosureModelSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryObstructionApplication

/-!
# The corrected closure-module step on the original reduced F1.11 triple

The actual reduced full-Borel core meets the adjacent-core closure in a
Sylow subgroup. Its image in the original completion is the intersection
of the original full Borel's two-core with the closure under the original
full endpoint. The literal center section then satisfies corrected 5.12
with fixed generation and actor placement discharged by the constructed
graph. The faithful module, full rank-one marking, vanishing residual
fixed space and replacement actor still require the remaining 6.4 argument.

Source: DGS, Groups and Graphs (1985), reduction p.95, corrected 5.12,
pp.113--115, and 6.4, pp.120--121. The original completion may be infinite;
its original S is not identified with the full Borel's actual two-core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
open Representation Representation.BinaryConjugationSection Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The exact original-completion image of the constructed closure Sylow. -/
theorem reduced_original_closure_sylow_intersection (h : HypothesisF11 L S) (i : Fin 2) :
    let P := fun j => (P₀ L S j).subgroupOf (G₀ L S)
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    ∃ T : Sylow 2 X, (T : Subgroup X).map ((G₀ L S).subtype.comp X.subtype) =
      (commonBorel L S).pCoreIn 2 ⊓
        conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)) := by
  obtain ⟨T,hT⟩ := source_closure_sylow_intersection (reduced_triple h)
    (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i
  refine ⟨T, ?_⟩
  rw [←map_map,hT,map_inf _ _ _ (G₀ L S).subtype_injective,
    reduced_core_closure_full_image h i,
    map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le (show B₀ L S ≤ G₀ L S from
      (show B₀ L S ≤ P₀ L S 0 from le_sup_right).trans le_sup_left),B₀_core h]

/-- Actual reduced F1.11 application of corrected 5.12, with the same
section denominator, quotient map, actor and original core intersection. -/
theorem reduced_closure_section_model_selection
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    (h : HypothesisF11 L S)
    (i : Fin 2)
    (hn : ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ normalizer (↑((((P₀ L S i).subgroupOf (G₀ L S))).pCoreIn 2 ⊓ (((P₀ L S (other i)).subgroupOf (G₀ L S))).pCoreIn 2) : Set (G₀ L S)))
    (C A : Subgroup (G₀ L S))
    (σ : Representation (ZMod 2) D W)
    (π : conjugateSpanBy ((((P₀ L S i).subgroupOf (G₀ L S))).pCoreIn 2) (((P₀ L S (other i)).subgroupOf (G₀ L S))) →* D)
    (hπ : Function.Surjective π)
    (hk : π.ker = ((((P₀ L S (other i)).subgroupOf (G₀ L S))).pCoreIn 2).subgroupOf
      (conjugateSpanBy ((((P₀ L S i).subgroupOf (G₀ L S))).pCoreIn 2) (((P₀ L S (other i)).subgroupOf (G₀ L S)))))
    (d : BinaryConjugationSection (conjugateSpanBy ((((P₀ L S i).subgroupOf (G₀ L S))).pCoreIn 2) (((P₀ L S (other i)).subgroupOf (G₀ L S))))
      (sylowCenterSpan (((P₀ L S (other i)).subgroupOf (G₀ L S)))) C (σ.comp π))
    (M : BinaryRankOneModel D) (hf : Function.Injective σ)
    (hres : fixedSpace σ (pResidual 2 D) = ⊥)
    (hA : A ≤ (((P₀ L S i).subgroupOf (G₀ L S))).pCoreIn 2) (hout : ¬ A ≤ (((P₀ L S (other i)).subgroupOf (G₀ L S))).pCoreIn 2)
    (hquad : ⁅A,⁅A,sylowCenterSpan (((P₀ L S (other i)).subgroupOf (G₀ L S)))⁆⁆ ≤ C)
    (hindex : (centralizer (A : Set (G₀ L S))).relIndex (sylowCenterSpan (((P₀ L S (other i)).subgroupOf (G₀ L S)))) ≤
      ((((P₀ L S (other i)).subgroupOf (G₀ L S))).pCoreIn 2).relIndex A) :
    let X := conjugateSpanBy ((((P₀ L S i).subgroupOf (G₀ L S))).pCoreIn 2) (((P₀ L S (other i)).subgroupOf (G₀ L S)))
    ∃ T : Sylow 2 X, (T : Subgroup X).map X.subtype = ((B₀ L S).subgroupOf (G₀ L S)).pCoreIn 2 ⊓ X ∧
      ∃ U : Sylow 2 D, (U : Subgroup D) = (T : Subgroup X).map π ∧
        NaturalRealization σ U := by
  exact source_closure_section_model_selection (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i hn C A σ π hπ hk d M hf hres hA hout hquad hindex

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
