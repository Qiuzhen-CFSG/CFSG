module
public import CFSG.Quasithin.Chapter13.Section05.SourceAssembly.A5Point
public import CFSG.Quasithin.Chapter13.Section05.SourceAssembly.OrdinarySix

/-!
# Assembly after the original alternating source preparation

The two prepared alternatives keep the same L, V and source flag. The
A₅ case uses the marked Context; the ordinary-A₆ case keeps the natural
central action, the actual two-core quotient marking and local maximality.
Their positive recognition theorems give exactly ModelConclusion G n.

This is a conditional assembly interface, not the full Theorem 13.5.12.
The preceding source must construct the prepared data and handle the
triple-cover A₆ branch before this can discharge the full theorem.
Source: Aschbacher–Smith, Theorem 13.5.12, printed p.918.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.SourceAssembly
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} {n : ℕ}

/-- Assemble both ordinary prepared branches without a recognition callback. -/
theorem modelConclusion_of_prepared_source
    (hdata :
      (n = 5 ∧ Nonempty (A5Source.Context T L V V₁ V₂ V₃)) ∨
      (n = 6 ∧ Nonempty (NaturalSixContext T L V V₁ V₂ V₃
        (normalizer (L : Set G)) (normalizer (V₁ : Set G))) ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        L ∈ Chapter1.LStar G (T : Subgroup G)))
    (hU : ¬ IsMulCommutative (conjugateSpanBy V₃ (normalizer (V₁ : Set G)))) :
    ModelConclusion G n := by
  rcases hdata with ⟨rfl,⟨d⟩⟩ | ⟨rfl,⟨d⟩,⟨e⟩,hmax⟩
  · exact A5Source.source_point_seed_modelConclusion d hU
  · exact ordinary_six_modelConclusion d e hmax hU
end CFSG.Quasithin.Chapter13.Section05.SourceAssembly
