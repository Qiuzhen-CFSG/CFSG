module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryArrangement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedWeakClosure

/-!
# The field-witness Sylow arrangement on the original layer

E.6.1 controls the full normalizer of the natural layer. Its TI property
therefore places the field actor in an ambient Sylow P preserving L and B,
with N_P(U) Sylow in N_M(U). The field witness is retained on the literal
quotient and has the same fixed subgroup. No involution lift is assumed.
Source: Aschbacher–Smith, opening of 6.1.14, printed pp.670–671.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- Choose the source Sylow while preserving the original natural layer. -/
theorem source_field_fixedSpace_sylow_arrangement
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) :
    ∃ P : Sylow 2 G,
      (P : Subgroup G) ≤ normalizer (L : Set G) ∧ commutatorLayer T L ≤ P ∧
      (P : Subgroup G) ≤ normalizer (commutatorLayer T L : Set G) ∧
      IsInvolutoryFieldFixedSpace L (P : Subgroup G) (commutatorLayer T L) U n ∧
      ∃ R : Sylow 2 ((normalizer (L : Set G)) ⊓ normalizer (U : Set G) : Subgroup G),
        (R : Subgroup ((normalizer (L : Set G)) ⊓ normalizer (U : Set G) : Subgroup G)).map
          ((normalizer (L : Set G)) ⊓ normalizer (U : Set G)).subtype =
            (P : Subgroup G) ⊓ normalizer (U : Set G) := by
  let : IsElementaryAbelian 2 (commutatorLayer T L) := h611.layer_elementary
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  obtain ⟨P, hPM, hBP, _, hPB, hf, hSyl⟩ := field_fixedSpace_sylow_arrangement
    T L (normalizer (L : Set G)) (commutatorLayer T L) U n
    h611.sylow_normalizes_layer hE.normalizer_le le_rfl
    (fun g hg => natural_layer_ti h611 hnatural hg) hnatural hfield hUne
  exact ⟨P, hPM, hBP, hPB, hf, hSyl⟩
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
