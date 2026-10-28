module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryArrangement

/-!
# Full Sylow control on the original field-fixed layer

The arranged ambient Sylow retains the original module and field witness.
E.6.1 and natural-offender exclusion control both Thompson normalizers,
promoting the local Sylow to N_G(U) and C_G(U). The actual central fixed
point then proves their membership in He. No full-normalizer Sylow or
characteristic-two conclusion is assumed.
Source: Aschbacher–Smith, 6.1.14(1–2), printed pp.670–671.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- The full relative Sylow and even-characteristic assertions of 6.1.14. -/
theorem source_field_fixedSpace_sylow_geometry
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
      normalizer (elementaryAbelianMaxJ
        ((P : Subgroup G) ⊓ normalizer (U : Set G)) : Set G) ≤ normalizer (L : Set G) ∧
      normalizer (elementaryAbelianMaxJ
        ((P : Subgroup G) ⊓ centralizer (U : Set G)) : Set G) ≤ normalizer (L : Set G) ∧
      (∃ R : Sylow 2 (normalizer (U : Set G)),
        (R : Subgroup (normalizer (U : Set G))).map (normalizer (U : Set G)).subtype =
          (P : Subgroup G) ⊓ normalizer (U : Set G)) ∧
      (∃ R : Sylow 2 (centralizer (U : Set G)),
        (R : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
          (P : Subgroup G) ⊓ centralizer (U : Set G)) ∧
      normalizer (U : Set G) ∈ Chapter1.He G ∧
      centralizer (U : Set G) ∈ Chapter1.He G ∧
      generalizedFitting (normalizer (U : Set G)) =
        pCore 2 (normalizer (U : Set G)) := by
  let : IsElementaryAbelian 2 (commutatorLayer T L) := h611.layer_elementary
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  obtain ⟨P, hPL, hBP, hPB, hf, hSyl⟩ :=
    source_field_fixedSpace_sylow_arrangement D h h611 hnatural hfield hUne
  obtain ⟨hNJ, hCJ, hNS, hCS⟩ := field_fixedSpace_sylow_control hE
    (by have := h611.n_gt_one; omega) hnatural le_rfl hfield hUne P hBP hPB hSyl
  obtain ⟨hN, hC, hF⟩ := field_fixedSpace_even_local P
    (h.simpleQTKE.evenCharacteristic P) hBP hPB hf hUne
  exact ⟨P, hPL, hBP, hPB, hf, hNJ, hCJ, hNS, hCS, hN, hC, hF⟩
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
