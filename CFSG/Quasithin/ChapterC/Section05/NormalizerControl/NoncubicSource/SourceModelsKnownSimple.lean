module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryContaining
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SourceComponentKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceCoreAction

/-!
# The complete containing-model catalogue on the original C.5.13 quotient

The original noncubic block supplies its binary simple image in the actual
auxiliary two-core quotient. The constructed conjugate-span C-component
contains that image, hence has two-rank at least two and is quasisimple.
The full known-simple A.3.6 theorem then supplies the literal simple or
triple-cover model for this same containing image.

This is the source model input for inspecting the proper embeddings in
C.5.13. The complete Theorem C list, including Held and J₄, is retained;
no universal A.3.12 implication or new model-recognition premise is used.
Source: Aschbacher–Smith C.5.13, printed pp.162–163, using A.3.6.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open Chapter1.Section02 Chapter1.Section02.LocalModels
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

private theorem source_auxiliary_sqtk_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hlocal := (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX P hP).1
  have hcore : A.pCoreIn 2 ≤ N.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAN) inf_le_right
  have hNH : N ∈ Chapter1.H G := by
    intro he
    exact hlocal.2.2.2 (bot_unique (hcore.trans he.le))
  exact uniqueness_local_quotient_sqtk hG hNH

/-- The containing component on the actual C.5.13 quotient is quasisimple
and belongs to the complete simple-or-triple-cover catalogue. Every input
is part of the original QTKE, block, Sylow and characteristic-two setup. -/
theorem source_twoCore_component_models_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let D := ((conjugateSpanBy K N).subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
    IsQuasisimple D ∧
      ((IsSimpleGroup D ∧ TheoremCModel D) ∨
        (Nonempty (center D ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel D)) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let L := conjugateSpanBy K N
  let r := QuotientGroup.mk' (pCore 2 N)
  let B := (K.subgroupOf N).map r
  let D := (L.subgroupOf N).map r
  have hL := noncubic_source_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  obtain ⟨_Q, _hQ, _hmem, _hquasi, _hNorm, _hfaith, _hK, n, hn, hm⟩ :=
    EmbeddingSelection.source_twoCore_sylow_action K T X hK h3 hT hUT hTK P hP hA hAX hX S hS
  have hBD : B ≤ D := map_mono (subgroupOf_mono N (le_conjugateSpanBy K N))
  let := pCore_isNilpotent (p := 2) (G := N)
  have hD : D.IsCComponent := hL.map_quotient (pCore 2 N)
  exact ChapterA.Section03.SourceEmbeddings.binary_containing_component_models_knownSimple
    (source_auxiliary_sqtk_knownSimple hG K T X hK h3 hTK hAX hX S hS)
    (pCore_quotient_pCore_eq_bot 2) hD hBD hn hm

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
