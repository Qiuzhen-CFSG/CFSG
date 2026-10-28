module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Kernel
public import Theory.GroupTheory.CentralizerResidualProducts

/-!
# Transporting the surviving C.5.13 component models

The canonical quotient map N/O₂(N) → N/C_N(V) is injective on the actual
normal closure image by the component-kernel theorem. Its restriction is
therefore an isomorphism, preserving all five surviving A.3.12 model types,
including the nonsplit triple cover. The ambient quotients are not identified.
This family supplies transport only; the row selection remains a separate
application of the actual A.3.12 embedding and the Sylow budget.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The restriction of the canonical ambient quotient map is an isomorphism
on the actual containing-component image. -/
theorem source_component_image_equiv (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let L := conjugateSpanBy K N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    Nonempty (((L.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) ≃*
      DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let L := conjugateSpanBy K N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let f := twoCoreToCentralizer (V.subgroupOf N) hs.2.2.2.2.2.2.1
  let C := (L.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))
  have hf := (source_component_kernel K T X hK h3 hT hUT hTK P hP hA hAX hX S hS).2.2
  let e := MulEquiv.ofBijective (f.subgroupMap C) ⟨hf,f.subgroupMap_surjective C⟩
  have hKN : K ≤ N := le_sup_left.trans (le_inf hAX ((K ⊔ T).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
  have him : C.map f = DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N) := by
    rw [DualOffender.closureImage,normalClosure_subgroupOf_eq_conjugateSpanBy K N hKN]
    exact twoCoreToCentralizer_image (V.subgroupOf N) (L.subgroupOf N) hs.2.2.2.2.2.2.1
  exact ⟨e.trans (MulEquiv.subgroupCongr him)⟩

/-- The exceptional triple cover is transported with its actual central
three-group and quotient, not replaced by the simple alternating group. -/
theorem alternatingCover_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) {m : ℕ} (h : IsAlternatingCover A m) : IsAlternatingCover B m := by
  obtain ⟨hq,⟨z⟩,⟨s⟩⟩ := h
  let : IsQuasisimple A := hq
  refine ⟨IsQuasisimple.of_mulEquiv e, ⟨(centerCongr e).symm.trans z⟩, ?_⟩
  let eq := QuotientGroup.congr (center A) (center B) e (map_center_equiv e)
  exact ⟨eq.symm.trans s⟩

/-- Every surviving A.3.12 model crosses the actual component isomorphism.
This is solely transport; the row selection is proved separately. -/
theorem surviving_models_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B)
    (h : IsAlternating A 7 ∨ IsAlternatingCover A 7 ∨ Nonempty (A ≃* Janko1.Model) ∨
      ClassicalGroup.IsPSL A 2 25 ∨
      ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL A 2 p) :
    IsAlternating B 7 ∨ IsAlternatingCover B 7 ∨ Nonempty (B ≃* Janko1.Model) ∨
      ClassicalGroup.IsPSL B 2 25 ∨
      ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL B 2 p := by
  rcases h with h | h | h | h | ⟨p,hp,h⟩
  · obtain ⟨a⟩ := h
    exact .inl ⟨e.symm.trans a⟩
  · exact .inr (.inl (alternatingCover_transport e h))
  · obtain ⟨a⟩ := h
    exact .inr (.inr (.inl ⟨e.symm.trans a⟩))
  · exact .inr (.inr (.inr (.inl (h.of_mulEquiv e.symm))))
  · exact .inr (.inr (.inr (.inr ⟨p,hp,h.of_mulEquiv e.symm⟩)))
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
