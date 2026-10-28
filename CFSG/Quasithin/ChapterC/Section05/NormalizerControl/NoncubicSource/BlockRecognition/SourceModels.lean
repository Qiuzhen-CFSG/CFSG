module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceShort
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceAction
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.ShortModels
/-!
# The original auxiliary span is one of the two A₇ blocks

Original source model selection, the full moved-action equivalence and
its dual ratio construct the actual alternating or exceptional A₇ block.
The universal A.3.12 input is retained; no block-type, irreducibility or
module-identification premise remains in the original source wrappers.
The final matching with the two original K markings is a separate step.
Source: Aschbacher–Smith C.5.13, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem noncubic_source_block_types {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hL : IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))))
    (hmodel : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let V := conjugateSpanBy (omegaOneCenterAmbient T) N
      let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
      let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
      IsAlternating (DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)) 7)
    (hq : let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
      let V := conjugateSpanBy (omegaOneCenterAmbient T) N
      let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
      let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
      let : IsElementaryAbelian 2 V := hs.1
      let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
      quadraticRatio (DualOffender.movedRepresentation (V.subgroupOf N) (K.subgroupOf N)).dual ≤ 2) :
    IsAlternatingBlock (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) 7 ∨
    IsExceptionalA7Block (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let L := conjugateSpanBy K N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  let : IsElementaryAbelian 2 (blockU L) := hL.elementary
  let : IsElementaryAbelian 2 (BlockModule L) := hL.module_elementary
  have hKN : K ≤ N := (noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS).1.1
  have hi := DualOffender.noncubic_source_moved_core K T X hK h3 hT hUT hTK P hP hA hAX S hS
  have hk := (EmbeddingSelection.source_component_kernel K T X hK h3 hT hUT hTK P hP hA hAX hX S hS).1
  obtain ⟨E⟩ := DualOffender.source_blockU_actionEquiv_of_moved V K N hs.2.1 hKN hs.2.2.1
    hi.2.2.2.2 hL hk
  have hc := blockModule_dual_cubic_le_of_image hL
    (DualOffender.movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) E
    ((cubicRatio_le_quadraticRatio _).trans hq)
  have hLH : L ∈ Chapter1.H G := by
    intro hz
    apply hL.core_ne_bot
    exact (map_eq_bot_iff_of_injective (pCore 2 L) L.subtype_injective).mp hz
  obtain ⟨e⟩ := hmodel
  exact short_a7_blocks_of_dual_cubic hL
    (Chapter1.Section02.uniqueness_local_quotient_sqtk hG hLH) (E.groupEquiv.trans e) hc
omit [Finite G] in
private theorem not_three_of_four {K : Subgroup G}
    (hfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) : ¬ IsAlternatingBlock K 3 := by
  intro h3
  have hc := EmbeddingSelection.binary_card (n := 2) (by simpa using hfour)
  norm_num at hc
  obtain ⟨e⟩ := h3.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hc
  norm_num at hc
theorem natural_source_a7_blocks {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
    L = K ∨ (IsL2EvenBlock K 2 ∨ IsAlternatingBlock K 5) ∧
      (IsAlternatingBlock L 7 ∨ IsExceptionalA7Block L) := by
  have hs := natural_source_short hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc
  rcases natural_source_models hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,noncubic_source_block_types hG K T X (Or.inl ⟨n,hn⟩)
      (not_three_of_four hfour) hT (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS
      hs hmodel (DualOffender.natural_source_moved_dual_ratio h hn hT hTK P hP X hA hAX hx hnc)⟩

theorem alternating_source_a7_blocks {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
    (hA312 : ∀ (H : Type u) [Group H] [Finite H],
      IsSQTK 𝒦 H → pCore 2 H = ⊥ → ∀ (S : Sylow 2 H) (B : Subgroup H),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
    L = K ∨ (IsL2EvenBlock K 2 ∨ IsAlternatingBlock K 5) ∧
      (IsAlternatingBlock L 7 ∨ IsExceptionalA7Block L) := by
  have hs := alternating_source_short hG hA312 h hTK P hP X hA hAX hX S hS hx hnc
  rcases alternating_source_models hG hA312 h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,noncubic_source_block_types hG K T X (Or.inr (Or.inr h.block))
      (not_three_of_four hfour) h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS
      hs hmodel (DualOffender.alternating_source_moved_dual_ratio h hTK P hP X hA hAX hx hnc)⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
