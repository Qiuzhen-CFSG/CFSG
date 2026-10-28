module

public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalTheorem
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.AlternatingTheorem
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalModelsKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalNormalizerKnownSimple

/-!
# The complete original C.5.13 over the known-simple catalogue

The proved source selector gives the actual A₇ action image and the
original block parameter. The original moved-module displacement supplies
Irr⁺, and its literal action transport supplies the intrinsic irreducible
interval and shortness of the auxiliary span. The A₇ module recognition
and five-letter or natural-plane restriction then match the enlarged block
to the original marking. The independently proved normalizer bound gives
the other assertion of C.5.13.

Both the natural and A₅ statements retain their original configurations
and quotient maps. The full source catalogue discharges A.3.12's use on
this auxiliary quotient; no classification premise remains here.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem not_three_of_four {K : Subgroup G}
    (hfour : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4) : ¬ IsAlternatingBlock K 3 := by
  intro h3
  have hc := EmbeddingSelection.binary_card (n := 2) (by simpa using hfour)
  norm_num at hc
  obtain ⟨e⟩ := h3.2.2.quotient_iso
  rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup] at hc
  norm_num at hc
private theorem natural_source_moved_IrrPlus_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let L := conjugateSpanBy K N
    let hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    L = K ∨ (IsL2EvenBlock K 2 ∨ IsAlternatingBlock K 5) ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
      IsAlternating (DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 ∧
      IsIrrPlus (DualOffender.movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤ := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  rcases natural_source_models_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc with
    he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,hfour,hmodel,
      DualOffender.natural_source_moved_isIrrPlus K T X (Or.inl ⟨n,hn⟩)
        (not_three_of_four hfour) hT (h.module_le.trans inf_le_left) hTK
        P hP hA hAX S hS hfour h hn hmodel⟩

private theorem alternating_source_moved_IrrPlus_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let L := conjugateSpanBy K N
    let hs := alternating_five_source_omega_span h hTK P hP X hA hAX
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let : IsElementaryAbelian 2 V := hs.1
    let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
    L = K ∨ (IsL2EvenBlock K 2 ∨ IsAlternatingBlock K 5) ∧
      ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
      IsAlternating (DualOffender.closureImage (V.subgroupOf N) (K.subgroupOf N)) 7 ∧
      IsIrrPlus (DualOffender.movedRepresentation (V.subgroupOf N) (K.subgroupOf N)) ⊤ ⊤ := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  rcases alternating_source_models_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc with
    he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,hfour,hmodel,
      DualOffender.alternating_source_moved_isIrrPlus K T X (Or.inr (Or.inr h.block))
        (not_three_of_four hfour) h.twoGroup (h.module_le.trans inf_le_left) hTK
        P hP hA hAX S hS hfour h hmodel⟩


private theorem natural_source_blockModuleIrreducible_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    BlockModuleIrreducible (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  rcases natural_source_moved_IrrPlus_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_htype,hfour,_hmodel,hirr⟩
  · rw [he]
    exact h.short.irreducible
  · have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
      (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
    have hm := DualOffender.noncubic_source_moved_core K T X (Or.inl ⟨n,hn⟩) (not_three_of_four hfour)
      hT (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
    exact DualOffender.source_blockModuleIrreducible_of_moved V K N hs.2.1 hKN hs.2.2.1
      hm.2.2.2.2 hirr

private theorem alternating_source_blockModuleIrreducible_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    BlockModuleIrreducible (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  rcases alternating_source_moved_IrrPlus_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_htype,hfour,_hmodel,hirr⟩
  · rw [he]
    exact h.block.2.1.irreducible
  · have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
      (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
    have hm := DualOffender.noncubic_source_moved_core K T X (Or.inr (Or.inr h.block)) (not_three_of_four hfour)
      h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
    exact DualOffender.source_blockModuleIrreducible_of_moved V K N hs.2.1 hKN hs.2.2.1
      hm.2.2.2.2 hirr


private theorem natural_source_short_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  have hirr := natural_source_blockModuleIrreducible_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc
  rcases natural_source_models_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_,hfour,hmodel⟩
  · rw [he]
    exact h.short
  · exact source_short_of_interval K T X (Or.inl ⟨n,hn⟩) (not_three_of_four hfour)
      hT (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS hmodel hirr

private theorem alternating_source_short_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    IsShort (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  have hirr := alternating_source_blockModuleIrreducible_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc
  rcases alternating_source_models_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_,hfour,hmodel⟩
  · rw [he]
    exact h.block.2.1
  · exact source_short_of_interval K T X (Or.inr (Or.inr h.block)) (not_three_of_four hfour)
      h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS hmodel hirr


private theorem natural_source_a7_blocks_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
  have hs := natural_source_short_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc
  rcases natural_source_models_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,noncubic_source_block_types hG K T X (Or.inl ⟨n,hn⟩)
      (not_three_of_four hfour) hT (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS
      hs hmodel (DualOffender.natural_source_moved_dual_ratio h hn hT hTK P hP X hA hAX hx hnc)⟩

private theorem alternating_source_a7_blocks_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
  have hs := alternating_source_short_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc
  rcases alternating_source_models_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,noncubic_source_block_types hG K T X (Or.inr (Or.inr h.block))
      (not_three_of_four hfour) h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX hX S hS
      hs hmodel (DualOffender.alternating_source_moved_dual_ratio h hTK P hP X hA hAX hx hnc)⟩


namespace Matching
private theorem natural_source_matched_block_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    L = K ∨ IsL2EvenBlock K 2 ∧ IsExceptionalA7Block L := by
  let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
  rcases natural_source_a7_blocks_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨hK,hL⟩
  · exact Or.inl he
  have hK2 : IsL2EvenBlock K 2 := by
    rcases hK with hK | hK
    · exact hK
    · obtain ⟨F0,_,_,hF0,hPSL,_⟩ := hn.2.2
      have hn2 := EmbeddingSelection.binary_parameter_of_alternating_five (by have := hn.1; omega)
        hPSL hK.2.2.quotient_iso
      simpa only [hn2] using hn
  rcases hL with hL | hL
  · exfalso
    have h3 : ¬ IsAlternatingBlock K 3 := by
      intro h3
      obtain ⟨F0,_,_,hF0,hPSL,_⟩ := hK2.2.2
      have hc := EmbeddingSelection.binary_card hPSL
      obtain ⟨e3⟩ := h3.2.2.quotient_iso
      rw [Nat.card_congr e3.toEquiv,nat_card_alternatingGroup] at hc
      norm_num at hc
    obtain ⟨hKL,hk,hU,R,hR⟩ := source_matching_data K T X
      (Or.inl ⟨2,hK2⟩) h3 hT (h.module_le.trans inf_le_left)
      hTK P hP hA hAX hX S hS
    have hU' : (blockU K).map (inclusion hKL) ≤ blockU L := by
      rintro l ⟨k,hk,rfl⟩
      obtain ⟨l,hl,he⟩ := hU (mem_map_of_mem K.subtype hk)
      exact (Subtype.ext he : l = inclusion hKL k) ▸ hl
    exact no_natural_two_in_alternating_seven hK2 hL (inclusion hKL)
      (inclusion_injective hKL) hU' hk R (by simpa only [inclusion_range] using hR)
  · exact Or.inr ⟨hK2,hL⟩
private theorem alternating_source_matched_block_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
    L = K ∨ IsAlternatingBlock L 7 := by
  let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
  rcases alternating_source_a7_blocks_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_,hL⟩
  · exact Or.inl he
  rcases hL with hL | hL
  · exact Or.inr hL
  exfalso
  have h3 : ¬ IsAlternatingBlock K 3 := by
    intro h3
    obtain ⟨e5⟩ := h.block.2.2.quotient_iso
    obtain ⟨e3⟩ := h3.2.2.quotient_iso
    have hc := Nat.card_congr (e5.symm.trans e3).toEquiv
    rw [nat_card_alternatingGroup, nat_card_alternatingGroup] at hc
    norm_num at hc
  obtain ⟨hKL,hk,hU,R,hR⟩ := source_matching_data K T X
    (Or.inr (Or.inr h.block)) h3 h.twoGroup (h.module_le.trans inf_le_left)
    hTK P hP hA hAX hX S hS
  obtain ⟨eL⟩ := hL.2.1
  obtain ⟨Q,hQ⟩ := exists_quotient_sylow_normalizing hKL eL R hR
  apply no_alternating_five_in_exceptional h.block hL (inclusion hKL)
    (inclusion_injective hKL) _ eL hk Q hQ
  rintro l ⟨k,hk,rfl⟩
  have hh := hU (mem_map_of_mem K.subtype hk)
  obtain ⟨l,hl,he⟩ := hh
  exact (Subtype.ext he : l = inclusion hKL k) ▸ hl
end Matching

theorem natural_source_theorem_5_13_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
    ((X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (U K : Set G)) ∧ (L = K ∨ IsL2EvenBlock K 2 ∧ IsExceptionalA7Block L) := by
  exact ⟨natural_source_normalizer_control_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc,
    Matching.natural_source_matched_block_knownSimple hG h hn hT hTK P hP X hA hAX hX S hS hx hnc⟩

theorem alternating_source_theorem_5_13_knownSimple (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {K T J : Subgroup G} (h : AlternatingPairSetup T K J)
    (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (X : Subgroup G) (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    {x : G} (hx : x ∈ normalizer (T : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let L := conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))
    ((X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) ⊓ normalizer (T : Set G) ≤
      normalizer (sourceModule K : Set G)) ∧ (L = K ∨ IsAlternatingBlock L 7) := by
  exact ⟨alternating_source_normalizer_control_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc,
    Matching.alternating_source_matched_block_knownSimple hG h hTK P hP X hA hAX hX S hS hx hnc⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
