module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.MovedInterval
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.Original
/-!
# The source auxiliary group has the C.1.7 irreducible block interval

Original C.5.13 model selection and the five-element displacement calculation
prove Irr⁺ on the full moved module. The source identity [V₁,L]=U(L) then
transports that result to the intrinsic block interval. The equality branch
L=K uses the original block marking. Both original natural and A₅ inputs
therefore give BlockModuleIrreducible L, with the genuine universal A.3.12
input retained and no assumed irreducibility or split central cover.
Source: Aschbacher–Smith C.5.13, printed p.163.
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
theorem natural_source_blockModuleIrreducible {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    BlockModuleIrreducible (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := natural_source_omega_span h hn hT hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  rcases natural_source_moved_IrrPlus hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_htype,hfour,_hmodel,hirr⟩
  · rw [he]
    exact h.short.irreducible
  · have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
      (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
    have hm := DualOffender.noncubic_source_moved_core K T X (Or.inl ⟨n,hn⟩) (not_three_of_four hfour)
      hT (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
    exact DualOffender.source_blockModuleIrreducible_of_moved V K N hs.2.1 hKN hs.2.2.1
      hm.2.2.2.2 hirr

theorem alternating_source_blockModuleIrreducible {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
    BlockModuleIrreducible (conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G))) := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := alternating_five_source_omega_span h hTK P hP X hA hAX
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let : IsElementaryAbelian 2 V := hs.1
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hs.2.1
  rcases alternating_source_moved_IrrPlus hG hA312 h hTK P hP X hA hAX hX S hS hx hnc with he | ⟨_htype,hfour,_hmodel,hirr⟩
  · rw [he]
    exact h.block.2.1.irreducible
  · have hKN : K ≤ N := le_inf (le_sup_left.trans hAX)
      (le_sup_left.trans ((K ⊔ T).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ T) (pCore 2 (K ⊔ T : Subgroup G)))))
    have hm := DualOffender.noncubic_source_moved_core K T X (Or.inr (Or.inr h.block)) (not_three_of_four hfour)
      h.twoGroup (h.module_le.trans inf_le_left) hTK P hP hA hAX S hS
    exact DualOffender.source_blockModuleIrreducible_of_moved V K N hs.2.1 hKN hs.2.2.1
      hm.2.2.2.2 hirr

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
