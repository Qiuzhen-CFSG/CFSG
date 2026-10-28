module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.OriginalModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.BlockRecognition.SourceIrrPlus

/-!
# Original C.5.13 data proves the unique noncentral moved section

The complete source model selection supplies either L=K or the literal
A₇ closure image and smaller L₂(4)/A₅ quotient. In the proper branch the
original natural or A₅ marking supplies the small displacement bound, and
the actual moved representation belongs to Irr⁺. No faithfulness, order-five,
module rank or irreducibility premise is added. Only genuine universal
A.3.12 remains as an earlier-source input.

Irr⁺ keeps the central layer: the central quotient is irreducible. Recognizing
its four or six dimensional model and constructing the full block record are
separate subsequent steps.
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
theorem natural_source_moved_IrrPlus {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
  rcases natural_source_models hG hA312 h hn hT hTK P hP X hA hAX hX S hS hx hnc with
    he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,hfour,hmodel,
      DualOffender.natural_source_moved_isIrrPlus K T X (Or.inl ⟨n,hn⟩)
        (not_three_of_four hfour) hT (h.module_le.trans inf_le_left) hTK
        P hP hA hAX S hS hfour h hn hmodel⟩

theorem alternating_source_moved_IrrPlus {𝒦 : GroupClass.{u}} (hG : IsSimpleQTKE 𝒦 G)
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
  rcases alternating_source_models hG hA312 h hTK P hP X hA hAX hX S hS hx hnc with
    he | ⟨htype,hfour,hmodel⟩
  · exact Or.inl he
  · exact Or.inr ⟨htype,hfour,hmodel,
      DualOffender.alternating_source_moved_isIrrPlus K T X (Or.inr (Or.inr h.block))
        (not_three_of_four hfour) h.twoGroup (h.module_le.trans inf_le_left) hTK
        P hP hA hAX S hS hfour h hmodel⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
