module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.Source
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The original C.5.13 binary image and Sylow order budget

Both noncubic source block types give a binary PSL₂ quotient. The original
full Sylow image in N/C_N(V) acts faithfully on that same image, so the
semilinear automorphism order bounds its two-part. The central-cover seed,
Sylow image and faithfulness are all supplied by the proved source setup.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem noncubic_binary_model (K : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3) :
    ∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) := by
  rcases hK with ⟨n,hn⟩ | ha | ha
  · obtain ⟨hdegree, _, _, _, _, _, hm, _⟩ := hn
    exact ⟨n,hdegree,hm⟩
  · exact (h3 ha).elim
  · obtain ⟨e⟩ := ha.2.2.quotient_iso
    have hc : Nat.card (GaloisField 2 2) = 2^2 := GaloisField.card 2 2 (by decide)
    obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card (GaloisField 2 2) = 4 by simpa using hc)
    exact ⟨2,by decide,GaloisField 2 2,inferInstance,inferInstance,hc,⟨e.trans f.symm⟩⟩

theorem source_binary_sylow_budget (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let V := conjugateSpanBy (omegaOneCenterAmbient T) N
    let hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
    let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
    let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
    ∃ n : ℕ, 1 < n ∧ ClassicalGroup.IsPSL ((K.subgroupOf N).map q) 2 (2^n) ∧
      ∃ Q : Sylow 2 (N ⧸ centralizer (V.subgroupOf N : Set N)),
        (Q : Subgroup _) = (T.subgroupOf N).map q ∧ Nat.card Q ∣ 2^n*n := by
  let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  let q := QuotientGroup.mk' (centralizer (V.subgroupOf N : Set N))
  obtain ⟨hSyl,hNorm,hfaith,⟨e⟩⟩ :=
    noncubic_source_quotient_action K T X hK h3 hT hUT hTK P hP hA hAX S hS
  obtain ⟨n,hn,hm⟩ := noncubic_binary_model K hK h3
  have hmodel := hm.of_mulEquiv e.symm
  obtain ⟨Q,hQ⟩ := hSyl
  refine ⟨n,hn,hmodel,Q,hQ,?_⟩
  apply binary_normalizer_card_dvd Q ((K.subgroupOf N).map q) (by omega) hmodel
  · simpa only [hQ] using hNorm
  · simpa only [hQ] using hfaith
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
