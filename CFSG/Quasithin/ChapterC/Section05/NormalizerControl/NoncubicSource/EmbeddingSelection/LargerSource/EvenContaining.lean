module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.EvenModels
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.ComponentKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverSource
/-!
# Even-characteristic exclusions on the literal larger C.5 quotient

Restrict the original quotient Sylow to the actual containing component.
The smaller image retains local membership, normalization and its binary
model under the subgroup inclusion. The intrinsic carrier exclusions then
apply without asserting that the full original quotient Sylow is faithful.

The final source application constructs all these subgroup data from the
original block, its auxiliary-span equality and its centralizing module
span. Only the binary row is selected from the proved smaller-image list.
Source: Aschbacher–Smith C.5.12–13, printed pp.162–163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open Chapter1.Section02 Chapter1.Section02.LocalModels ChapterA.Section03.SourceEmbeddings
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem binary_containing_even_exclusions
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hL : L.IsCComponent)
    (hBL : B ≤ L) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    {n : ℕ} (hn : 1 < n) (hmodel : ClassicalGroup.IsPSL B 2 (2^n)) :
    (∀ m, 1 ≤ m → ¬ Triality.Standard.IsTrialityGroupAt (2^m) L) ∧
    (∀ m, 1 ≤ m → ¬ IsReeF4At L m) ∧
    (∀ name : ClassificationModels.SporadicName, name ≠ .j3 →
      ¬ Nonempty (L ≃* name.Carrier)) ∧ ¬ IsM22Cover L := by
  obtain ⟨S,_,hloc,hnorm⟩ := exists_local_sylow_normalizing T hB hL.subnormal hBL hTB
  let : IsQuasisimple (B.subgroupOf L) := quasisimple_subgroupOf hBL
  have hm := hmodel.of_mulEquiv (subgroupOfEquivOfLe hBL)
  exact ⟨fun _ he => not_binary_local_triality S hloc hnorm (by omega) he hm,
    fun _ he => not_binary_local_ree S hloc hnorm (by omega) he hm,
    fun name he => not_binary_local_sporadic S hloc hnorm hn hm name he,
    not_binary_local_m22_cover S hloc hnorm hn hm⟩

/-- The analogous central-cover exclusion uses only the genuine carrier's E. -/
theorem not_sl2_five_containing_even
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hL : L.IsCComponent)
    (hBL : B ≤ L) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hE : IsEvenCharacteristic L) (hmodel : IsSL B 2 5) : False := by
  obtain ⟨S,_,hloc,hnorm⟩ := exists_local_sylow_normalizing T hB hL.subnormal hBL hTB
  let : IsQuasisimple (B.subgroupOf L) := quasisimple_subgroupOf hBL
  exact not_sl2_five_local_of_evenCharacteristic S (hE S) hloc hnorm
    (by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
      exact ⟨F,inferInstance,inferInstance,hF,⟨(subgroupOfEquivOfLe hBL).trans e⟩⟩)

theorem not_sl2_five_containing_m22_cover
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ ChapterA.Section03.localCComponents T) (hL : L.IsCComponent)
    (hBL : B ≤ L) [IsQuasisimple B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hmodel : IsSL B 2 5) (hcover : IsM22Cover L) : False := by
  obtain ⟨S,_,hloc,hnorm⟩ := exists_local_sylow_normalizing T hB hL.subnormal hBL hTB
  let : IsQuasisimple (B.subgroupOf L) := quasisimple_subgroupOf hBL
  exact not_sl2_five_of_faithful_sylow S _ hnorm
    (sylow_faithful_of_m22_cover S hloc hnorm hcover)
    (by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hmodel
      exact ⟨F,inferInstance,inferInstance,hF,⟨(subgroupOfEquivOfLe hBL).trans e⟩⟩)

/-- The local subgroup data for the original larger quotient; every structural
premise is discharged from the literal auxiliary-span equality. -/
theorem source_larger_restricted_setup_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hTK : T ≤ normalizer (K : Set G)) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hLK : conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K) :
    let r := QuotientGroup.mk' (pCore 2 X)
    let B := (K.subgroupOf X).map r
    let E := ((conjugateSpanBy K X).subgroupOf X).map r
    let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
    B ∈ ChapterA.Section03.localCComponents Q ∧ E.IsCComponent ∧ B ≤ E ∧
      (Q : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (B : Set (X ⧸ pCore 2 X)) := by
  let r := QuotientGroup.mk' (pCore 2 X)
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hlocal := (source_larger_local_family_knownSimple hG K T X hK h3 hTK hAX hX S hS).1
  rw [hLK] at hlocal
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : K.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hKX).mp hlocal
  have hD := source_larger_span_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
  let := pCore_isNilpotent (p := 2) (G := X)
  refine ⟨mem_L_map_twoCore_mem_localCComponents hmem,hD.map_quotient _,
    map_mono (subgroupOf_mono X (le_conjugateSpanBy K X)),?_⟩
  have hnorm : (S : Subgroup X) ≤ normalizer (K.subgroupOf X : Set X) := by
    rw [← hTs, ← subgroupOf_normalizer_eq hKX]
    exact comap_mono hTK
  exact (map_mono hnorm).trans (le_normalizer_map r)

/-- Triality, Ree and all sporadic rows are excluded on the exact image of
⟨K^X⟩ in X/O₂(X), whenever the proved smaller image is in its binary row. -/
theorem source_larger_binary_even_exclusions_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K T X : Subgroup G) (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hLK : conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K)
    {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL ((K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 2 (2^n)) :
    let E := ((conjugateSpanBy K X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    (∀ m, 1 ≤ m → ¬ Triality.Standard.IsTrialityGroupAt (2^m) E) ∧
    (∀ m, 1 ≤ m → ¬ IsReeF4At E m) ∧
    (∀ name : ClassificationModels.SporadicName, name ≠ .j3 →
      ¬ Nonempty (E ≃* name.Carrier)) ∧ ¬ IsM22Cover E := by
  obtain ⟨hloc,hE,hBE,hnorm⟩ :=
    source_larger_restricted_setup_knownSimple hG K T X hK h3 hTK hAX hX S hS hLK
  have hquasi := (noncubic_twoCore_small_models_with_quotient K T X hK h3 hUT hT hTK
    (le_sup_left.trans hAX) hX S hS hVC).1
  let : IsQuasisimple ((K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := hquasi
  exact binary_containing_even_exclusions
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))) hloc hE hBE hnorm hn hmodel

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
