module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalFullSpan
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.SignedThreeModelControl
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverRows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.BinaryRows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.RankTwo
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SurvivingTransport
/-!
# The original natural larger-span row selection

The actual natural block image retains its possible SL2(5) central cover.
The proved full-span quasisimplicity and the genuine A.3.12 embedding
select exactly equality, the five binary-image models, or signed-three
models at five. The original field parameter, J4 exclusion and full-Sylow
rank-two residual equality are discharged by the source data.
Source: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]

theorem natural_full_span_selection
    {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK κ Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    {K T : Subgroup G} {F : Type*} [Field F]
    (h : Setup T K F) {n : ℕ} (hn : IsL2EvenBlock K n)
    (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hTK : T ≤ normalizer (K : Set G))
    (X : Subgroup G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T)
    (hVC : conjugateSpanBy (U K) X ≤ centralizer (U K : Set G))
    (hLK : conjugateSpanBy K (X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)) = K) :
    let D := conjugateSpanBy K X
    let r := QuotientGroup.mk' (pCore 2 X)
    (K.subgroupOf X).map r = (D.subgroupOf X).map r ∨ IsL2EvenBlock K 2 ∧
      ((IsAlternating ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 7 ∨
        IsAlternatingCover ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 7 ∨
        Nonempty (((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) ≃* Janko1.Model) ∨
        ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 25 ∨
        ∃ p, A312ExceptionalPrime p ∧ ClassicalGroup.IsPSL ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) 2 p) ∨
      IsSL ((K.subgroupOf X).map r) 2 5 ∧
        ∃ u, IsPSLSign ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) u 3 5 ∨
          IsSLSign ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) u 3 5) := by
  have hK : IsChiZeroBlock K := Or.inl ⟨n,hn⟩
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hUT : U K ≤ T := h.module_le.trans inf_le_left
  let D := conjugateSpanBy K X
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let E := (D.subgroupOf X).map r
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal := (source_larger_local_family hG hA312 K T X hK h3 hTK hAX hX S hS).1
  rw [hLK] at hlocal
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : K.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hKX).mp hlocal
  have hBmem : B ∈ ChapterA.Section03.localCComponents Q :=
    mem_L_map_twoCore_mem_localCComponents hmem
  obtain ⟨hD,hrows⟩ := source_larger_span_embedding hG hA312 K T X hK h3 hTK hAX hX S hS
  rw [hLK] at hrows
  let := pCore_isNilpotent (p := 2) (G := X)
  have hE : E.IsCComponent := hD.map_quotient (pCore 2 X)
  have hBE : B ≤ E := map_mono (subgroupOf_mono X (le_conjugateSpanBy K X))
  let f := r.subgroupMap (D.subgroupOf X)
  have hk : f.ker = pCore 2 (D.subgroupOf X) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hD.subnormal).symm
  let eD := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (r.subgroupMap_surjective _))
  let : IsQuasisimple ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) :=
    natural_source_full_span_quotient_quasisimple hG hA312 h hn hT hTK X hAX hX S hS hVC
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv eD
  obtain ⟨hb,m,hm,hmodel,hquot,hmodels⟩ := noncubic_twoCore_small_models_with_quotient
    K T X hK h3 hUT hT hTK hKX hX S hS hVC
  let : IsQuasisimple B := hb
  have hnat : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) :=
    hn.2.2.choose_spec.choose_spec.choose_spec.2.1
  have he : n=m := (binary_two_valuation (lt_of_lt_of_le (by decide : 0<2) hn.1) hnat).symm.trans
    (binary_two_valuation (by omega : 0<m) hmodel)
  have hnat2 (hm2 : m=2) : IsL2EvenBlock K 2 := (he.trans hm2) ▸ hn
  have hJ4 (hm2 : m=2) : ¬ Nonempty (E ≃* Janko4.Model) := by
    rintro ⟨e⟩
    exact natural_source_full_span_not_jankoFour h (hnat2 hm2) hT hTK X hKX hX S hS hVC ⟨eD.trans e⟩
  have hrank := fun hm hr => eq_of_rankTwo_parabolic_model Q hBmem hE hBE hm hr
  rcases hmodels with hb | ⟨hm2,hb⟩
  · rcases select_binary_rows_with_jankoFour_exclusion B E hm hb hBE hJ4 hrows hrank with hh | ⟨hm2,hmodels⟩
    · exact .inl hh
    · exact .inr ⟨hnat2 hm2,.inl (surviving_models_transport eD.symm hmodels)⟩
  · have hquot' : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by simpa only [hm2,Nat.reducePow] using hquot
    rcases select_sl2_five_rows B E hb hquot' hBE (hJ4 hm2) hrows hrank with hh | hmodels
    · exact .inl hh
    · exact .inr ⟨hnat2 hm2,.inr ⟨hb,signed_three_models_transport eD.symm hmodels⟩⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
