module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.NaturalRows
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.NaturalFullSpanKnownSimple
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.CoverKnownSimple
/-!
# The original natural larger-span selector up to the odd ternary parameter

The exact smaller quotient image is binary or SL2(5). The binary case now
has its complete known-simple selector. The full SL2(5) containing catalogue
leaves only signed degree-three groups over odd prime fields. All component,
quasisimplicity, quotient-kernel and model hypotheses are derived from the
original C.5 setup; only the remaining prime identification is separate.

The original natural module, centralizing span and auxiliary-span equality
are retained. No universal A.3.12 or embedding-list premise is used.
Source: Aschbacher–Smith C.5.12, printed p.163.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne Chapter1.Section02 Chapter1.Section02.LocalModels
universe u
variable {G : Type u} [Group G] [Finite G]
theorem natural_full_span_selection_prime_remainder
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
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
        ∃ p, p.Prime ∧ Odd p ∧ ∃ u,
          IsPSLSign ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) u 3 p ∨
          IsSLSign ((D.subgroupOf X) ⧸ pCore 2 (D.subgroupOf X)) u 3 p) := by
  have hK : IsChiZeroBlock K := Or.inl ⟨n,hn⟩
  have hKX : K ≤ X := le_sup_left.trans hAX
  have hTX : T ≤ X := le_sup_right.trans hAX
  have hUT : U K ≤ T := h.module_le.trans inf_le_left
  let D := conjugateSpanBy K X
  let r := QuotientGroup.mk' (pCore 2 X)
  let B := (K.subgroupOf X).map r
  let E := (D.subgroupOf X).map r
  let Q := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal := (source_larger_local_family_knownSimple hG K T X hK h3 hTK hAX hX S hS).1
  rw [hLK] at hlocal
  have hTs : T.subgroupOf X = (S : Subgroup X) := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX,hS]
  have hmem : K.subgroupOf X ∈ Chapter1.L X (S : Subgroup X) := by
    rw [← hTs]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTX hKX).mp hlocal
  have hBmem : B ∈ ChapterA.Section03.localCComponents Q :=
    mem_L_map_twoCore_mem_localCComponents hmem
  have hD := source_larger_span_component_knownSimple hG K T X hK h3 hTK hAX hX S hS
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
    natural_source_full_span_quotient_quasisimple_knownSimple hG h hn hT hTK X hAX hX S hS hVC
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv eD
  obtain ⟨hb,m,hm,hmodel,hquot,hmodels⟩ := noncubic_twoCore_small_models_with_quotient
    K T X hK h3 hUT hT hTK hKX hX S hS hVC
  let : IsQuasisimple B := hb
  have hnat : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n) :=
    hn.2.2.choose_spec.choose_spec.choose_spec.2.1
  have he : n=m := (binary_two_valuation (lt_of_lt_of_le (by decide : 0<2) hn.1) hnat).symm.trans
    (binary_two_valuation (by omega : 0<m) hmodel)
  have hnat2 (hm2 : m=2) : IsL2EvenBlock K 2 := (he.trans hm2) ▸ hn
  have hsetup := source_larger_restricted_setup_knownSimple hG K T X hK h3 hTK hAX hX S hS hLK
  have hSQTK := source_larger_quotient_sqtk_knownSimple hG K T X hK h3 hTK hAX hX S hS
  rcases hmodels with hb | ⟨hm2,hb⟩
  · rcases binary_larger_selection_knownSimple hSQTK (pCore_quotient_pCore_eq_bot 2 (G := X))
      Q hBmem hE hBE hsetup.2.2.2 hm hb with hh | ⟨hm2,hmodels⟩
    · exact .inl hh
    · exact .inr ⟨hnat2 hm2,.inl (surviving_models_transport eD.symm hmodels)⟩
  · rcases sl2_five_larger_selection_knownSimple hSQTK (pCore_quotient_pCore_eq_bot 2 (G := X))
      Q hBmem hE hBE hsetup.2.2.2 hb with hh | ⟨p,hp,ho,u,hm⟩
    · exact .inl hh
    · refine .inr ⟨hnat2 hm2,.inr ⟨hb,p,hp,ho,u,?_⟩⟩
      cases u with
      | false =>
          rcases hm with hm | hm
          · exact .inl (hm.of_mulEquiv eD)
          · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
            exact .inr ⟨F,inferInstance,inferInstance,hF,⟨eD.trans e⟩⟩
      | true =>
          rcases hm with hm | hm
          · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
            exact .inl ⟨F,inferInstance,inferInstance,J,hF,hc,⟨eD.trans e⟩⟩
          · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
            exact .inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨eD.trans e⟩⟩

end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
