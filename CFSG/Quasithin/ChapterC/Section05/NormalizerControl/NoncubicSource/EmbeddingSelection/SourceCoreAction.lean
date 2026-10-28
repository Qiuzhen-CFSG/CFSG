module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.SourceParameters
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Kernel

/-!
# The original full Sylow action on the two-core quotient

The map KT → N/O₂(N) has kernel exactly O₂(KT): reducedness of the
original omega-center span gives one containment, and normality of P₁ in
N gives the other. This retains the binary block model, quasisimplicity,
local-component membership and the full faithful Sylow action in the
precise quotient on which A.3.12 is available.
Source: Aschbacher–Smith C.5.13, printed pp.162–163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

theorem source_twoCore_sylow_action (K T X : Subgroup G)
    (hK : IsChiZeroBlock K) (h3 : ¬ IsAlternatingBlock K 3)
    (hT : IsPGroup 2 T) (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hA : K ⊔ T ∈ Chapter1.He G) (hAX : K ⊔ T ≤ X) (hX : X ∈ Chapter1.He G)
    (S : Sylow 2 X) (hS : (S : Subgroup X).map X.subtype = T) :
    let N := X ⊓ normalizer ((K ⊔ T).pCoreIn 2 : Set G)
    let r := QuotientGroup.mk' (pCore 2 N)
    let B := (K.subgroupOf N).map r
    ∃ Q : Sylow 2 (N ⧸ pCore 2 N), (Q : Subgroup _) = (T.subgroupOf N).map r ∧
      B ∈ ChapterA.Section03.localCComponents Q ∧ IsQuasisimple B ∧
      (Q : Subgroup (N ⧸ pCore 2 N)) ≤ normalizer (B : Set (N ⧸ pCore 2 N)) ∧
      (Q : Subgroup (N ⧸ pCore 2 N)) ⊓ centralizer (B : Set (N ⧸ pCore 2 N)) = ⊥ ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* B) ∧
      ∃ n, 1 < n ∧ ClassicalGroup.IsPSL B 2 (2^n) := by
  let A := K ⊔ T
  let N := X ⊓ normalizer (A.pCoreIn 2 : Set G)
  let V := conjugateSpanBy (omegaOneCenterAmbient T) N
  let r := QuotientGroup.mk' (pCore 2 N)
  have hs := noncubic_source_span K T X hK h3 hT hUT hTK P hP hA hAX S hS
  let : (V.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hs.2.1).mpr hs.2.2.1
  have hred := hs.2.2.2.2.2.2.1
  have hAN : A ≤ N := le_inf hAX (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
  have hKN : K ≤ N := le_sup_left.trans hAN
  have hTN : T ≤ N := le_sup_right.trans hAN
  have hlocal := noncubic_auxiliary_local_family K T X hK h3 hTK hAX hX S hS
  obtain ⟨Q,hQ⟩ := hlocal.2.2
  have hTQ : T.subgroupOf N = (Q : Subgroup N) := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hTN,hQ]
  have hmem : K.subgroupOf N ∈ Chapter1.L N (Q : Subgroup N) := by
    rw [← hTQ]
    exact (Chapter1.mem_LIn_iff_subgroupOf hTN hKN).mp hlocal.1
  let Qbar := Q.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 N))
  have hQbar : (Qbar : Subgroup _) = (T.subgroupOf N).map r := by
    change (Q : Subgroup N).map r = (T.subgroupOf N).map r
    rw [hTQ]
  have hBmem : (K.subgroupOf N).map r ∈ ChapterA.Section03.localCComponents Qbar := by
    let := pCore_isNilpotent (p := 2) (G := N)
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hmem
  let f := r.comp (inclusion hAN)
  have hker : f.ker = pCore 2 A := by
    ext a
    constructor
    · intro ha
      have hc : inclusion hAN a ∈ pCore 2 N := (QuotientGroup.eq_one_iff _).mp ha
      have hv := le_centralizer_iff.mp hred.le_centralizer_pCore hc
      have hu : (a : G) ∈ centralizer (U K : Set G) := by
        intro u hu
        exact congrArg N.subtype (hv ⟨u,hs.2.1 (hs.2.2.2.1 hu)⟩ (hs.2.2.2.1 hu))
      have hp : (a : G) ∈ A.pCoreIn 2 :=
        (CounterexampleCharacteristic.ReducedMarking.normal_short_extension_centralizer
          K T hK.chi.short hT hTK) ▸ ⟨a.property,hu⟩
      obtain ⟨b,hb,he⟩ := hp
      exact (Subtype.ext he : b=a) ▸ hb
    · intro ha
      apply (QuotientGroup.eq_one_iff _).mpr
      have hcore : A.pCoreIn 2 ≤ N.pCoreIn 2 :=
        le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A) ((pCoreIn_le 2 A).trans hAN) inf_le_right
      obtain ⟨b,hb,he⟩ := hcore (mem_map_of_mem A.subtype ha)
      exact (Subtype.ext he : b=inclusion hAN a) ▸ hb
  let K₀ := K.subgroupOf A
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hTK)
  have hcomp : K₀.IsCComponent := (noncubic_mem_local_family K T hK h3 hTK P hP).1
  let e := (subgroupOfEquivOfLe (show K ≤ A from le_sup_left)).symm
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (K ⧸ pCore 2 K) := noncubic_quotient_quasisimple hK h3
  let : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv eq
  have hgen : K₀ ⊔ T.subgroupOf A = ⊤ := by
    change K.subgroupOf A ⊔ T.subgroupOf A = ⊤
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hm (D : Subgroup G) (hDA : D ≤ A) :
      (D.subgroupOf A).map f = (D.subgroupOf N).map r := by
    rw [← Subgroup.map_map]
    congr 1
    apply map_injective N.subtype_injective
    rw [Subgroup.map_map,map_subgroupOf_eq_of_le (hDA.trans hAN)]
    exact map_subgroupOf_eq_of_le hDA
  have hk : (f.subgroupMap K₀).ker = pCore 2 K₀ := by
    rw [ker_subgroupMap,hker]
    exact (pCore_subnormal_eq_comap 2 hcomp.subnormal).symm
  let ec := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (f.subgroupMap_surjective K₀))
  let et := (eq.trans ec).trans (MulEquiv.subgroupCongr (hm K le_sup_left))
  have hfaith := noncubic_image_faithful K₀ (T.subgroupOf A) hcomp inferInstance hT.comap_subtype hgen f hker
  change (T.subgroupOf A).map f ⊓ centralizer ((K.subgroupOf A).map f : Set _) = ⊥ at hfaith
  rw [hm T le_sup_right,hm K le_sup_left] at hfaith
  refine ⟨Qbar,hQbar,hBmem,IsQuasisimple.of_mulEquiv et,?_,?_,⟨et⟩,?_⟩
  · rw [hQbar]
    apply (map_mono (f := r) ?_).trans (le_normalizer_map _)
    rw [← subgroupOf_normalizer_eq hKN]
    exact subgroupOf_mono N hTK
  · rwa [hQbar]
  · obtain ⟨n,hn,hnm⟩ := noncubic_binary_model K hK h3
    exact ⟨n,hn,hnm.of_mulEquiv et.symm⟩
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl.EmbeddingSelection
