module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsJankoFour
public import Theory.SpecificGroups.Janko4.Model.SylowOvergroups.PrimeTwentyThree

/-!
# The unconditional M₂₃ local-overcomponent application

The local subgroup already supplied by the exceptional J₄ analysis contains
both the marked section and the full Sylow subgroup. Its normal two-subgroup
and factor 23 place it directly inside a conjugate of the native max1 subgroup.
The genuine max1 two-core quotient is M₂₄, where the proved section exclusion
applies. No enlargement to an arbitrary maximal subgroup is needed.

The final theorem retains the original QTKE, local-family, normalization and
containment hypotheses. The stronger catalogue-free statement for arbitrary
maximal Sylow overgroups remains a separate intrinsic J₄ problem.

Source: Aschbacher–Smith A.3.12(17), printed pp.47–48, and 1.2.8, pp.506–507.
The quotient and local-component transports are adapted from the imported
conditional consumer, whose public interfaces are unchanged.
-/

public section
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup Janko4.Cardinality.localKernel
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The actual M₂₄ quotient of max1 rules out the normalized exceptional section. -/
private theorem not_max1_section
    (S : Sylow 2 (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (B : Subgroup (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four))
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup (Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)) ≤
        normalizer (B : Set (Janko4.Cardinality.max1Subgroup
          Janko4.matrixA_mul_self Janko4.matrixB_pow_four)))
    (h : Exceptional.IsModel (B ⧸ pCore 2 B)) : False := by
  let q := QuotientGroup.mk' (Janko4.Cardinality.localKernel
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk', Janko4.LocalStructure.localKernel_eq_twoCore]
    let := pCore_isNilpotent (p := 2) (G := Janko4.Cardinality.max1Subgroup
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)
    infer_instance
  obtain ⟨hb,hs,hm⟩ := Exceptional.local_section_map hB hn h q
  exact Exceptional.not_mathieu_twentyFour
    (S.mapSurjective (QuotientGroup.mk'_surjective _)) (B.map q) hb hs hm
    (Janko4.LocalStructure.localQuotientEquivM24
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four)

/-- Direct placement of the actual two-local excludes a local M₂₃ section in J₄.
No maximal Sylow-overgroup catalogue or ambient core assumption is needed. -/
theorem not_mathieuTwentyThree_in_jankoFour
    (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M23)) : False := by
  have hm : Exceptional.IsModel (B ⧸ pCore 2 B) := Or.inr (Or.inl h)
  obtain ⟨N,hN,hBN,hSN⟩ := Exceptional.jankoFour_exists_twoLocal S B hB hn hm
    (MulEquiv.refl _)
  have h23 : 23 ∣ Nat.card N := by
    have hc : Nat.card (B ⧸ pCore 2 B) = 10200960 :=
      (Nat.card_congr h.some.toEquiv).trans Sporadic.Mathieu.m23_order
    exact (by decide : 23 ∣ 10200960).trans ((hc ▸ card_quotient_dvd_card (pCore 2 B)).trans
      (card_dvd_of_le hBN))
  obtain ⟨g, hNg⟩ := Janko4.SylowOvergroups.twoLocal_le_conjugate_max1_of_twentyThree
    S N hN hSN h23
  let C := Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  let M := C.map (MulAut.conj g).toMonoidHom
  have hSM : (S : Subgroup Janko4.Model) ≤ M := hSN.trans hNg
  have hBM : B ≤ M := hBN.trans hNg
  let e : M ≃* C := ((MulAut.conj g).subgroupMap C).symm
  let P := S.subtype hSM
  have hl : B.subgroupOf M ∈ localCComponents P := local_restrict hB hBM
  have hnorm : (P : Subgroup M) ≤ normalizer (B.subgroupOf M : Set M) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : Janko4.Model)
  have hsmall : Exceptional.IsModel ((B.subgroupOf M) ⧸ pCore 2 (B.subgroupOf M)) :=
    hm.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBM)))
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  obtain ⟨hl',hn',hm'⟩ := Exceptional.local_section_map hl hnorm hsmall e.toMonoidHom
  exact not_max1_section (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    ((B.subgroupOf M).map e.toMonoidHom) hl' hn' hm'

end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents

namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The native two-local placement closes every proper M₂₃ embedding. -/
theorem eq_of_mathieuTwentyThree_containing
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hn : (T : Subgroup G) ≤ normalizer (B : Set G))
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* Sporadic.Mathieu.M23)) : B = K := by
  obtain ⟨S,_,hl,hs⟩ := exists_local_sylow_normalizing T hB hK.subnormal hBK hn
  have hsmall : Nonempty (((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) ≃*
      Sporadic.Mathieu.M23) :=
    ⟨(QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hBK))).trans h.some⟩
  rcases Exceptional.containing_models_of_core_eq_bot hG hO T hB hK hBK hn
    (Or.inr (Or.inl h)) with he | hJ | hM | hJ4
  · exact he
  · have hd : Nat.card (B ⧸ pCore 2 B) ∣ Nat.card K :=
      (card_quotient_dvd_card _).trans (card_dvd_of_le hBK)
    rw [Nat.card_congr h.some.toEquiv, Sporadic.Mathieu.m23_order,
      Nat.card_congr hJ.some.toEquiv,
      Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
    norm_num at hd
  · apply le_antisymm hBK
    apply subgroupOf_eq_top.mp
    apply (B.subgroupOf K).eq_top_of_card_eq
    apply le_antisymm (Nat.card_le_card_of_injective (B.subgroupOf K).subtype
      (B.subgroupOf K).subtype_injective)
    rw [Nat.card_congr hM.some.toEquiv, ← Nat.card_congr hsmall.some.toEquiv]
    exact Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 (B.subgroupOf K)))
      (QuotientGroup.mk'_surjective _)
  · obtain ⟨e⟩ := hJ4
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [e.toMonoidHom.ker_eq_bot e.injective]
      infer_instance
    have hl' := localCComponents_map_of_solvable_ker hl e.toMonoidHom
    have hs' := (map_mono hs).trans (le_normalizer_map e.toMonoidHom)
    let eB := QuotientGroup.congr _ _ (e.subgroupMap (B.subgroupOf K))
      (pCore_map_iso 2 (e.subgroupMap (B.subgroupOf K)))
    exact (not_mathieuTwentyThree_in_jankoFour
      (S.mapSurjective (f := e.toMonoidHom) e.surjective) ((B.subgroupOf K).map e.toMonoidHom)
      hl' hs' ⟨eB.symm.trans hsmall.some⟩).elim
end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents

namespace CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The M₂₃ local quotient survives enlargement to the original local overcomponent.
The J₄ branch is discharged by direct native two-local placement. -/
theorem mathieuTwentyThree_local_overcomponent
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {X K : Subgroup G}
    (hX : X ∈ L G (T : Subgroup G))
    (hn : (T : Subgroup G) ≤ normalizer (X : Set G))
    (hK : K ∈ L G (T : Subgroup G)) (hXK : X ≤ K)
    (h : Nonempty ((X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M23)) :
    Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M23) := by
  let H := K ⊔ (T : Subgroup G)
  have hXH : X ≤ H := hXK.trans le_sup_left
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  have hx : X.subgroupOf H ∈ L H (S : Subgroup H) :=
    (mem_LIn_iff_subgroupOf le_sup_right hXH).mp ⟨hXH,hX⟩
  have hn' : (S : Subgroup H) ≤ normalizer (X.subgroupOf H : Set H) := by
    intro s hs
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp (hn hs) (x : G)
  let q := QuotientGroup.mk' (pCore 2 H)
  let Sbar := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hbar : (X.subgroupOf H).map q ∈ localCComponents Sbar :=
    mem_L_map_twoCore_mem_localCComponents hx
  have hnorm : (Sbar : Subgroup (H ⧸ pCore 2 H)) ≤
      normalizer ((X.subgroupOf H).map q : Set _) :=
    (map_mono hn').trans (le_normalizer_map q)
  have hq := uniqueness_local_quotient_sqtk hG hK.2.2
  let eX := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hXH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hXH))
  have hkX : IsPGroup 2 (q.subgroupMap (X.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eB := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (X.subgroupOf H)) (q.subgroupMap_surjective _) hkX
  have hm : Nonempty ((((X.subgroupOf H).map q) ⧸ pCore 2 ((X.subgroupOf H).map q)) ≃*
      Sporadic.Mathieu.M23) := ⟨eB.symm.trans (eX.trans h.some)⟩
  let := pCore_isNilpotent (p := 2) (G := H)
  have he := eq_of_mathieuTwentyThree_containing
    hq (pCore_quotient_pCore_eq_bot 2) Sbar hbar (hK.1.map_quotient _)
    (map_mono (comap_mono hXK)) hnorm hm
  rw [he] at hm
  have hkK : IsPGroup 2 (q.subgroupMap (K.subgroupOf H)).ker := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eC := MonoidHom.quotientPCoreEquivOfSurjective
    (q.subgroupMap (K.subgroupOf H)) (q.subgroupMap_surjective _) hkK
  let eK := QuotientGroup.congr _ _ (subgroupOfEquivOfLe (show K ≤ H from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)))
  exact ⟨eK.symm.trans (eC.trans hm.some)⟩
end CFSG.Quasithin.Chapter1.Section02.ExceptionalOvercomponents
