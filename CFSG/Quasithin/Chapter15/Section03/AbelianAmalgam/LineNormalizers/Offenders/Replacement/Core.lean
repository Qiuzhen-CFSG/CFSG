module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Inheritance

/-!
# Recovering the temporary two-core

The original core and the temporary core are distinct constructions. The original
section-kernel bounds imply that `Y_E` normalizes `C_T(V_E/E)`, so `Y_E T_E ≤ H`.
The temporary core lies in `T_E` and is normal in `Y_E T_E`; it therefore lies in
that group's two-core `S_E`. The preceding local relation `[V,S_E] ≤ E` propagates
across the `H`-conjugates of `V`, proving the reverse core containment.

The inputs concern the original action: `Q_E ≤ K`, `Y_E ∩ K ≤ Q_E`, the local
core of `Y_E T_E`, and its commutators with `V`. They are retained explicitly;
no equality between the original and temporary cores is assumed or concluded.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170, using the preceding 15.3.66 local structure.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G : Type*} [Group G]
open scoped commutatorElement

/-- The original core centralizes the larger section whenever it lies in its kernel. -/
theorem lineQ_le_quotientCentralizer (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hQK : lineQ E ≤ Descent.sectionKernel V E) :
    lineQ E ≤ lineQuotientCentralizer T V E := by
  rw [Descent.quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
  refine le_inf ?_ hQK
  have hQT : lineQ E ≤ lineT T E := by
    rw [← hP]
    exact map_mono (pCore_isPGroup.le_sylow_of_normal P)
  exact hQT.trans inf_le_left

/-- The marked residual normalizes the quotient centralizer. The two kernel hypotheses
refer to the original action and original core, before replacement. -/
theorem lineY_le_temporary (Y T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hY : lineNormalizer E ≤ normalizer (lineY Y E : Set G))
    (hQK : lineQ E ≤ Descent.sectionKernel V E)
    (hYK : lineY Y E ⊓ Descent.sectionKernel V E ≤ lineQ E) :
    lineY Y E ≤ temporaryLineNormalizer T V E := by
  have hKG := (normal_subgroupOf_iff_le_normalizer (Descent.sectionKernel_le V E)).mp
    (Descent.sectionKernel_normal V E hEV)
  have hRK : lineQuotientCentralizer T V E ≤ Descent.sectionKernel V E := by
    rw [Descent.quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
    exact inf_le_right
  have hRY : ⁅lineY Y E, lineQuotientCentralizer T V E⁆ ≤ lineY Y E :=
    le_normalizer_iff_commutator_le_left.mp
      (((lineQuotientCentralizer_le_lineT T V E).trans inf_le_right).trans hY)
  have hRK' : ⁅lineY Y E, lineQuotientCentralizer T V E⁆ ≤ Descent.sectionKernel V E :=
    (commutator_mono le_rfl hRK).trans (le_normalizer_iff_commutator_le_right.mp
      (((lineY_le Y E).trans inf_le_right).trans hKG))
  exact le_inf ((lineY_le Y E).trans inf_le_right)
    (le_normalizer_iff_commutator_le_right.mpr
      ((le_inf hRY hRK').trans (hYK.trans (lineQ_le_quotientCentralizer T V E hEV P hP hQK))))

private theorem commutator_span_le (H A V E : Subgroup G) (hAH : A ≤ H)
    (hVH : V ≤ H) (hEH : E ≤ H) (hHA : H ≤ normalizer (A : Set G))
    (hHE : H ≤ normalizer (E : Set G)) (hVA : ⁅V, A⁆ ≤ E) :
    ⁅conjugateSpanBy V H, A⁆ ≤ E := by
  let N := E.subgroupOf H
  let D := A.subgroupOf H
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hEH).mpr hHE
  let : D.Normal := (normal_subgroupOf_iff_le_normalizer hAH).mpr hHA
  let q := QuotientGroup.mk' N
  let : (D.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective N)
  let C := centralizerModulo (⊤ : Subgroup H) D N
  let : C.Normal := by dsimp only [C, centralizerModulo]; infer_instance
  have hVC : V ≤ C.map H.subtype := by
    intro v hv
    refine mem_map.mpr ⟨⟨v, hVH hv⟩, ?_, rfl⟩
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_top _, fun a ha => ?_⟩
    change ⁅(a : G), v⁆ ∈ E
    rw [← commutatorElement_inv]
    exact E.inv_mem (hVA (commutator_mem_commutator hv ha))
  have hHC : H ≤ normalizer (C.map H.subtype : Set G) := by
    have h := C.le_normalizer_map H.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype] at h
  have hspan := conjugateSpanBy_le hVC hHC
  apply commutator_le.mpr
  intro v hv a ha
  obtain ⟨vH, hvC, rfl⟩ := hspan hv
  have hc := (mem_centralizerModulo_iff.mp hvC).2 ⟨a, hAH ha⟩ ha
  change ⁅a, (vH : G)⁆ ∈ E at hc
  rw [← commutatorElement_inv]
  exact E.inv_mem hc

/-- The reverse containment uses the core of `Y_E T_E` and `[V,S_E]≤E`,
then extends the latter relation over the full temporary conjugate span. -/
theorem temporaryCore_eq_quotientCentralizer [Finite G] (Y T V E : Subgroup G)
    [IsMulCommutative V] (hEV : E ≤ V) (hVT : V ≤ lineT T E)
    (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hY : lineNormalizer E ≤ normalizer (lineY Y E : Set G))
    (hQK : lineQ E ≤ Descent.sectionKernel V E)
    (hYK : lineY Y E ⊓ Descent.sectionKernel V E ≤ lineQ E)
    (hlocal : (lineY Y E ⊔ lineT T E).pCoreIn 2 ≤ T ⊓ centralizer (E : Set G))
    (hcomm : ⁅V, T ⊓ centralizer (E : Set G)⁆ ≤ E) :
    temporaryCore T V E = lineQuotientCentralizer T V E := by
  let H := temporaryLineNormalizer T V E
  let Q := temporaryCore T V E
  have hTH : lineT T E ≤ H := lineT_le_temporary T V E hEV
  have hYH : lineY Y E ≤ H := lineY_le_temporary Y T V E hEV P hP hY hQK hYK
  have hQT : Q ≤ lineT T E := temporaryCore_le_lineT T V E hEV P hP
  have hHQ : H ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (temporaryCore_le T V E)).mp (temporaryCore_normal T V E)
  have hQS : Q ≤ T ⊓ centralizer (E : Set G) :=
    (le_pCoreIn_of_normalizes (temporaryCore_isPGroup T V E)
      (hQT.trans le_sup_right) ((sup_le hYH hTH).trans hHQ)).trans hlocal
  have hUQ : ⁅lineV V E, Q⁆ ≤ E := by
    rw [lineV_eq_temporary_span T V E hEV P hP]
    exact commutator_span_le H Q V E (temporaryCore_le T V E)
      (hVT.trans hTH) (hEV.trans (hVT.trans hTH)) hHQ inf_le_left
      ((commutator_mono le_rfl hQS).trans hcomm)
  apply le_antisymm
  · intro q hq
    exact (mem_lineQuotientCentralizer_iff T V E (lineV_le_lineNormalizer V E hEV) q).mpr
      ⟨hQT hq, fun u hu => hUQ (commutator_mem_commutator hu hq)⟩
  · have hp : IsPGroup 2 (lineT T E) := hP ▸ P.isPGroup'.map (lineNormalizer E).subtype
    exact le_pCoreIn_of_normalizes (hp.to_le (lineQuotientCentralizer_le_lineT T V E))
      (quotientCentralizer_le_temporary T V E) inf_le_right

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
