module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Temporary
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.Frattini

/-!
# Sylow and conjugate-span inheritance under replacement

Write `K = C_{G_E}(V_E/E)` and `H = N_{G_E}(C_T(V_E/E))`.
The intersection description of the quotient centralizer shows `T_E ≤ H`.
Its original Sylow subgroup therefore restricts to a Sylow subgroup of `H`.
Frattini gives `G_E = H K`; since `E ≤ V`, the kernel `K` normalizes `V`.
Consequently the original `V_E` is exactly the span of the `H`-conjugates of `V`.
The original constructions are retained throughout.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G : Type*} [Group G]

/-- The original line Sylow subgroup normalizes its intersection with the section kernel. -/
theorem lineT_le_temporary (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) : lineT T E ≤ temporaryLineNormalizer T V E := by
  have hK := (normal_subgroupOf_iff_le_normalizer (Descent.sectionKernel_le V E)).mp
    (Descent.sectionKernel_normal V E hEV)
  refine le_inf inf_le_right ?_
  rw [Descent.quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
  exact (le_inf (inf_le_left.trans T.le_normalizer) (inf_le_right.trans hK)).trans
    inf_normalizer_le_normalizer_inf

/-- The same ambient `T_E` is Sylow in the temporary normalizer. -/
theorem lineT_sylow_temporary [Finite G] (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    ∃ S : Sylow 2 (temporaryLineNormalizer T V E),
      (S : Subgroup (temporaryLineNormalizer T V E)).map
        (temporaryLineNormalizer T V E).subtype = lineT T E := by
  have hidx : ¬ 2 ∣ (lineT T E).relIndex (lineNormalizer E) := by
    rw [← hP]
    change ¬ 2 ∣ (((P : Subgroup (lineNormalizer E)).map
      (lineNormalizer E).subtype).comap (lineNormalizer E).subtype).index
    rw [comap_map_eq_self_of_injective (lineNormalizer E).subtype_injective]
    exact P.not_dvd_index
  have hidxH : ¬ 2 ∣ (lineT T E).relIndex (temporaryLineNormalizer T V E) := by
    intro hd
    apply hidx
    exact dvd_trans hd (dvd_of_mul_right_eq _ (relIndex_mul_relIndex _ _ _
      (lineT_le_temporary T V E hEV) inf_le_left))
  have hp : IsPGroup 2 (lineT T E) := hP ▸ P.isPGroup'.map (lineNormalizer E).subtype
  exact ⟨(hp.comap_subtype (K := temporaryLineNormalizer T V E)).toSylow hidxH,
    map_subgroupOf_eq_of_le (lineT_le_temporary T V E hEV)⟩

/-- The temporary core lies in the unchanged Sylow subgroup. -/
theorem temporaryCore_le_lineT [Finite G] (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    temporaryCore T V E ≤ lineT T E := by
  obtain ⟨S, hS⟩ := lineT_sylow_temporary T V E hEV P hP
  rw [← hS]
  exact map_mono (pCore_isPGroup.le_sylow_of_normal S)

/-- Trivial action modulo `E ≤ V` stabilizes the original `V`. -/
theorem sectionKernel_le_normalizer (V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) : Descent.sectionKernel V E ≤ normalizer (V : Set G) := by
  intro x hx
  have hc := ((Descent.mem_sectionKernel_iff V E (lineV_le_lineNormalizer V E hEV) x).mp hx).2
  have hc' := ((Descent.mem_sectionKernel_iff V E (lineV_le_lineNormalizer V E hEV) x⁻¹).mp
    ((Descent.sectionKernel V E).inv_mem hx)).2
  intro v
  constructor
  · intro hv
    have h := V.mul_mem (V.inv_mem (hEV (hc v (le_conjugateSpanBy V _ hv)))) hv
    convert h using 1
    group
    rfl
  · intro hv
    have h := V.mul_mem (V.inv_mem (hEV (hc' (x * v * x⁻¹)
      (le_conjugateSpanBy V _ hv)))) hv
    convert h using 1
    group
    rfl

/-- Frattini supplies the temporary normalizer as a supplement to the section kernel. -/
theorem temporary_sup_sectionKernel [Finite G] (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    temporaryLineNormalizer T V E ⊔ Descent.sectionKernel V E = lineNormalizer E := by
  let L := lineNormalizer E
  let K := (Descent.sectionKernel V E).subgroupOf L
  let : K.Normal := Descent.sectionKernel_normal V E hEV
  obtain ⟨S, hS⟩ := P.exists_sylow_map_eq_inf_of_normal K
  have hmap : ((S : Subgroup K).map K.subtype).map L.subtype =
      lineQuotientCentralizer T V E := by
    rw [hS, map_inf _ _ _ L.subtype_injective, hP,
      map_subgroupOf_eq_of_le (Descent.sectionKernel_le V E),
      Descent.quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
    rw [lineT, inf_assoc, inf_of_le_right (Descent.sectionKernel_le V E)]
  have hfr := congrArg (fun B : Subgroup L => B.map L.subtype) S.normalizer_sup_eq_top
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, L.range_subtype,
    map_subgroupOf_eq_of_le (Descent.sectionKernel_le V E)] at hfr
  apply le_antisymm (sup_le inf_le_left (Descent.sectionKernel_le V E))
  change L ≤ _
  rw [← hfr]
  apply sup_le_sup_right
  exact le_inf (map_subtype_le _) (hmap ▸
    ((S : Subgroup K).map K.subtype).le_normalizer_map L.subtype)

/-- The supplement is the literal setwise product in the original `G_E`. -/
theorem temporary_product_sectionKernel [Finite G] (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    (lineNormalizer E : Set G) = (temporaryLineNormalizer T V E : Set G) *
      (Descent.sectionKernel V E : Set G) := by
  have hn := (normal_subgroupOf_iff_le_normalizer (Descent.sectionKernel_le V E)).mp
    (Descent.sectionKernel_normal V E hEV)
  rw [← temporary_sup_sectionKernel T V E hEV P hP]
  exact coe_mul_of_left_le_normalizer_right _ _
    (show temporaryLineNormalizer T V E ≤ normalizer (Descent.sectionKernel V E : Set G)
      from inf_le_left.trans hn)

/-- The original line span is still generated by the conjugates inside `H`. -/
theorem lineV_eq_temporary_span [Finite G] (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) :
    lineV V E = conjugateSpanBy V (temporaryLineNormalizer T V E) := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨g, hg, v, hv, rfl⟩
    change g ∈ (lineNormalizer E : Set G) at hg
    rw [temporary_product_sectionKernel T V E hEV P hP] at hg
    obtain ⟨h, hh, k, hk, rfl⟩ := hg
    have hkv : k * v * k⁻¹ ∈ V :=
      (sectionKernel_le_normalizer V E hEV hk v).mp hv
    have hc := subset_closure (show h * (k * v * k⁻¹) * h⁻¹ ∈
      {x | ∃ a ∈ temporaryLineNormalizer T V E, ∃ b ∈ V, a * b * a⁻¹ = x}
      from ⟨h, hh, _, hkv, rfl⟩)
    change h * (k * v * k⁻¹) * h⁻¹ ∈ conjugateSpanBy V (temporaryLineNormalizer T V E) at hc
    simpa only [mul_inv_rev, mul_assoc, SetLike.mem_coe] using hc
  · exact conjugateSpanBy_mono le_rfl inf_le_left

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
