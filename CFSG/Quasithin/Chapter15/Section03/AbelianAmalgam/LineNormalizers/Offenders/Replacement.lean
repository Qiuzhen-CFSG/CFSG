module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Core
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Thompson
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Marked
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.Replacement.Transvections.Action

/-!
# The temporary line normalizer: core and Thompson transfers

The temporary normalizer retains `T_E`, its Sylow and maximum-elementary data,
and the original conjugate span `V_E`. The earlier local action facts identify
its own two-core with `C_T(V_E/E)`. The elementary Thompson subgroup of its
centralizer has the same section-action image as the original `I₀`; its image
modulo the temporary core is nontrivial. These facts supply the actual maximum
elementary subgroup used in the displayed offender inequalities.

The rank-kernel containment below is intrinsic to the temporary group and only
concerns `C_A(V_E)`. It requires no containment of the full centralizer in a
core. The core equality discharges the temporary premise of offender selection.

The inherited marked quotient and its paired linear projection are assembled
here from the original local package. The common-center transvection identity
is supplied by the separate `Replacement.Transvections` interface; this module
does not assert the terminal S₃ or index-three conclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Transvections
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement.Geometry.OriginalData
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
variable {G : Type*} [Group G] [Finite G]

/-! The original local package is now placed in the literal temporary group.
The adapters below keep the source subgroup `lineQ E` distinct from the
temporary core and retain the intrinsic centralizers in `H`. -/

noncomputable def temporaryData_of_original
    {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
    (d : OriginalData Y T V M E Pc) : TemporaryData Y T V E where
  line_le := d.line_le
  span_le_sylow := d.span_le_sylow
  sylow := d.sylow
  sylow_eq := d.sylow_image
  residual_normalized := d.residual_normal
  original_core_section := d.core_le_kernel
  residual_section_core := residual_section_kernel_le_core d
  local_core := d.local_core
  local_commutator := d.seed_commutator
  residual_core_centralizes := by
    have hVline : V ≤ lineV V E := le_conjugateSpanBy V (lineNormalizer E)
    exact d.residual_core_centralizes_span.trans (centralizer_le hVline)
  seed_normalized := d.sylow_le_M.trans d.action.normalizes
  seed_elementary := d.sylow_action_elementary
  tau := d.tau
  tau_mem := d.marked.tau_mem
  conjugator := d.residualElement (d.markedResidual : G)⁻¹ (by
    exact (lineY Y E).inv_mem d.markedResidual.property)
  conjugator_mem := by exact (lineY Y E).inv_mem d.markedResidual.property
  centralizer_tau_mod := by
    let _ : ((temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E)).Normal :=
      temporaryCore_normal T V E
    intro c hc
    let F := d.markedQuotientFactors
    change c ∈ temporaryLineNormalizer T V E ∧ c ∈ centralizer (E : Set G) at hc
    let cH : temporaryLineNormalizer T V E := ⟨c, hc.1⟩
    have hcF : cH ∈ (temporaryCentralizer T V E).subgroupOf
        (temporaryLineNormalizer T V E) := ⟨cH.property, hc.2⟩
    have hh := F.quotient_commute cH d.tau hcF
      (mem_sup_right (mem_zpowers d.marked.tau))
    have hqH : ⁅cH, d.tau⁆ ∈
        (temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E) :=
      (QuotientGroup.eq_one_iff _).mp (commutatorElement_eq_one_iff_commute.mpr hh)
    have he : ⁅(c : G), d.marked.tau⁆ ∈ temporaryCore T V E := by
      change ((⁅cH, d.tau⁆ : temporaryLineNormalizer T V E) : G) ∈ temporaryCore T V E
      exact hqH
    exact he
  centralizer_span := d.inherited.2.2.2

/-- The actual marked fixed-space geometry in the faithful action on `V_E`.
The second summand is obtained from the inverse of the selected residual
element, while the complementary-space theorem is applied to that residual
element itself, preserving the source right-conjugation convention. -/
noncomputable def fixedGeometry_of_original
    {Y T V M E Pc : Subgroup G} {D : Type*} [Group D] [IsMulCommutative V]
    (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) :
        Set (temporaryLineNormalizer T V E))) :
    letI := d.module_normal
    letI := d.module_elementary
    letI := d.line_normal
    FixedGeometry (localRepresentation T V E f hf hker) (f d.tau)
      (f (d.residualElement ((d.markedResidual : G)⁻¹) (by
        exact (lineY Y E).inv_mem d.markedResidual.property)))
      (localLineSpace T V E) := by
  letI := d.module_normal
  letI := d.module_elementary
  letI := d.line_normal
  let H := temporaryLineNormalizer T V E
  let U := (lineV V E).subgroupOf H
  let ρ := localRepresentation T V E f hf hker
  let r : lineY Y E := d.markedResidual
  have hyr : (r : G) ∈ lineY Y E := r.property
  have hyinv : (r : G)⁻¹ ∈ lineY Y E := (lineY Y E).inv_mem hyr
  let c : H := d.residualElement ((r : G)⁻¹) hyinv
  have hc : c = (d.residualElement (r : G) hyr)⁻¹ := by
    apply Subtype.ext
    rfl
  have hop := d.markedOperatorRelations f hf hker (r : G) hyr d.markedResidual_image_ne_one
  have hfirst (t : H) :
      firstSpace ρ (f t) =
        Representation.NormalElementaryQuotient.subspace U
          ((centralizer ({t} : Set H)).subgroupOf U) := by
    change (ρ (f t) - LinearMap.id).ker = _
    exact (MarkedSection.rawFixed_eq_ker U f hf hker t).symm
  have hmap :
      (firstSpace ρ (f d.tau)).map (ρ (f c)) =
        Representation.NormalElementaryQuotient.subspace U
          ((centralizer ({c * d.tau * c⁻¹} : Set H)).subgroupOf U) := by
    have hm := firstSpace_map ρ (f d.tau) (f c)
    have hfc : f c * f d.tau * (f c)⁻¹ = f (c * d.tau * c⁻¹) := by
      rw [map_mul, map_mul, map_inv]
    rw [hfc, hfirst (c * d.tau * c⁻¹)] at hm
    exact hm
  let hzdata := d.exists_denominator_fixed_generator
  let z := Classical.choose hzdata
  have hz : z ≠ 0 := (Classical.choose_spec hzdata).1
  have hcenter := (Classical.choose_spec hzdata).2
  refine { spans := ?_, disjoint := ?_, center := z, center_ne := hz, center_eq := ?_ }
  · change firstSpace ρ (f d.tau) ⊔
      (firstSpace ρ (f d.tau)).map (ρ (f c)) = ⊤
    rw [hmap, hfirst d.tau]
    simpa [hc] using
      (MarkedSection.rawFixed_isCompl U f hf hker d.tau
        (d.residualElement (r : G) hyr) hop).sup_eq_top
  · change Disjoint (firstSpace ρ (f d.tau))
      ((firstSpace ρ (f d.tau)).map (ρ (f c)))
    rw [hmap, hfirst d.tau]
    simpa [hc] using
      (MarkedSection.rawFixed_isCompl U f hf hker d.tau
        (d.residualElement (r : G) hyr) hop).disjoint
  · rw [hfirst d.tau]
    exact hcenter

/-! The marked quotient itself, with its exact `E` kernel and diagonal
centralizer action, is the interface consumed by the offender inequalities. -/
noncomputable def pairedSection_of_original
    {Y T V M E Pc : Subgroup G} {D : Type*} [Group D] [IsMulCommutative V]
    (d : OriginalData Y T V M E Pc)
    (f : temporaryLineNormalizer T V E →* D) (hf : Function.Surjective f)
    (hker : f.ker = centralizer
      ((lineV V E).subgroupOf (temporaryLineNormalizer T V E) :
        Set (temporaryLineNormalizer T V E))) :
    letI := d.module_normal
    letI := d.module_elementary
    letI := d.line_normal
    letI := temporaryCore_normal T V E
    PairedSection (Transvections.localSpan T V E) (Transvections.localLine T V E)
      ((temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E))
      (Transvections.localCore T V E) f hf hker (d.pairedRepresentation f hf hker) := by
  letI := d.module_normal
  letI := d.module_elementary
  letI := d.line_normal
  let _ : (localCore T V E).Normal := temporaryCore_normal T V E
  exact d.pairedSection f hf hker

omit [Finite G] in
/-- The actual centralizer factor is normal in the temporary line normalizer. -/
theorem temporaryCentralizer_normal_of_original
    (T V E : Subgroup G) [IsMulCommutative V] :
    ((temporaryCentralizer T V E).subgroupOf (temporaryLineNormalizer T V E)).Normal := by
  have hNC : lineNormalizer E ≤ normalizer (centralizer (E : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (E : Set G))).mp inferInstance
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
  exact (le_inf (temporaryLineNormalizer T V E).le_normalizer
    (inf_le_left.trans hNC)).trans inf_normalizer_le_normalizer_inf

/-- The unchanged Sylow witnesses in the temporary normalizer and its
centralizer, with the source subgroups retained literally. -/
theorem temporary_sylow_witnesses_of_original
    {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
    (d : OriginalData Y T V M E Pc) :
    (∃ S : Sylow 2 (temporaryLineNormalizer T V E),
      (S : Subgroup (temporaryLineNormalizer T V E)).map
        (temporaryLineNormalizer T V E).subtype = lineT T E) ∧
    (∃ S : Sylow 2 (temporaryCentralizer T V E),
      (S : Subgroup (temporaryCentralizer T V E)).map
        (temporaryCentralizer T V E).subtype =
          lineT T E ⊓ centralizer (E : Set G)) := by
  exact ⟨lineT_sylow_temporary T V E d.line_le d.sylow d.sylow_image,
    temporaryCentralizer_sylow T V E d.line_le d.sylow d.sylow_image⟩

/-- The source-local structure supplies an actual offender candidate in `H`.
In particular the core-kernel premise of the intermediate selection theorem
has been proved, rather than added to this theorem's assumptions. -/
theorem exists_temporary_max_of_local_structure (M Y T V E : Subgroup G)
    [IsMulCommutative V] (hEV : E ≤ V) (hVT : V ≤ lineT T E)
    (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hY : lineNormalizer E ≤ normalizer (lineY Y E : Set G))
    (hQK : lineQ E ≤ Descent.sectionKernel V E)
    (hYK : lineY Y E ⊓ Descent.sectionKernel V E ≤ lineQ E)
    (hlocal : (lineY Y E ⊔ lineT T E).pCoreIn 2 ≤ T ⊓ centralizer (E : Set G))
    (hcomm : ⁅V, T ⊓ centralizer (E : Set G)⁆ ≤ E)
    (hNM : normalizer (V : Set G) ≤ M) (hI : ¬ lineI E ≤ lineM M E)
    (hJC : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G)) :
    let H := temporaryLineNormalizer T V E
    let Q := (temporaryCore T V E).subgroupOf H
    letI : Q.Normal := temporaryCore_normal T V E
    ∃ (S : Sylow 2 H), (S : Subgroup H).map H.subtype = lineT T E ∧
      ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
        A ≤ (temporaryCentralizer T V E).subgroupOf H ∧
        A.map (QuotientGroup.mk' Q) ≠ ⊥ := by
  have hcore : temporaryCore T V E ≤ Descent.sectionKernel V E := by
    rw [temporaryCore_eq_quotientCentralizer Y T V E hEV hVT P hP hY hQK hYK hlocal hcomm,
      Descent.quotientCentralizer_eq_inf T V E (lineV_le_lineNormalizer V E hEV)]
    exact inf_le_right
  exact exists_temporary_max_nontrivial_image M T V E hEV P hP hNM hI hcore hJC

omit [Finite G] in
/-- The precise centralizer containment needed by `displayed_rank_inequalities`,
with all subgroups formed inside the actual temporary normalizer. -/
theorem rank_kernel_le_temporaryCore (T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (hUT : lineV V E ≤ lineT T E)
    (P : Sylow 2 (lineNormalizer E))
    (hP : (P : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (A : Subgroup (temporaryLineNormalizer T V E))
    (hA : A ≤ (lineT T E).subgroupOf (temporaryLineNormalizer T V E)) :
    A ⊓ centralizer (((lineV V E).subgroupOf (temporaryLineNormalizer T V E)) :
      Set (temporaryLineNormalizer T V E)) ≤
        (temporaryCore T V E).subgroupOf (temporaryLineNormalizer T V E) := by
  let H := temporaryLineNormalizer T V E
  have hUH : lineV V E ≤ H := hUT.trans (lineT_le_temporary T V E hEV)
  have hp : IsPGroup 2 (lineT T E) := hP ▸ P.isPGroup'.map (lineNormalizer E).subtype
  have hRQ : lineQuotientCentralizer T V E ≤ temporaryCore T V E :=
    le_pCoreIn_of_normalizes (hp.to_le (lineQuotientCentralizer_le_lineT T V E))
      (quotientCentralizer_le_temporary T V E) inf_le_right
  intro x hx
  apply hRQ
  apply (mem_lineQuotientCentralizer_iff T V E (lineV_le_lineNormalizer V E hEV) (x : G)).mpr
  refine ⟨hA hx.1, fun v hv => ?_⟩
  have hc := hx.2 (⟨v, hUH hv⟩ : H) hv
  have he : v * (x : G) = (x : G) * v := congrArg Subtype.val hc
  rw [commutatorElement_eq_one_iff_mul_comm.mpr he]
  exact E.one_mem

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.Replacement
