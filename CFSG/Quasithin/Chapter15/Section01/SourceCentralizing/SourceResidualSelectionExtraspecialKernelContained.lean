module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelSpan
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelCoreFullDisplacement
import all CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceThompson

/-!
# The characteristic elementary envelope when the full module lies in the core

The original action has quadratic ratio two. Its maximum-elementary offender
inequality therefore puts every contained copy of the original module in
the omega-center of the Thompson subgroup of the containing subgroup.
For Q=O₂(C_G(U)), that envelope is preserved by Mc. Consequently the actual
C_G(U)-span of V is elementary, and its Q-displacement lies in the actual
span of E. This does not identify E with that span.

The internal import reuses the original faithful-action offender transport
from the same package; its private helper does not enter the public types.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup containing the prepared module has it in its Thompson
omega-center, by the original non-FF action. -/
theorem PreparedChosenModule.le_omega_maxJ_of_le
    (T : Sylow 2 G) {M V Q : Subgroup G} (h : PreparedChosenModule T M V)
    (hVQ : V ≤ Q) (hQM : Q ≤ M) :
    V ≤ omegaOneCenterAmbient (elementaryAbelianMaxJ Q) := by
  let := h.elementary
  have hc : elementaryAbelianMaxJ Q ≤ centralizer (V : Set G) := by
    by_contra hn
    have hf := image_isFF_of_maxJ_not_centralizes M Q V hQM hVQ h.normalized hn
    have hh := (isFFModule_iff_quadraticRatio_le_one _).mp hf
    rw [h.quadratic_ratio] at hh
    norm_num at hh
  exact elementary_centralizer_maxJ_le_omegaCenter Q V hVQ (le_centralizer_iff.mp hc)

/-- In the contained branch the same full module lies in a characteristic
elementary envelope preserved by the original partner. -/
theorem PreparedChosenModule.extraspecial_contained_core_envelope
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hVQ : V ≤ (centralizer
      ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)).pCoreIn 2) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let Q := (centralizer (U : Set G)).pCoreIn 2
    let W := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
    V ≤ W ∧ W ≤ Q ∧ Mc ≤ normalizer (W : Set G) := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let Q := (centralizer (U : Set G)).pCoreIn 2
  let W := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  have hcore := h.extraspecial_moved_centralizer_twoCore
    hG T hempty hM hmany hJ hu hfull hex
  have hQM : Q ≤ M := hcore.2.1.trans hM.1.2
  have hWQ : W ≤ Q := by
    have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
    intro w hw
    exact hJQ (((mem_omegaOneCenterAmbient_iff _ w).mp hw).1)
  have hMcQ : Mc ≤ normalizer (Q : Set G) := by
    change Mc ≤ normalizer ((centralizer (U : Set G)).pCoreIn 2 : Set G)
    rw [hcore.1]
    exact Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  refine ⟨h.le_omega_maxJ_of_le T hVQ hQM,hWQ,?_⟩
  intro m hm
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : Q.map (MulAut.conj m).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hMcQ hm)
  change W.map (MulAut.conj m).toMonoidHom = W
  rw [show W = omegaOneCenterAmbient (elementaryAbelianMaxJ Q) from rfl,
    ←omegaOneCenterAmbient_map_injective _ (MulAut.conj m).injective,
    ←elementaryAbelianMaxJ_map_equiv (MulAut.conj m) Q,he]

/-- The actual full-module span is elementary in the contained branch;
its displacement is bounded by the actual fixed-subgroup span. -/
theorem PreparedChosenModule.extraspecial_contained_module_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := h.elementary; SourceCases.Extraspecial (imageRepresentation M V h.normalized)
      (((T : Subgroup G).subgroupOf M).map (actionHom M V h.normalized).rangeRestrict))
    (hVQ : V ≤ (centralizer
      ((⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆ : Subgroup G) : Set G)).pCoreIn 2) :
    let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
    let C := centralizer (U : Set G)
    let Q := C.pCoreIn 2
    let H := conjugateSpanBy V C
    let F := conjugateSpanBy (thompsonFixed T V) C
    IsElementaryAbelian 2 H ∧ H ≤ Q ∧ Mc ≤ normalizer (H : Set G) ∧
      F ≤ H ∧ ⁅Q,H⁆ ≤ F := by
  let U := ⁅V,ChapterB.thompsonJ (T : Subgroup G) 1⁆
  let C := centralizer (U : Set G)
  let Q := C.pCoreIn 2
  let H := conjugateSpanBy V C
  let F := conjugateSpanBy (thompsonFixed T V) C
  let W := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  have henv := h.extraspecial_contained_core_envelope
    hG T hempty hM hmany hJ hu hfull hex hVQ
  have hmod := h.extraspecial_partner_module_and_normalizer
    hG T hempty hM hmany hJ hu hfull hex
  have hmodU : localModule T Mc = U := hmod.1
  have hCMc : C ≤ Mc := by
    rw [hmod.2]
    exact Subgroup.centralizer_le_normalizer _
  have hHW : H ≤ W := conjugateSpanBy_le henv.1 (hCMc.trans henv.2.2)
  let : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian _
  have hMcC : Mc ≤ normalizer (C : Set G) := by
    rw [hmod.2]
    exact normalizer_le_normalizer_centralizer _
  have hIH : M ⊓ Mc ≤ normalizer (H : Set G) :=
    normalizes_conjugateSpanBy V C (M ⊓ Mc) (inf_le_left.trans h.normalized)
      (inf_le_right.trans hMcC)
  have htwo := h.maximal_overgroups_of_full_extraspecial
    hG T hempty hM hmany hJ hu hfull hex
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := by
    rw [htwo]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hNH : Mc ≤ normalizer (H : Set G) := by
    intro m hm
    obtain ⟨a,ha,c,hc,rfl⟩ :=
      source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc hMc m hm
    have hcC : c ∈ C := by
      change c ∈ centralizer (U : Set G)
      rw [←hmodU]
      exact hc.2
    exact (normalizer (H : Set G)).mul_mem (hIH ⟨ha.2,ha.1⟩)
      ((le_normalizer_conjugateSpanBy V C) hcC)
  refine ⟨IsElementaryAbelian.of_le hHW,hHW.trans henv.2.1,hNH,
    conjugateSpanBy_mono inf_le_left le_rfl,?_⟩
  have hCQ : C ≤ normalizer (Q : Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hVC : V ≤ C := hVQ.trans (pCoreIn_le 2 C)
  have hd : ⁅Q,V⁆ ≤ thompsonFixed T V :=
    h.extraspecial_moved_centralizer_full_displacement
      hG T hempty hM hmany hJ hu hfull hex
  change ⁅Q,conjugateSpanBy V C⁆ ≤ F
  rw [commutator_comm,commutator_conjugateSpanBy_of_normalized_right V C Q hVC hCQ]
  exact conjugateSpanBy_mono ((commutator_comm V Q).trans_le hd) le_rfl

end CFSG.Quasithin.Chapter15.Section01
