module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialKernelContained
public import Theory.GroupTheory.ElementaryThompsonNormalizerControl
import all CFSG.Quasithin.ChapterD.Section01.UniqueFactor.SourceThompson

/-!
# The actual partner span of a prepared module in its two-core

If the original prepared module lies in the partner's two-core, its span
under the partner's local-module centralizer lies in a characteristic
elementary envelope. Source ordering makes the span partner-invariant.
It lies in both original two-cores, strictly contains the original module,
and has a genuine FF action of the partner.

The core containment is retained here as a reusable local hypothesis.
The order-fifteen source supplies it separately from its literal action.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

/-- The original module in the partner core has a strictly larger elementary
common-core span, with a genuine FF action of the same partner. -/
theorem PreparedChosenModule.partner_core_span_ff
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hVQ : V ≤ Mc.pCoreIn 2) :
    let C := centralizer (localModule T Mc : Set G)
    let H := conjugateSpanBy V C
    ∃ (hn : Mc ≤ normalizer (H : Set G)) (he : IsElementaryAbelian 2 H),
      letI := he
      V < H ∧ H ≤ M.pCoreIn 2 ⊓ Mc.pCoreIn 2 ∧
        H ≤ centralizer (V : Set G) ∧
        ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (H : Set G) ∧
        IsFFModule (imageRepresentation Mc H hn) := by
  let Q := Mc.pCoreIn 2
  let C := centralizer (localModule T Mc : Set G)
  let H := conjugateSpanBy V C
  let W := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  have hMcC : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G) := ⟨hMcC.1,hTMc⟩
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow Mc (T.subtype hTMc)
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] at hh
  have hQM : Q ≤ M := hQT.trans hM.1.2
  have hMcQ : Mc ≤ normalizer (Q : Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hMcW : Mc ≤ normalizer (W : Set G) := by
    intro m hm
    apply mem_normalizer_iff_map_conj_eq.mpr
    have he : Q.map (MulAut.conj m).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hMcQ hm)
    change W.map (MulAut.conj m).toMonoidHom = W
    rw [show W = omegaOneCenterAmbient (elementaryAbelianMaxJ Q) from rfl,
      ←omegaOneCenterAmbient_map_injective _ (MulAut.conj m).injective,
      ←elementaryAbelianMaxJ_map_equiv (MulAut.conj m) Q,he]
  have hWQ : W ≤ Q := by
    have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA => hA.1
    intro w hw
    exact hJQ (((mem_omegaOneCenterAmbient_iff _ w).mp hw).1)
  have hCMc : C ≤ Mc := localModule_centralizer_le_partner T Mc hu
  have hHW : H ≤ W := conjugateSpanBy_le
    (h.le_omega_maxJ_of_le T hVQ hQM) (hCMc.trans hMcW)
  let : IsElementaryAbelian 2 W := omegaOneCenterAmbient_elementaryAbelian _
  let heH : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le hHW
  let := heH
  have hHQ : H ≤ Q := hHW.trans hWQ
  have hMcCn : Mc ≤ normalizer (C : Set G) :=
    (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc).trans
      (normalizer_le_normalizer_centralizer _)
  have hIH : M ⊓ Mc ≤ normalizer (H : Set G) :=
    normalizes_conjugateSpanBy V C (M ⊓ Mc) (inf_le_left.trans h.normalized)
      (inf_le_right.trans hMcCn)
  have hNH : Mc ≤ normalizer (H : Set G) := by
    intro m hm
    obtain ⟨a,ha,c,hc,rfl⟩ :=
      source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc hMc m hm
    exact (normalizer (H : Set G)).mul_mem (hIH ⟨ha.2,ha.1⟩)
      ((le_normalizer_conjugateSpanBy V C) hc.2)
  have hHV : H ≤ centralizer (V : Set G) :=
    H.le_centralizer.trans (centralizer_le (le_conjugateSpanBy V C))
  let K := M ⊓ centralizer (V : Set G)
  have hHK : H ≤ K := le_inf (hHQ.trans hQM) hHV
  have hKMc : K ≤ Mc := inf_le_right.trans (h.centralizer_le_partner T hu)
  have hHcore : H ≤ K.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 H) hHK (hKMc.trans hNH)
  have hMK : M ≤ normalizer (K : Set G) :=
    (le_inf M.le_normalizer (h.normalized.trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hHM : H ≤ M.pCoreIn 2 :=
    hHcore.trans (pCoreIn_mono_of_normalizes inf_le_left hMK)
  have hNM : normalizer (V : Set G) ≤ M := by
    let := h.elementary
    exact hM.1.1.2 ⟨V,h.nontrivial,IsElementaryAbelian.isPGroup 2 V,rfl⟩ h.normalized
  have hCHM : centralizer (H : Set G) ≤ M :=
    (centralizer_le (le_conjugateSpanBy V C)).trans
      ((Subgroup.centralizer_le_normalizer _).trans hNM)
  have hnot : ¬ Mc ≤ M := fun hh => hne (hMc.1.eq_of_le hM.1.1.1 hh).symm
  have hVH : V < H := lt_of_le_of_ne (le_conjugateSpanBy V C) (by
    intro he
    exact hnot (hNH.trans (he ▸ hNM)))
  have hJT : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (H : Set G) := by
    intro hj
    have hm : (((T.subtype hTMc : Sylow 2 Mc) : Subgroup Mc).map Mc.subtype) =
        (T : Subgroup G) := map_subgroupOf_eq_of_le hTMc
    apply hnot
    apply le_of_thompson_normalizer_centralizer_control Mc M H (T.subtype hTMc)
      hNH (inf_le_right.trans hCHM)
    · simpa only [hm] using hj
    · simpa only [hm] using (source_centralizing_baumann_control hG T hM hJ).2.2.2.2.2.1
  refine ⟨hNH,heH,hVH,le_inf hHM hHQ,hHV,hJT,?_⟩
  exact image_isFF_of_maxJ_not_centralizes Mc (T : Subgroup G) H hTMc
    (hHQ.trans hQT) hNH hJT

end CFSG.Quasithin.Chapter15.Section01
