module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.Normalizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.BinaryLinearThree

/-!
# Exclusion of the original natural binary SL3 block

The exchanged two-residual fixes the core quotient and hence the full block
cover by the binary natural-module automorphism calculation. Conjugating
back makes U(L)ᵗ centralize Y₀. The literal source centralizer identity then
makes it centralize L. The external cubic supplies S-normalization of L;
therefore L and T normalize the nontrivial two-subgroup U(L)U(L)ᵗ.
Original 14.1.6(3) puts L in Mc, contradicting its selection.

Both exchanged plane rows remain in the quotient-action dichotomy. No
three-rank-two assertion is made about SL3(2), and no residual recognition
or commuting-layer callback remains.
Source: Aschbacher--Smith 15.1.24(2), printed p.1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal exchanged residual centralizes the full block cover. -/
theorem ExchangedSource.linearThree_exchanged_centralizes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.linearThreeY.map (MulAut.conj t).toMonoidHom ≤ centralizer (d.L : Set G) :=
  a.block.centralizes_of_coreQuotient
    (s.linearThree_exchanged_action (h := h) sp hTM a ht htS).1
    (s.linearThree_exchanged_normalizes (h := h) sp hG hTM a ht htS)
    (s.linearThree_exchanged_core_quotient (h := h) sp hG hTM a ht htS)

/-- Conjugating the actual residual control back to the other block makes
the two layer factors commute with the opposite block. -/
theorem ExchangedSource.linearThree_conjugate_layer_centralizes
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hTM : (T : Subgroup G) ≤ M) (a : d.ConstrainedL3Alternative)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S) :
    d.linearThreeU.map (MulAut.conj t).toMonoidHom ≤ centralizer (d.L : Set G) := by
  have htinv : t⁻¹ ∈ (T : Subgroup G) := (T : Subgroup G).inv_mem ht
  have htinvS : t⁻¹ ∉ d.S := fun hi => htS (inv_mem_iff.mp hi)
  have hA := s.linearThree_exchanged_centralizes (h := h) sp hG hTM a htinv htinvS
  have hUS : d.linearThreeU ≤ d.S := by
    obtain ⟨P,hP⟩ := s.component_sylow
    exact ((map_mono blockU_le_core).trans (hP ▸ pCoreIn_le_sylow d.L P)).trans d.SL_le_S
  have hS : d.S.map (MulAut.conj t).toMonoidHom = d.S := by
    let := s.sylow_normal
    exact mem_normalizer_iff_map_conj_eq.mp ((le_normalizer_of_normal_subgroupOf d.S_le_T) ht)
  have hUtS : d.linearThreeU.map (MulAut.conj t).toMonoidHom ≤ d.S :=
    (map_mono hUS).trans hS.le
  have hUtY : d.linearThreeU.map (MulAut.conj t).toMonoidHom ≤
      centralizer (d.linearThreeY : Set G) := by
    rintro _ ⟨u,hu,rfl⟩ y hy
    have hh := hA (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom hy) u ((map_subtype_le _) hu)
    have he := congrArg (MulAut.conj t) hh
    change t * (u * (t⁻¹ * y * (t⁻¹)⁻¹)) * t⁻¹ =
      t * ((t⁻¹ * y * (t⁻¹)⁻¹) * u) * t⁻¹ at he
    change y * (t * u * t⁻¹) = (t * u * t⁻¹) * y
    group at he ⊢
    exact he.symm
  have hR : (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤
      d.linearThreeY := map_mono primeToResidual_three_le_twoResidual
  exact ((le_inf hUtS (hUtY.trans (centralizer_le hR))).trans a.centralizers.le).trans inf_le_right

/-- Original 15.1.24(2), with the actual original residual and exchanged
planes. Both plane rows are retained through the quotient-action dichotomy. -/
theorem ExchangedSource.no_constrained_l3
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    {h : PreparedChosenModule T M V} (sp : d.PreExclusionSource h.normalized 3)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    ¬ d.ConstrainedL3Alternative := by
  intro a
  obtain ⟨t,ht,htS⟩ := s.exchange_exists
  exact s.false_of_constrained_l3_commuting_layers hG hempty hu a
    (s.fixes_planes.1.trans (s.linearThree_normalizer_control (h := h) sp hG hTM a)) ht htS
    (s.linearThree_conjugate_layer_centralizes (h := h) sp hG hTM a ht htS)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
