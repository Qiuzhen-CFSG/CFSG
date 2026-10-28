module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Escaping.Source.Residual
public import Theory.SpecificGroups.Alternating.FiveTwoCoreExtension
public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients

/-!
# The actual terminal conjugate has corank at most two

The source quotient-centralizer X contains C_T(V). For the selected H in XT,
O₂(H) intersect X lies in O₂(L₁H): adjoining O₂(L₁) makes this intersection
normal under both L₁ and H. The actual A₅ residual of H identifies H/O₂(H)
as A₅ or S₅, whose two-rank is at most two. Apply that rank bound only to
the elementary image of the original conjugate A=Vᵍ. Its kernel lies in
A intersect O₂(L₁H), giving the literal terminal corank bound.

This avoids assuming that all of O₂(H) is normal in L₁H, or that prime rank
is monotone under arbitrary quotients. The source incidence, quotient maps
and selected H are unchanged. Source: Aschbacher--Smith, proof of 12.5.1,
printed p.822. Final exterior exclusion remains with qt-d-1251-source.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

omit [Finite G] in
private theorem normalizes_core_join (K N C : Subgroup G)
    (hn : K ≤ normalizer (N : Set G)) (hc : ⁅K,C⁆ ≤ N) :
    K ≤ normalizer ((N ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro k hk x hx
  have he : N ⊔ C ≤ (N ⊔ C).comap (MulAut.conj k).toMonoidHom := by
    apply sup_le
    · intro n hn'
      exact mem_sup_left (le_normalizer_iff.mp hn k hk n hn')
    · intro c hc'
      have hh := (N ⊔ C).mul_mem
        (mem_sup_left (hc (commutator_mem_commutator hk hc'))) (mem_sup_right hc')
      change k * c * k⁻¹ ∈ N ⊔ C
      simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using hh
  exact he hx

namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)
include h structural

omit structural in
/-- The actual Sylow centralizer acts trivially on L₁/O₂(L₁). -/
theorem sylow_centralizer_le_pointSupplement :
    (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ s.pointSupplement := by
  have hTL : (T : Subgroup G) ≤ normalizer (s.marking.Li 1 : Set G) :=
    (le_inf le_sup_right s.sylow_le_G₁).trans (s.Mi_normalizes_Li 1)
  apply le_pCoreActionKernelIn_of_commutator 2 (s.marking.Li 1) (s.marking.Gi 1) _
    (inf_le_left.trans s.sylow_le_G₁) (inf_le_left.trans hTL)
  have hJL : s.marking.Li 1 ≤ L ⊔ (T : Subgroup G) :=
    (s.marking.Li_le_L 1).trans le_sup_left
  apply le_trans (le_inf ?_ ?_) (inf_pCoreIn_le_of_le 2 hJL)
  · exact le_normalizer_iff_commutator_le_left.mp (inf_le_left.trans hTL)
  · rw [exterior_sylow_centralizer_eq_core s h]
    exact le_normalizer_iff_commutator_le_right.mp
      (((s.marking.Li_le_L 1).trans le_sup_left).trans
        ((L ⊔ (T : Subgroup G)).le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))

/-- The kernel used for the conjugate image lies in the full terminal core. -/
theorem HStar_core_inf_supplement_le_terminal_core {H : Subgroup G}
    (hHG : H ≤ s.marking.Gi 1) :
    H.pCoreIn 2 ⊓ s.pointSupplement ≤ terminalCore s.marking H := by
  let N := (s.marking.Li 1).pCoreIn 2
  let C := H.pCoreIn 2 ⊓ s.pointSupplement
  have hGN : s.marking.Gi 1 ≤ normalizer (N : Set G) :=
    ((normal_subgroupOf_iff_le_normalizer (s.marking.Li_le_Gi 1)).mp
      (s.point_component_normal_from_source h structural).2).trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hHN : H ≤ normalizer (N : Set G) := hHG.trans hGN
  have hHC : H ≤ normalizer (C : Set G) :=
    (le_inf (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
      (hHG.trans (s.point_group_normalizes_supplement h structural))).trans
        inf_normalizer_le_normalizer_inf
  have hLN : s.marking.Li 1 ≤ normalizer (N : Set G) :=
    (s.marking.Li_le_Gi 1).trans hGN
  have hLC : ⁅s.marking.Li 1,C⁆ ≤ N :=
    (commutator_mono le_rfl inf_le_right).trans
      (pCoreActionKernelIn_commutator 2 (s.marking.Li 1) (s.marking.Gi 1))
  have hnL := normalizes_core_join (s.marking.Li 1) N C hLN hLC
  have hnH := (le_inf hHN hHC).trans (normalizer_inf_normalizer_le_normalizer_sup N C)
  have hp : IsPGroup 2 (N ⊔ C : Subgroup G) :=
    (isPGroup_pCoreIn 2 (s.marking.Li 1)).to_sup_of_normal_left'
      ((isPGroup_pCoreIn 2 H).to_le inf_le_left)
      ((inf_le_left.trans (pCoreIn_le 2 H)).trans hHN)
  exact le_sup_right.trans (le_pCoreIn_of_normalizes hp
    (sup_le ((pCoreIn_le 2 _).trans le_sup_left)
      ((inf_le_left.trans (pCoreIn_le 2 H)).trans le_sup_right))
    (sup_le hnL hnH))

/-- The original H has two-rank at most two after its intrinsic core is removed. -/
theorem HStar_in_pointSupplement_quotient_two_rank {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G)) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
  obtain ⟨e⟩ := s.HStar_in_pointSupplement_residual_a5 h structural hH hHX
  let S := T.subtype hH.1.1.2
  have he := Theory.SpecificGroups.Alternating.FiveExtensionAction.core_quotient_of_two_supplement
    (pResidual 2 H) (S : Subgroup H) le_normalizer_of_normal S.isPGroup' e
  rw [pResidual_sup_sylow_eq_top S] at he
  let c := QuotientGroup.congr _ _ (topEquiv : (⊤ : Subgroup H) ≃* H)
    (pCore_map_iso 2 topEquiv)
  rcases he with ha | ha
  · obtain ⟨a⟩ := ha
    rw [primeRank_congr 2 (c.symm.trans a)]
    exact (primeRank_subgroup_le 2 _).trans
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
  · obtain ⟨a⟩ := ha
    rw [primeRank_congr 2 (c.symm.trans a)]
    exact Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two

/-- Corank two for the actual conjugate, with no additional rank premise. -/
theorem terminal_corank_le_two_in_pointSupplement {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHX : H ≤ s.pointSupplement ⊔ (T : Subgroup G))
    {g : G} (hAT : V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G))
    (hAC : V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (terminalIntersection s.marking H g) ≤ 2 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  have hAH : A ≤ H := hAT.trans hH.1.1.2
  have hHG : H ≤ s.marking.Gi 1 := hHX.trans
    (sup_le s.pointSupplement_le_point s.sylow_le_G₁)
  have hAX : A ≤ s.pointSupplement :=
    (le_inf hAT hAC).trans (s.sylow_centralizer_le_pointSupplement h)
  have hker : A ⊓ H.pCoreIn 2 ≤ terminalIntersection s.marking H g :=
    le_inf inf_le_left ((le_inf inf_le_right (inf_le_left.trans hAX)).trans
      (s.HStar_core_inf_supplement_le_terminal_core h structural hHG))
  apply (ChapterE.Section06.subgroupCorank_antitone hker).trans
  let q := QuotientGroup.mk' (pCore 2 H)
  let I := (A.subgroupOf H).map q
  have he : subgroupCorank A (A ⊓ H.pCoreIn 2) = Nat.log 2 (Nat.card I) := by
    unfold subgroupCorank
    congr 1
    rw [inf_relIndex_left, ← relIndex_ker, QuotientGroup.ker_mk']
    have hh : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
      comap_map_eq_self_of_injective H.subtype_injective _
    rw [←hh,relIndex_subgroupOf hAH]
  rw [he]
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 I := IsElementaryAbelian.map _
  have hr : Representation.BinaryOffender.rank I ≤ primeRank 2 I := by
    let : IsElementaryAbelian 2 (⊤ : Subgroup I) :=
      IsElementaryAbelian.of_injective (⊤ : Subgroup I).subtype Subtype.val_injective
    simpa only [Representation.BinaryOffender.rank,Subgroup.card_top] using
      (offender_rank_le_primeRank (⊤ : Subgroup I))
  exact hr.trans ((primeRank_subgroup_le 2 I).trans
    (s.HStar_in_pointSupplement_quotient_two_rank h structural hH hHX))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
