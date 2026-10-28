module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.ResidualControl
public import CFSG.Quasithin.Chapter15.Section01.CaseI.SylowControl
public import Theory.GroupTheory.PResidual.CentralizingSupplement

/-!
# The literal Thompson-normalizer actor before rank-one exclusion

In H = C_M(Z₁), the normal module V is centralized by J(S)=J(T).
The Thompson Frattini factorization therefore makes N_H(J(T)) a
supplement to C_H(V). Its two-residual has exactly the original moving
commutator, and is still contained in O²(H). Thus it normalizes the
selected component and generates the moving subgroup by commutators.

This shared input applies to both the ordinary and constrained cases,
and to both source primes. It does not select exchanged planes or
assert the remaining block automorphism calculation.
Source: Aschbacher--Smith 15.1.21(ii), printed p.1098.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- The original local Thompson normalizer, before any model selection. -/
def rankOneThompsonNormalizer (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (M ⊓ d.G1) ⊓ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)

/-- Its residual is embedded in the original ambient group. -/
def rankOneThompsonResidual (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (pResidual 2 d.rankOneThompsonNormalizer).map d.rankOneThompsonNormalizer.subtype

theorem rankOneThompsonResidual_le (d : CaseIComponentData T M Mc V) :
    d.rankOneThompsonResidual ≤
      (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype :=
  embedded_pResidual_mono 2 inf_le_left

/-- The Frattini residual retains the literal moving subgroup of 15.1.16. -/
theorem PreExclusionSource.thompsonResidual_commutator
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ⁅V, d.rankOneThompsonResidual⁆ =
      ⁅V, (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ := by
  let := h.elementary
  let H := M ⊓ d.G1
  have hVH : V ≤ H := le_inf h.le_selected
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  have hHV : H ≤ normalizer (V : Set G) := inf_le_left.trans h.normalized
  let : (V.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHV
  obtain ⟨P, hP⟩ := s.centralizer_sylow.restrict
    (le_inf (d.S_le_T.trans hM.1.2) d.S_le_G1) inf_le_right
  have hJS := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
  change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at hJS
  have hmapJ : (elementaryAbelianMaxJ (P : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hP, hJS]
  have hJP : elementaryAbelianMaxJ (P : Subgroup H) ≤
      centralizer (V.subgroupOf H : Set H) := by
    intro j hj v hv
    apply Subtype.ext
    exact (hJ (hmapJ ▸ mem_map_of_mem H.subtype hj)) v (h.le_local hv)
  let N := normalizer (elementaryAbelianMaxJ (P : Subgroup H) : Set H)
  have hgen : N ⊔ centralizer (V.subgroupOf H : Set H) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨n, hn, c, hc, rfl⟩ := ChapterB.thompson_normalizer_factorization
      (V.subgroupOf H) P hJP x
    exact mul_mem_sup hn hc
  have hN : N.map H.subtype = d.rankOneThompsonNormalizer := by
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ H := by
      rw [← hmapJ]
      exact map_subtype_le _
    have he : elementaryAbelianMaxJ (P : Subgroup H) =
        (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H := by
      apply map_injective H.subtype_injective
      rw [hmapJ, map_subgroupOf_eq_of_le hJT]
    dsimp [N, rankOneThompsonNormalizer]
    rw [he, ← subgroupOf_normalizer_eq hJT, subgroupOf_map_subtype, inf_comm]
  have he := congrArg (map H.subtype)
    (commutator_embedded_pResidual_eq_of_centralizing_sup 2 (V.subgroupOf H) N hgen)
  simp only [map_commutator, map_subgroupOf_eq_of_le hVH,
    map_embedded_pResidual] at he
  rw [hN] at he
  exact he

/-- An actual two-perfect actor in N_M(J(T)) normalizes L and generates
the original moving subgroup. No assertion about its centralization of L
is assumed or made here. -/
theorem PreExclusionSource.thompsonResidual_action
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    IsPPerfect 2 d.rankOneThompsonResidual ∧
      d.rankOneThompsonResidual ≤ normalizer (d.L : Set G) ∧
      d.rankOneThompsonResidual ≤ normalizer (elementaryAbelianMaxJ d.S : Set G) ∧
      ⁅⁅V, (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆,
        d.rankOneThompsonResidual⁆ =
        ⁅V, (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype⁆ := by
  let := h.elementary
  have hp : IsPPerfect 2 d.rankOneThompsonResidual := isPPerfect_embedded_pResidual 2 _
  have hn : d.rankOneThompsonResidual ≤ normalizer (V : Set G) :=
    d.rankOneThompsonResidual_le.trans (((map_subtype_le _).trans inf_le_left).trans h.normalized)
  refine ⟨hp, d.rankOneThompsonResidual_le.trans (le_sup_left.trans s.residual_normalizes), ?_, ?_⟩
  · have hJS := (h.caseI_marked_thompson_control hG T hM hJ d.Z1_le_fixed).1
    change elementaryAbelianMaxJ d.S = elementaryAbelianMaxJ (T : Subgroup G) at hJS
    rw [hJS]
    exact (map_subtype_le _).trans inf_le_right
  · rw [← s.thompsonResidual_commutator (h := h) hG hM hJ]
    exact commutator_isPPerfect_idempotent _ V hp (IsElementaryAbelian.isPGroup 2 V) hn

/-- The Thompson-normalizer residual must act nontrivially on the original
component. This obstruction is available before any exchanged selection. -/
theorem PreExclusionSource.thompsonResidual_not_centralizes
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ¬ d.rankOneThompsonResidual ≤ centralizer (d.L : Set G) := by
  intro hc
  exact s.false_of_moving_actor_centralizes (h := h) hc
    (s.thompsonResidual_action (h := h) hG hM hJ).2.2.2

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
