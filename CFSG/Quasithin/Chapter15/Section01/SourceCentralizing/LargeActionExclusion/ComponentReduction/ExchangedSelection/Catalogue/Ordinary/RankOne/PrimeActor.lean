module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.RankOne.Geometry
public import Theory.GroupTheory.PResidual.PermutingPrimeLift
public import Theory.GroupTheory.Commutator.FixedSeedKernel

/-!
# The actual prime actor for the ordinary and constrained rank-one arguments

The Thompson Frattini factorization makes the original normalizer inside
C_M(Z₁) surject onto C_M(Z₁)/C_M(V). The quotient's two-residual has the
original prime order p. The permuting prime-lift theorem therefore supplies
a p-subgroup Y of N_M(J(T)) ∩ G₁, with SY = YS. Equal images modulo the
centralizer of V give [V,Y] = [V,O²(C_M(Z₁))], and two-perfect commutator
idempotence gives [V₂,Y] = V₂.

No ordinary model, constrained block, or exchanged selection is assumed.
The same actor feeds both branches of 15.1.21(ii). Its construction is
complete here; the model calculation centralizing it remains with the
ordinary rank-one owner and the constrained rank-one owner respectively.
Source: Aschbacher--Smith 15.1.21(ii), printed p.1098.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}

/-- The prime actor of 15.1.21(ii), in the original Thompson normalizer. -/
theorem PreExclusionSource.rankOne_prime_actor
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ∃ Y : Subgroup G, d.RankOnePrimeActor p Y ∧
      Y ≤ (pResidual 2 (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype := by
  let := h.elementary
  let : Fact p.Prime := ⟨s.prime_prime⟩
  let H := M ⊓ d.G1
  let C := (M ⊓ centralizer (V : Set G)).subgroupOf H
  let : C.Normal := caseI_module_centralizer_normal (Z1 := d.Z1) h.normalized
  let q := QuotientGroup.mk' C
  let N := d.rankOneThompsonNormalizer
  have hNH : N ≤ H := inf_le_left
  let i := inclusion hNH
  let f := q.comp i
  have hVH : V ≤ H := le_inf h.le_selected
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  have hHV : H ≤ normalizer (V : Set G) := inf_le_left.trans h.normalized
  let : (V.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHV
  have hSH : d.S ≤ H := le_inf (d.S_le_T.trans hM.1.2) d.S_le_G1
  obtain ⟨P,hP⟩ := s.centralizer_sylow.restrict hSH inf_le_right
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
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective C a
    obtain ⟨n,hn,c,hc,hx⟩ := ChapterB.thompson_normalizer_factorization
      (V.subgroupOf H) P hJP x
    have hnJ : (n : G) ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
      rw [← hmapJ]
      exact le_normalizer_map H.subtype (mem_map_of_mem H.subtype hn)
    have hnN : (n : G) ∈ N := ⟨n.property,hnJ⟩
    refine ⟨⟨n,hnN⟩, ?_⟩
    have hcC : c ∈ C := by
      refine ⟨c.property.1, ?_⟩
      intro v hv
      exact congrArg Subtype.val (hc ⟨v,hVH hv⟩ hv)
    have hqc : q c = 1 := (QuotientGroup.eq_one_iff c).mpr hcC
    change q n = q x
    rw [← hx, map_mul, hqc, mul_one]
  have hSN : d.S ≤ N := by
    refine le_inf hSH ?_
    rw [← hJS]
    exact d.S.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ d.S)
  obtain ⟨PN,hPN⟩ := s.centralizer_sylow.restrict hSN (hNH.trans inf_le_right)
  obtain ⟨Y0,hY0p,hY0perf,hperm,himage,hY0R⟩ :=
    exists_permuting_prime_residual_lift f hf PN s.residual_card
  let Y := Y0.map N.subtype
  have hYN : Y ≤ N := map_subtype_le _
  have hYperfect : IsPPerfect 2 Y := hY0perf.of_surjective
    (N.subtype.subgroupMap Y0) (N.subtype.subgroupMap_surjective Y0)
  have hYR : Y ≤ (pResidual 2 H).map H.subtype := by
    have he : N.subtype = H.subtype.comp i := rfl
    rw [show Y = Y0.map N.subtype from rfl, he, ← Subgroup.map_map]
    exact map_mono ((map_mono hY0R).trans (map_pResidual_le 2 i))
  have hYperm : (d.S : Set G) * (Y : Set G) = (Y : Set G) * (d.S : Set G) := by
    have he := congrArg (Set.image N.subtype) hperm
    rw [Set.image_mul, Set.image_mul] at he
    change ((PN : Subgroup N).map N.subtype : Set G) * (Y : Set G) =
      (Y : Set G) * ((PN : Subgroup N).map N.subtype : Set G) at he
    rwa [hPN] at he
  have hsame : (Y0.map i).map q = (pResidual 2 H).map q := by
    rw [Subgroup.map_map, map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective C)]
    exact himage
  have hker : q.ker ≤ centralizer (V.subgroupOf H : Set H) := by
    rw [QuotientGroup.ker_mk']
    intro c hc v hv
    exact Subtype.ext (hc.2 v hv)
  have hcomm : ⁅V,Y⁆ = ⁅V,(pResidual 2 H).map H.subtype⁆ := by
    have he := congrArg (map H.subtype)
      (commutator_eq_of_centralizing_kernel (V.subgroupOf H) (V.subgroupOf H)
        (Y0.map i) (pResidual 2 H) q hker le_rfl hsame)
    rw [map_commutator, map_commutator, map_subgroupOf_eq_of_le hVH,
      Subgroup.map_map] at he
    exact he
  refine ⟨Y, ⟨hY0p.map N.subtype,hYN,hYperm,?_⟩,hYR⟩
  rw [← hcomm]
  exact commutator_isPPerfect_idempotent Y V hYperfect
    (IsElementaryAbelian.isPGroup 2 V) ((hYN.trans hNH).trans hHV)

/-- The constructed actor normalizes the actual component and cannot
centralize it. This is the precise contradiction for the model action
calculation in source case (ii), before any exchanged selection. -/
theorem PreExclusionSource.rankOne_prime_actor_noncentral
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G)) :
    ∃ Y : Subgroup G, d.RankOnePrimeActor p Y ∧
      Y ≤ normalizer (d.L : Set G) ∧ ¬ Y ≤ centralizer (d.L : Set G) := by
  obtain ⟨Y,hY,hYR⟩ := s.rankOne_prime_actor (h := h) hG hM hJ
  exact ⟨Y,hY,hYR.trans (le_sup_left.trans s.residual_normalizes),
    fun hc => s.false_of_moving_actor_centralizes (h := h) hc hY.moves⟩

end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
