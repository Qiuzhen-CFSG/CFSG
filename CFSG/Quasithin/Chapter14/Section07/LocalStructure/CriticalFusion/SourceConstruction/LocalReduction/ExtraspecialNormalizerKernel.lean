module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerPoint
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.GroupTheory.SylowNormalRestriction
/-!
# The literal point-centralizer kernel in the maximal normalizer

Write N = N_G(K), Y_K = C_N(L₁/O₂(L₁)), and C_K = C_N(K/O₂(K)).
These centralizers are kernels of the actual normalizer conjugation actions,
with their embedded images and relative normality retained. Comparing the
point action with the original star map gives T ∩ Y_K = R₁. The cubic
quotient has automorphism group of order two; the known index in T
therefore makes Y_K normal of index two in N, with Y_K T = N. Normal
Sylow restriction identifies the original R₁ as a Sylow subgroup of Y_K.
Finally O₂(L₁) = O₂(K) gives C_K ≤ Y_K.

The final theorem applies these deductions together with the maximal-local
normalizer and characteristic-point results to the original group and flag.
It supplies the opening inputs of Aschbacher–Smith 14.7.21(1), printed
pp.1049–1050, refs/quasithin.pdf. The proof that N_G(K) = H, the later
solvable/component exclusions and the final four-input assembly remain open.
Every genuine earlier source premise is retained for its existing producer.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem normalizerCore_le_sylow (H : Subgroup G) (hT : (T : Subgroup G) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup G) :=
  (pCoreIn_le_sylow H (T.subtype hT)).trans_eq (map_subgroupOf_eq_of_le hT)

omit [Finite G] in
private theorem pointAction_eq_one_iff_star
    (hn : F.H ≤ normalizer (F.Li L 1 : Set G)) (t : F.H) :
    pCoreNormalizerAction 2 (F.Li L 1) ⟨t,hn t.property⟩ = 1 ↔
      starMap F t ∈ centralizer (star F (F.Li L 1) : Set (HStar F.H)) := by
  let A := F.Li L 1
  have hAH : A ≤ F.H := (F.Li_le L 1).trans inf_le_right
  have hcore : A.pCoreIn 2 ≤ F.H.pCoreIn 2 := pCoreIn_mono_of_normalizes hAH hn
  rw [pCoreNormalizerAction_eq_one_iff]
  constructor
  · intro hfix x hx
    obtain ⟨a,ha,rfl⟩ := hx
    let aA : A := ⟨a,ha⟩
    have hh := hfix aA
    have hc : (t : G) * (a : G) * (t : G)⁻¹ / (a : G) ∈ F.H.pCoreIn 2 :=
      hcore (mem_map_of_mem A.subtype hh)
    have hc' : t * a * t⁻¹ / a ∈ pCore 2 F.H := by
      have hm : ((F.H.pCoreIn 2).subgroupOf F.H) = pCore 2 F.H :=
        comap_map_eq_self_of_injective F.H.subtype_injective _
      exact hm ▸ hc
    have hq : starMap F (t*a*t⁻¹/a) = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
    rw [map_div,map_mul,map_mul,map_inv,div_eq_one] at hq
    have heq : starMap F t * starMap F a = starMap F a * starMap F t := by
      have hh := congrArg (fun z => z * starMap F t) hq
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh
    exact heq.symm
  · intro hc a
    let aH : F.H := ⟨a,hAH a.property⟩
    have heq := hc (starMap F aH) (mem_map_of_mem (starMap F) a.property)
    have hq : starMap F (t*aH*t⁻¹/aH) = 1 := by
      rw [map_div,map_mul,map_mul,map_inv,←heq,mul_inv_cancel_right,div_self']
    have hk : t*aH*t⁻¹/aH ∈ pCore 2 F.H := (QuotientGroup.eq_one_iff _).mp hq
    let z := (F.Li L 1).normalizerMonoidHom ⟨t,hn t.property⟩ a / a
    have hz : (z : G) ∈ A.pCoreIn 2 :=
      inf_pCoreIn_le_of_le 2 hAH ⟨z.property,mem_map_of_mem F.H.subtype hk⟩
    have hm : (A.pCoreIn 2).subgroupOf A = pCore 2 A :=
      comap_map_eq_self_of_injective A.subtype_injective _
    exact hm ▸ hz

/-- Centralization of the literal point quotient inside N_G(K). -/
@[expose] def normalizerPointCentralizer (F : InvariantFlag T V 3) (L : Subgroup G) : Subgroup G :=
  normalizer (K F : Set G) ⊓
    (pCoreNormalizerAction 2 (F.Li L 1)).ker.map (normalizer (F.Li L 1 : Set G)).subtype

omit [Finite G] in
private theorem pointCentralizer_kernel
    (hn : normalizer (K F : Set G) ≤ normalizer (F.Li L 1 : Set G)) :
    normalizerPointCentralizer F L =
      ((pCoreNormalizerAction 2 (F.Li L 1)).comp (inclusion hn)).ker.map
        (normalizer (K F : Set G)).subtype := by
  ext x
  constructor
  · rintro ⟨hx,⟨a,ha,he⟩⟩
    refine ⟨⟨x,hx⟩,?_,rfl⟩
    change pCoreNormalizerAction 2 (F.Li L 1) (inclusion hn ⟨x,hx⟩) = 1
    have he' : a = inclusion hn ⟨x,hx⟩ := Subtype.ext he
    exact he' ▸ ha
  · rintro ⟨x,hx,rfl⟩
    exact ⟨x.property,⟨inclusion hn x,hx,rfl⟩⟩

/-- The point-centralizing normalizer meets the original T in precisely R₁. -/
theorem extraspecial_normalizer_point_sylow_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    (T : Subgroup G) ⊓ normalizerPointCentralizer F L = F.Ri L 1 := by
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful he
  have hHN := H_normalizes_K F
  have hHA := hHN.trans hn
  have hnA : ((F.Li L 1).subgroupOf F.H).Normal := normal_subgroupOf_of_le_normalizer hHA
  have hstar := point_core_star_eq_centralizer_of_normal h structural hnA
  have hRH : F.Ri L 1 ≤ F.H := (pCoreIn_le 2 _).trans Rechoice.group_le_H
  have hRT : F.Ri L 1 ≤ (T : Subgroup G) := normalizerCore_le_sylow _ le_sup_right
  have hcore : F.H.pCoreIn 2 ≤ F.Ri L 1 := by
    have hQT := normalizerCore_le_sylow F.H (F.invariant 1)
    exact (le_inf (hQT.trans le_sup_right) le_rfl).trans
      (inf_pCoreIn_le_of_le 2 Rechoice.group_le_H)
  have hpre : (star F (F.Ri L 1)).comap (starMap F) = (F.Ri L 1).subgroupOf F.H := by
    change (((F.Ri L 1).subgroupOf F.H).map (starMap F)).comap (starMap F) = _
    rw [comap_map_eq,starMap,QuotientGroup.ker_mk']
    apply sup_eq_left.mpr
    intro x hx
    exact hcore (mem_map_of_mem F.H.subtype hx)
  rw [pointCentralizer_kernel hn]
  ext t
  constructor
  · rintro ⟨ht,⟨a,ha,heq⟩⟩
    let tH : F.H := ⟨t,F.invariant 1 ht⟩
    have htfix : pCoreNormalizerAction 2 (F.Li L 1) ⟨tH,hHA tH.property⟩ = 1 := by
      have hae : inclusion hn a = ⟨tH,hHA tH.property⟩ := Subtype.ext heq
      exact hae ▸ ha
    have hm : starMap F tH ∈ star F (F.Ri L 1) := by
      rw [hstar]
      exact ⟨mem_map_of_mem (starMap F) ht,(pointAction_eq_one_iff_star hHA tH).mp htfix⟩
    have hh : tH ∈ (star F (F.Ri L 1)).comap (starMap F) := hm
    rw [hpre] at hh
    exact hh
  · intro ht
    have htT := hRT ht
    let tH : F.H := ⟨t,hRH ht⟩
    have hm : starMap F tH ∈ star F (F.Ri L 1) := mem_map_of_mem (starMap F) ht
    have hc : starMap F tH ∈ centralizer (star F (F.Li L 1) : Set (HStar F.H)) :=
      (hstar ▸ hm).2
    exact ⟨htT,⟨⟨t,hHN tH.property⟩,(pointAction_eq_one_iff_star hHA tH).mpr hc,rfl⟩⟩

/-- Source 14.7.21: Y_K is normal of index two in N_G(K), and T supplements it. -/
theorem extraspecial_normalizer_point_index
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ((normalizerPointCentralizer F L).subgroupOf (normalizer (K F : Set G))).Normal ∧
      (normalizerPointCentralizer F L).relIndex (normalizer (K F : Set G)) = 2 ∧
      normalizerPointCentralizer F L ⊔ (T : Subgroup G) = normalizer (K F : Set G) := by
  let N := normalizer (K F : Set G)
  let Y := normalizerPointCentralizer F L
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful he
  let f := (pCoreNormalizerAction 2 (F.Li L 1)).comp (inclusion hn)
  have hY : Y = f.ker.map N.subtype := pointCentralizer_kernel hn
  have hYN : Y.subgroupOf N = f.ker := by
    rw [hY]
    exact comap_map_eq_self_of_injective N.subtype_injective _
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hnA : ((F.Li L 1).subgroupOf F.H).Normal :=
    normal_subgroupOf_of_le_normalizer ((H_normalizes_K F).trans hn)
  have hR : (F.Ri L 1).relIndex (T : Subgroup G) = 2 := by
    have hcore : pCore 2 F.H ≤ (F.Ri L 1).subgroupOf F.H := by
      intro x hx
      have hQT := normalizerCore_le_sylow F.H (F.invariant 1)
      exact inf_pCoreIn_le_of_le 2 Rechoice.group_le_H
        ⟨mem_sup_right (hQT (mem_map_of_mem F.H.subtype hx)),mem_map_of_mem F.H.subtype hx⟩
    have hcoreT : pCore 2 F.H ≤ (T : Subgroup G).subgroupOf F.H := by
      intro x hx
      exact normalizerCore_le_sylow F.H (F.invariant 1) (mem_map_of_mem F.H.subtype hx)
    have hh := point_core_star_index_two_of_normal h structural hnA
    change (((F.Ri L 1).subgroupOf F.H).map (starMap F)).relIndex
      (((T : Subgroup G).subgroupOf F.H).map (starMap F)) = 2 at hh
    rw [relIndex_map_map,starMap,QuotientGroup.ker_mk',sup_eq_left.mpr hcore,
      sup_eq_left.mpr hcoreT,relIndex_subgroupOf (show (T : Subgroup G) ≤ F.H from F.invariant 1)] at hh
    exact hh
  have hYT : Y.relIndex (T : Subgroup G) = 2 := by
    rw [←inf_relIndex_left,extraspecial_normalizer_point_sylow_intersection h hab structural previous faithful he]
    exact hR
  have hkt : f.ker.relIndex ((T : Subgroup G).subgroupOf N) = 2 := by
    rw [←hYN,relIndex_subgroupOf hTN]
    exact hYT
  have hc := pointResidual_core_quotient_card h structural (F := F)
  let : IsCyclic ((F.Li L 1) ⧸ pCore 2 (F.Li L 1)) := isCyclic_of_prime_card hc
  have hAut : Nat.card (MulAut ((F.Li L 1) ⧸ pCore 2 (F.Li L 1))) = 2 := by
    rw [IsCyclic.card_mulAut,hc]
    decide
  have hd : f.ker.index ∣ 2 := by
    rw [index_ker]
    simpa only [hAut] using f.range.card_subgroup_dvd_card
  have htwo : 2 ∣ f.ker.index := by
    simpa only [hkt] using relIndex_dvd_index_of_normal f.ker ((T : Subgroup G).subgroupOf N)
  have hi : f.ker.index = 2 := Nat.dvd_antisymm hd htwo
  have hindex : Y.relIndex N = 2 := by
    change (Y.subgroupOf N).index = 2
    rwa [hYN]
  have hnY : (Y.subgroupOf N).Normal := hYN ▸ inferInstanceAs f.ker.Normal
  refine ⟨hnY,hindex,?_⟩
  let := hnY
  have hYNle : Y ≤ N := inf_le_left
  have hjoin : Y ⊔ (T : Subgroup G) ≤ N := sup_le hYNle hTN
  have hrel : Y.relIndex (Y ⊔ (T : Subgroup G)) = 2 := by
    rw [←relIndex_subgroupOf hjoin,subgroupOf_sup hYNle hTN,relIndex_sup_left,
      relIndex_subgroupOf hTN,hYT]
  have hm := relIndex_mul_relIndex Y (Y ⊔ (T : Subgroup G)) N le_sup_left hjoin
  rw [hrel,hindex] at hm
  have h1 : (Y ⊔ (T : Subgroup G)).relIndex N = 1 := by omega
  exact le_antisymm hjoin (relIndex_eq_one.mp h1)

/-- R₁ is the literal Sylow two-subgroup in the point-centralizing normalizer. -/
theorem extraspecial_normalizer_point_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    IsSylowIn 2 (F.Ri L 1) (normalizerPointCentralizer F L) := by
  let N := normalizer (K F : Set G)
  let Y := normalizerPointCentralizer F L
  have hTN : (T : Subgroup G) ≤ N := (F.invariant 1).trans (H_normalizes_K F)
  have hYN : Y ≤ N := inf_le_left
  let := (extraspecial_normalizer_point_index h hab structural previous faithful he).1
  obtain ⟨S,hS⟩ := (T.subtype hTN).exists_sylow_map_eq_inf_of_normal (Y.subgroupOf N)
  let e := subgroupOfEquivOfLe hYN
  refine ⟨S.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change ((S : Subgroup (Y.subgroupOf N)).map e.toMonoidHom).map Y.subtype = F.Ri L 1
  rw [map_map]
  have heq : Y.subtype.comp e.toMonoidHom = N.subtype.comp (Y.subgroupOf N).subtype := rfl
  rw [heq,←map_map,hS,Subgroup.map_inf _ _ N.subtype N.subtype_injective]
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTN,map_subgroupOf_eq_of_le hYN]
  exact extraspecial_normalizer_point_sylow_intersection h hab structural previous faithful he

/-- The literal centralizer of K/O₂(K) in N_G(K). -/
@[expose] def normalizerResidualCentralizer (F : InvariantFlag T V 3) : Subgroup G :=
  (pCoreNormalizerAction 2 (K F)).ker.map (normalizer (K F : Set G)).subtype

/-- Centralization of the residual quotient implies centralization of the
point quotient, with the common two-core retained. -/
theorem extraspecial_normalizer_residualCentralizer_le_pointCentralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    normalizerResidualCentralizer F ≤ normalizerPointCentralizer F L := by
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful he
  have hP := (extraspecial_centralizer_core_reduction_no_small_intervals h hab structural previous faithful he).1
  rintro x ⟨n,hnker,rfl⟩
  refine ⟨n.property,⟨inclusion hn n,?_,rfl⟩⟩
  change pCoreNormalizerAction 2 (F.Li L 1) (inclusion hn n) = 1
  rw [pCoreNormalizerAction_eq_one_iff]
  intro a
  let aK : K F := ⟨a,pointResidual_le F a.property⟩
  have hk := (pCoreNormalizerAction_eq_one_iff 2 (K F) n).mp hnker aK
  let z := (F.Li L 1).normalizerMonoidHom (inclusion hn n) a / a
  have hz : (z : G) ∈ (K F).pCoreIn 2 := mem_map_of_mem (K F).subtype hk
  rw [←hP] at hz
  have hc : ((F.Li L 1).pCoreIn 2).subgroupOf (F.Li L 1) = pCore 2 (F.Li L 1) :=
    comap_map_eq_self_of_injective (F.Li L 1).subtype_injective _
  exact hc ▸ hz

/-- Apply the normalizer construction to the original group and flag.
These are the opening normalizer inputs to 14.7.21(1), not its final equality H=N_G(K). -/
theorem extraspecial_normalizer_source_setup
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let Y := normalizerPointCentralizer F L
    IsMaximalTwoLocal N ∧
      {M : Subgroup G | IsMaximalTwoLocal M ∧ F.H ≤ M} = {N} ∧
      normalizer ((K F).pCoreIn 2 : Set G) = N ∧
      normalizer (F.Li L 1 : Set G) = N ∧
      (Y.subgroupOf N).Normal ∧ Y.relIndex N = 2 ∧ Y ⊔ (T : Subgroup G) = N ∧
      (T : Subgroup G) ⊓ Y = F.Ri L 1 ∧ IsSylowIn 2 (F.Ri L 1) Y ∧
      normalizerResidualCentralizer F ≤ Y := by
  obtain ⟨hm,hu⟩ := extraspecial_residual_normalizer_unique d h hab structural previous faithful he
  obtain ⟨hp,ha⟩ := extraspecial_core_normalizer_eq d h hab structural previous faithful he
  obtain ⟨hn,hi,hgen⟩ := extraspecial_normalizer_point_index h hab structural previous faithful he
  exact ⟨hm,hu,hp,ha,hn,hi,hgen,
    extraspecial_normalizer_point_sylow_intersection h hab structural previous faithful he,
    extraspecial_normalizer_point_sylow h hab structural previous faithful he,
    extraspecial_normalizer_residualCentralizer_le_pointCentralizer h hab structural previous faithful he⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
