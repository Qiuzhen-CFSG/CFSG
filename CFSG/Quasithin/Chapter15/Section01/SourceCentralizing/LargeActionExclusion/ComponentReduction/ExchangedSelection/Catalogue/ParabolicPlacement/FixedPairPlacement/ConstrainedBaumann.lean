module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalSeparation
public import Theory.GroupAction.SylowFixedCommutator

/-!
# Baumann normalization for the original constrained local family

The original central-involution seed moves every escaping local member K.
In H = K N_S(K), odd-orbit averaging gives a noncentral fixed vector in
[⟨Z^H⟩,K]. Thompson heredity places that vector in α(S). The established
separation of distinct conjugate moved supports then prevents Baum(S)
from moving K.

This argument retains the original ambient hypotheses and works for every
constrained local member, without a rank-one model or S-normalization.
It supplies the missing normalization for the literal same-pair placement.
Source: Aschbacher--Smith C.1.16(3), pp.125--126, and the local action in
15.1.20(2), used in 15.1.22(*), pp.1094--1099.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC ChapterC.RankOne.ChiProduct.SelectedRankOne
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

theorem localFamily_seed_fixed_witness (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    ∃ u ∈ d.normalizerMoved K, u ∈ thompsonAlpha d.S ∧ u ∉ centralizer (K : Set G) := by
  obtain ⟨⟨P,hP⟩,hJRS,hZR⟩ := d.localFamily_normalizer_setup h hM.1.2 hu hK hq hout hf
  let H := K ⊔ d.normalizerSylow K
  let U := d.normalizerModule K
  let K0 := K.subgroupOf H
  let : K0.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer inf_le_right)
  have a := d.localFamily_normalizerAction hG hempty hM hJ hu h hK hq hout hf
  let := a.reduced.elementary
  have hgen : K0 ⊔ (P : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show K ≤ H from le_sup_left),hP,
      ←MonoidHom.range_eq_map,range_subtype]
  have hZnc : ¬ centralInvolutions T ≤ centralizer (K : Set G) := by
    intro hc
    have hMc : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
      hu ▸ Set.mem_singleton Mc
    exact hout (le_inf hK.1 ((le_centralizer_iff.mp hc).trans hMc.2))
  obtain ⟨z,hz,hnc⟩ := SetLike.not_le_iff_exists.mp hZnc
  let zH : H := ⟨z,mem_sup_right (hZR hz)⟩
  let zU : U := ⟨zH,le_normalClosure hz⟩
  have hfix : ∀ s ∈ P, s*zH = zH*s := by
    intro s hs
    apply Subtype.ext
    exact centralInvolutions_le_centralizer_sylow T hz s
      (d.S_le_T (show (s:G) ∈ d.S from (hP ▸ mem_map_of_mem H.subtype hs).1))
  have hncH : zH ∉ centralizer (K0 : Set H) := by
    intro hc
    apply hnc
    intro k hk
    exact congrArg H.subtype (hc ⟨k,mem_sup_left hk⟩ hk)
  obtain ⟨w,hw,hwP,hwK⟩ := Theory.GroupAction.exists_moved_sylow_fixed_of_seed U K0 P hgen zU hfix hncH
  let W := (⁅U,K0⁆ : Subgroup H) ⊓ centralizer (P : Set H)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le
    (show W ≤ U from inf_le_left.trans (commutator_le_left U K0))
  have hWP : W ≤ (P : Subgroup H) :=
    inf_le_left.trans ((commutator_le_left U K0).trans
      (a.reduced.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P)))
  have hJP : elementaryAbelianMaxJ (P : Subgroup H) ≤ P := sSup_le fun _ hA => hA.1
  have hua : w ∈ thompsonAlpha (P : Subgroup H) :=
    elementary_centralizer_maxJ_le_omegaCenter (P : Subgroup H) W hWP
      (inf_le_right.trans (centralizer_le hJP)) ⟨hw,hwP⟩
  have hα : (thompsonAlpha (P : Subgroup H)).map H.subtype = thompsonAlpha d.S := by
    unfold thompsonAlpha
    rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,hP,hJRS]
  refine ⟨w,mem_map_of_mem H.subtype hw,hα ▸ mem_map_of_mem H.subtype hua,?_⟩
  intro hc
  apply hwK
  intro k hk
  exact Subtype.ext (hc k hk)

theorem localFamily_baumann_normalizes (d : CaseIComponentData T M Mc V)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ d.MZ)
    (hf : generalizedFitting K = pCore 2 K) :
    baumann d.S ≤ normalizer (K : Set G) := by
  obtain ⟨u,huW,hua,huc⟩ := d.localFamily_seed_fixed_witness hG hempty hM hJ hu h hK hq hout hf
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hn
  have hfix : g*u*g⁻¹ = u := mul_inv_eq_iff_eq_mul.mpr (hg.2 u hua).symm
  have huim : u ∈ (d.normalizerMoved K).map (MulAut.conj g).toMonoidHom := by
    rw [←hfix]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom huW
  exact huc (d.localFamily_moved_separation hG hempty hM hJ hu h hK hq hout hf g hg.1 hn huim)

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
