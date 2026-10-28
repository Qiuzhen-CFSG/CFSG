module
public import CFSG.Quasithin.Chapter15.Section01.OrderingSource.Placement
public import Theory.GroupTheory.PResidual.SymmetricThreeProducts

/-!
# Ordering pieces from the original restricted local action

Restrict the literal local centralizer quotient to a minimal parabolic. If
its action image is a two-group, its Sylow image fills it, so the parabolic
lies in the product of the selected Sylow group and the module centralizer.
Otherwise its odd residual supplies the reduced module used by Baumann
control, placing the whole parabolic in the selected maximal local subgroup.

Source: Aschbacher–Smith, original 14.1.4, printed p.976.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem source_minimalParabolic_ordering_piece
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M N H : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hN : N ∈ Chapter1.HOver G (T : Set G))
    (hP : IsMinimalParabolicOver T H) (hHN : H ≤ N)
    (hodd : Odd (Nat.card (pResidual 2
      ((H.subgroupOf N).map (localActionMap (centralInvolutions T) N))))) :
    H ≤ (N ⊓ M) ⊔ (N ⊓ centralizer (localModule T N : Set G)) := by
  have hTH : (T : Subgroup G) ≤ H := hP.1.1.le
  have hH := Chapter3.mem_HOver_of_sylow_interval T hTH hHN hN
  let V := localModule T N
  have hVN : V ≤ N := conjugateSpanBy_le_self
    (fun z hz => hN.2 ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)
  have hVT : V ≤ (T : Subgroup G) := by
    have hh := (localModule_reduced_from_source hG T hN).le_pCore.trans
      (pCore_isPGroup.le_sylow_of_normal (T.subtype hN.2))
    have hm := map_mono (f := N.subtype) hh
    change (V.subgroupOf N).map N.subtype ≤ ((T : Subgroup G).subgroupOf N).map N.subtype at hm
    rwa [map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hN.2] at hm
  have hVH := hVT.trans hTH
  let U := V.subgroupOf H
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (hHN.trans (le_normalizer_conjugateSpanBy _ _))
  let : IsElementaryAbelian 2 V := localModule_elementary_from_source hG T hN
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVH
  let q := localActionMap (centralInvolutions T) N
  let R := (H.subgroupOf N).map q
  let e := (subgroupOfEquivOfLe hHN).symm
  let f : H →* R := (q.subgroupMap (H.subgroupOf N)).comp e.toMonoidHom
  have hf : Function.Surjective f := (q.subgroupMap_surjective _).comp e.surjective
  have hker : f.ker = centralizer (U : Set H) := by
    ext g
    have he : f g = 1 ↔ q ⟨g,hHN g.property⟩ = 1 := by
      exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
    rw [MonoidHom.mem_ker,he]
    change (⟨g,hHN g.property⟩ : N) ∈ q.ker ↔ _
    rw [show q.ker = centralizer (V.subgroupOf N : Set N) from
      (QuotientGroup.ker_mk' _).trans (localActionKernel_eq_centralizer T hN.2)]
    constructor
    · intro hg v hv
      exact Subtype.ext (congrArg N.subtype (hg ⟨v,hHN v.property⟩ hv))
    · intro hg v hv
      exact Subtype.ext (congrArg H.subtype (hg ⟨v,hVH hv⟩ hv))
  by_cases hp : IsPGroup 2 R
  · let S := T.subtype hTH
    have hs : ((S.mapSurjective hf : Sylow 2 R) : Subgroup R) = ⊤ :=
      (Sylow.is_maximal' _ (hp.to_subgroup ⊤) le_top).symm
    intro g hg
    have hfg : f ⟨g,hg⟩ ∈ (S : Subgroup H).map f := by
      rw [← Sylow.coe_mapSurjective hf,hs]
      trivial
    obtain ⟨s,hsS,hsg⟩ := hfg
    have hc : (⟨g,hg⟩ : H) / s ∈ centralizer (U : Set H) := by
      rw [← hker]
      change f ((⟨g,hg⟩ : H) / s) = 1
      rw [map_div,hsg,div_self']
    have hcG : g / (s : G) ∈ N ⊓ centralizer (V : Set G) := by
      refine ⟨N.div_mem (hHN hg) (hN.2 hsS),?_⟩
      intro v hv
      exact congrArg H.subtype (hc ⟨v,hVH hv⟩ hv)
    have hsG : (s : G) ∈ N ⊓ M := ⟨hN.2 hsS,hM.1.2 hsS⟩
    have hm := ((N ⊓ M) ⊔ (N ⊓ centralizer (V : Set G))).mul_mem
      (mem_sup_right hcG) (mem_sup_left hsG)
    simpa only [div_mul_cancel] using hm
  · have hHM : H ≤ M := source_oddByTwo_minimalParabolic_le hG T hempty hM hJ
      hH hP U f hf hker (pResidual 2 R) hodd (isPGroup_quotient_pResidual 2) hp
    exact (le_inf hHN hHM).trans le_sup_left
end CFSG.Quasithin.Chapter15.Section01
