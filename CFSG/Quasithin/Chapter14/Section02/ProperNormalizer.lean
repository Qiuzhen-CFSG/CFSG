module
public import CFSG.Quasithin.Chapter14.Section02.PairedCore
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Central omega control in the proper-index large amalgam

O₂(H)≤S and characteristic two put Ω₁Z(S) inside Ω₁Z(O₂(H)). The empty
faithful family makes the original residual centralize that subgroup.
The perfect supplement and the original Sylow show that the two-residual
and solvable residual agree, even though the selected supplement need not
be normal. As S has index two, H normalizes Ω₁Z(S); original 14.2.3 then
puts its entire ambient normalizer in Mc.

The exchanged-source consumer obtains O₂(H)≤S by lifting the normalizer
of the actual C-component through O₂(H). No refined component-placement
or new centralization input is needed for that branch.

Source: Aschbacher--Smith 14.2.15, displayed (!), printed p.985,
using 14.1.3 and 14.2.3 on the original H.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- If O₂(H) lies in the chosen index-two subgroup, the actual residual
centralizes its central omega subgroup. -/
theorem source_proper_omega_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup G) [Group.IsPerfect K]
    (hgen : K ⊔ (T : Subgroup G) = H)
    (hi : ((T : Subgroup G) ⊓ normalizer (K : Set G)).relIndex (T : Subgroup G) = 2)
    (hcore : H.pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K : Set G)) :
    let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
    (pResidual 2 H).map H.subtype ≤ centralizer (omegaOneCenterAmbient S : Set G) ∧
      normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc := by
  let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
  let ZS := omegaOneCenterAmbient S
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hSH : S ≤ H := hST.trans hH.1.1.2
  have hKH : K ≤ H := le_sup_left.trans_eq hgen
  have hchar := Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1
  have hZQ : ZS ≤ omegaOneCenterAmbient (H.pCoreIn 2) := by
    intro z hz
    obtain ⟨hzS,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff S z).mp hz
    have hzQ : z ∈ H.pCoreIn 2 := hchar ⟨hSH hzS,fun q hq => hzC q (hcore hq)⟩
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hzQ,hz2,fun q hq => hzC q (hcore hq)⟩
  have hres : (solvableResidual H).map H.subtype ≤ centralizer (ZS : Set G) := by
    rintro k ⟨a,ha,rfl⟩ z hz
    have hz' := hZQ hz
    change z ∈ omegaOneCenterAmbient ((pCore 2 H).map H.subtype) at hz'
    rw [omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective] at hz'
    obtain ⟨b,hb,rfl⟩ := hz'
    exact congrArg H.subtype ((InitialSource.residual_le_centralizer_omegaCore
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hH.1.1 ha) b hb)
  have he : pResidual 2 H = solvableResidual H := by
    let D := solvableResidual H
    let TH := T.subtype hH.1.1.2
    have hBD : K.subgroupOf H ≤ D := by
      let : Group.IsPerfect (K.subgroupOf H) := Group.IsPerfect.ofSurjective
        (f := (subgroupOfEquivOfLe hKH).symm.toMonoidHom)
        (subgroupOfEquivOfLe hKH).symm.surjective
      exact le_solvableResidual_of_isPerfect _
    have hg : K.subgroupOf H ⊔ (TH : Subgroup H) = ⊤ := by
      apply map_injective H.subtype_injective
      change (K.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H).map H.subtype = _
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,
        map_subgroupOf_eq_of_le hH.1.1.2,←MonoidHom.range_eq_map,range_subtype,hgen]
    have hsup : D ⊔ (TH : Subgroup H) = ⊤ := top_unique (hg ▸ sup_le_sup_right hBD _)
    have hp := isPGroup_quotient_of_sup_eq_top D (TH : Subgroup H) TH.isPGroup' hsup
    refine le_antisymm (sInf_le ⟨inferInstance,hp⟩) ?_
    let := (isPGroup_quotient_pResidual (G := H) 2) |>.isNilpotent
    exact solvableResidual_le_of_solvable_quotient _
  have hKR : K ≤ (solvableResidual H).map H.subtype :=
    le_map_solvableResidual_of_isPerfect K H hKH
  have hKC : K ≤ centralizer (ZS : Set G) := hKR.trans hres
  have hSn : (S.subgroupOf (T : Subgroup G)).Normal := normal_of_index_eq_two hi
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp hSn
  have hTZ : (T : Subgroup G) ≤ normalizer (ZS : Set G) := by
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj t).injective]
    exact congrArg omegaOneCenterAmbient (mem_normalizer_iff_map_conj_eq.mp (hTS ht))
  have hHN : H ≤ normalizer (ZS : Set G) := by
    rw [←hgen]
    exact sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _)) hTZ
  obtain ⟨huniq,hHZ⟩ := source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2
  have hZZ : centralInvolutions T ≤ ZS := by
    intro z hz
    obtain ⟨hzT,hz2,hzC⟩ := (mem_omegaOneCenterAmbient_iff (T : Subgroup G) z).mp hz
    have hzK : z ∈ centralizer (K : Set G) := fun k hk => (hHZ (hKH hk) z hz).symm
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨⟨hzT,Subgroup.centralizer_le_normalizer _ hzK⟩,hz2,fun s hs => hzC s (hST hs)⟩
  have hZne : ZS ≠ ⊥ := by
    intro hh
    have hbot : centralInvolutions T = ⊥ := le_bot_iff.mp (hh ▸ hZZ)
    have hc := plane_centralInvolutions_card T M hM.1.2 hcard e
    rw [hbot,card_bot] at hc
    omega
  refine ⟨he ▸ hres,?_⟩
  exact normalizer_le_of_unique_maximalTwoLocal
    (fun N hN hHN => Set.mem_singleton_iff.mp (huniq ▸
      (show N ∈ maximalTwoLocalOvergroups H from ⟨hN,hHN⟩)))
    (omegaOneCenterAmbient_elementaryAbelian S).isPGroup hZne hHN

/-- In the exchanged branch, C-component normalizer lifting provides the
core containment needed above on the literal original H. -/
theorem source_paired_omega_normalizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hgen : K ⊔ (T.subtype hH.1.1.2 : Subgroup H) = ⊤)
    (hi : ((T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G)).relIndex (T : Subgroup G) = 2) :
    let S := (T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G)
    (pResidual 2 H).map H.subtype ≤ centralizer (omegaOneCenterAmbient S : Set G) ∧
      normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc := by
  let := hK.perfect
  let : Group.IsPerfect (K.map H.subtype) :=
    Group.IsPerfect.ofSurjective (f := (K.equivMapOfInjective H.subtype H.subtype_injective).toMonoidHom)
      (K.equivMapOfInjective H.subtype H.subtype_injective).surjective
  have hg : K.map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (Subgroup.map H.subtype) hgen
    change (K ⊔ (T : Subgroup G).subgroupOf H).map H.subtype = (⊤ : Subgroup H).map H.subtype at hh
    simpa only [Subgroup.map_sup,map_subgroupOf_eq_of_le hH.1.1.2,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hcN : pCore 2 H ≤ normalizer (K : Set H) := by
    let := pCore_isPGroup (p := 2) (G := H) |>.isNilpotent
    rw [← normalizer_cComponent_quotient hK (pCore 2 H)]
    intro x hx
    change QuotientGroup.mk' (pCore 2 H) x ∈ normalizer (K.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H))
    rw [show QuotientGroup.mk' (pCore 2 H) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hcT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hH.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hc : H.pCoreIn 2 ≤ (T : Subgroup G) ⊓ normalizer (K.map H.subtype : Set G) :=
    le_inf hcT ((map_mono (f := H.subtype) hcN).trans (K.le_normalizer_map H.subtype))
  exact source_proper_omega_normalizer hG T hempty hM hu hmany hcard e H hH
    (K.map H.subtype) hg hi hc
end CFSG.Quasithin.Chapter14.Section02
