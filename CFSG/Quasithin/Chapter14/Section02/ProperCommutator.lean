module
public import CFSG.Quasithin.Chapter14.Section02.ProperComponent
public import CFSG.Quasithin.Chapter14.Section02.ProperCoreControl
public import CFSG.Quasithin.Chapter15.Section03.InitialSource.OddImage

/-!
# The original involution witness in the proper-index completion

The cubic residual image gives V=[V,Y] and hence V≤Y. Since Y is
2-perfect, it lies in the relative 2-residual of every containing subgroup
normalizing V. A nonidentity element of the original central line therefore
supplies the elementary commutator witness in 1.2.11. Together with the
proved Sylow and core-centralizer controls, this yields the genuine
quasisimple-or-characteristic-two dichotomy for the residual component.
The earlier selected-component placement and local-family inputs remain
explicit for their original source producers.

Source: Aschbacher--Smith 14.2.15, printed p.985, using 14.1.18 and 1.2.11.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.Section02
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original cubic residual generates the local plane by commutators. -/
theorem source_plane_module_residual_commutator
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3)) :
    localModule T M = ⁅localModule T M,sourceResidual M Mc⁆ ∧
      localModule T M ≤ sourceResidual M Mc := by
  let Y := sourceResidual M Mc
  have hYM : Y ≤ M := sourceResidual_le _ _
  have hMY : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal M Mc)
  let : (Y.subgroupOf M).Normal := residualY_normal M Mc
  let : (localActionImage (centralInvolutions T) M Y).Normal :=
    (inferInstance : (Y.subgroupOf M).Normal).map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨_,_,_,_,heY,_,huniq,_⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hc : Nat.card (localActionImage (centralInvolutions T) M Y) = 3 :=
    (Nat.card_congr heY.some.toEquiv).trans (Nat.card_zmod 3)
  have hescape : ¬Y ≤ Mc := by
    intro hYMc
    have hTMc : (T : Subgroup G) ≤ Mc := by
      intro t ht
      exact (InitialSource.centralizer_le_partner T hu)
        (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
    have hMcmax : IsMaximalTwoLocal Mc :=
      (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G))
        from hu ▸ Set.mem_singleton Mc).1
    have he : Mc = M := Set.mem_singleton_iff.mp (huniq ▸
      (show Mc ∈ maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G))
        from ⟨hMcmax,sup_le hYMc hTMc⟩))
    exact (plane_ordering_and_overgroups hG T hempty hM hu hmany hcard
      (plane_centralInvolutions_card T M hM.1.2 hcard e)).2.1 he.symm
  have hv := InitialSource.localModule_eq_commutator_of_odd_image hG T hM.1 hu hYM
    (by rw [normalizer_eq_top]; exact le_top) (by rw [hc]; decide) hescape
  refine ⟨hv,?_⟩
  rw [hv]
  exact le_normalizer_iff_commutator_le_right.mp
    ((conjugateSpanBy_le_self (fun z hz =>
      hM.1.2 ((mem_omegaOneCenterAmbient_iff _ z).mp hz).1)).trans hMY)

/-- The plane gives the literal relative-residual witness required by 1.2.11. -/
theorem source_plane_relative_residual_witness
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (X : Subgroup G) (hYX : sourceResidual M Mc ≤ X) {z : G}
    (hz : z ∈ centralInvolutions T) :
    ∃ A : Subgroup G, A ≤ X ∧ IsElementaryAbelian 2 A ∧
      z ∈ ⁅A,(pResidual 2 (X ⊓ normalizer (A : Set G) : Subgroup G)).map
        (X ⊓ normalizer (A : Set G)).subtype⁆ := by
  let V := localModule T M
  let Y := sourceResidual M Mc
  have hYM : Y ≤ M := sourceResidual_le _ _
  obtain ⟨hv,hVY⟩ := source_plane_module_residual_commutator hG T hempty hM hu hmany hcard e
  have hYN : Y ≤ X ⊓ normalizer (V : Set G) := le_inf hYX
    (hYM.trans (le_normalizer_conjugateSpanBy _ _))
  have hp : IsPPerfect 2 (Y.subgroupOf (X ⊓ normalizer (V : Set G))) :=
    (residualY_isPPerfect M Mc).of_surjective
      (subgroupOfEquivOfLe hYN).symm.toMonoidHom (subgroupOfEquivOfLe hYN).symm.surjective
  have hYR : Y ≤ (pResidual 2 (X ⊓ normalizer (V : Set G) : Subgroup G)).map
      (X ⊓ normalizer (V : Set G)).subtype := by
    simpa only [map_subgroupOf_eq_of_le hYN] using map_mono
      (f := (X ⊓ normalizer (V : Set G)).subtype) (le_pResidual_of_isPPerfect _ hp)
  refine ⟨V,hVY.trans hYX,InitialSource.localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩,?_⟩
  exact commutator_mono le_rfl hYR (hv ▸ (le_conjugateSpanBy _ _ hz))

/-- Original 1.2.11 applied to the canonical component in the proper completion. -/
theorem source_proper_completion_dichotomy
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (K S : Subgroup G) (hST : S ≤ (T : Subgroup G))
    (hi : S.relIndex (T : Subgroup G) = 2)
    (hN : normalizer (omegaOneCenterAmbient S : Set G) ≤ Mc)
    (hplacement : ∀ P : Sylow 2 Mc, S ≤ (P : Subgroup Mc).map Mc.subtype →
      maximalTwoLocalOvergroups (K ⊔ (P : Subgroup Mc).map Mc.subtype) = {Mc})
    (hK : K ∈ Chapter1.L G S) (hSN : S ≤ normalizer (K : Set G))
    (hZS : centralInvolutions T ≤ S)
    (hcore : pCore 2 (K ⊔ sourceResidual M Mc ⊔ S : Subgroup G) ≠ ⊥) :
    let X := K ⊔ sourceResidual M Mc ⊔ S
    let L := (solvableResidual X).map X.subtype
    IsQuasisimple L ∨ X ∈ Chapter1.He G := by
  let X := K ⊔ sourceResidual M Mc ⊔ S
  let L := (solvableResidual X).map X.subtype
  have hSX : S ≤ X := le_sup_right
  have hcorea : X.pCoreIn 2 ≠ ⊥ := fun hh =>
    hcore (((pCore 2 X).map_eq_bot_iff_of_injective X.subtype_injective).mp hh)
  have hs := source_proper_completion_sylow hG T hempty hM hu hmany hcard e H hH
    K S hST hi hN hplacement hcore
  obtain ⟨hTX,hCT⟩ := source_proper_completion_core_control hG T hempty hM hu hmany
    hcard e H hH K S hST hi hN hplacement hcore
  obtain ⟨hL,_,_⟩ := source_proper_completion_component hG T hempty hM hu hmany hcard e
    K S hST hK hSN hcorea hs
  have hLE : L.subgroupOf X = solvableResidual X := by
    exact comap_map_eq_self_of_injective X.subtype_injective _
  let : (L.subgroupOf X).Normal := by rw [hLE]; infer_instance
  let : Group.IsSolvable (X ⧸ L.subgroupOf X) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientMulEquivOfEq hLE.symm).toMonoidHom)
      (QuotientGroup.quotientMulEquivOfEq hLE.symm).surjective
  have hcZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hZne : centralInvolutions T ≠ ⊥ := by intro hh; rw [hh,card_bot] at hcZ; omega
  let : Nontrivial (centralInvolutions T) := (nontrivial_iff_ne_bot _).mpr hZne
  obtain ⟨z,hzne⟩ := exists_ne (1 : centralInvolutions T)
  have hz : orderOf (z : G) = 2 := orderOf_eq_prime
    ((mem_omegaOneCenterAmbient_iff _ _).mp z.property).2.1
    (fun hh => hzne (Subtype.ext hh))
  exact Chapter1.lemma_1_2_11_of_solvable_component_quotient hG T X L z hcorea
    (hTX.symm ▸ hs) hL hz ⟨hST (hZS z.property),hSX (hZS z.property)⟩
    ((mem_omegaOneCenterAmbient_iff _ _).mp z.property).2.2
    (source_plane_relative_residual_witness hG T hempty hM hu hmany hcard e X
      (le_sup_right.trans le_sup_left) z.property) (hCT.trans hTX.symm.le)
end CFSG.Quasithin.Chapter14.Section02
