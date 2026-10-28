module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.Residual
public import CFSG.Quasithin.Chapter15.Section03.Constructions

/-!
# The distinguished local subgroup in source 14.1.6

Characteristic two places the original Z = Ω₁(Z(T)) inside Ω₁(Z(O₂(H)))
for every H in H(T). The empty faithful family and the component generation
result therefore put H∞ inside C_G(Z). Every local component is perfect and
lies in the residual of its actual join with T, so it also lies in C_G(Z).

The unique maximal two-local Mc over C_G(Z) then contains every local
component. The genuine 1.2.7 theorem identifies its C-components with the
maximal members of L(G,T), and gives Mc as the unique maximal two-local
overgroup of each actual component joined with T.

This proves all of 14.1.6, together with the reduced-module result imported
from Residual. Universal Theorems A and C remain genuine earlier inputs;
no local identification, natural-module marking, or source setup is assumed.
Source: Aschbacher–Smith 14.1.6, printed p.977, and the initial setup of
15.3.1 on pp.1120–1121.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Characteristic two places the actual central involutions in the local omega core. -/
theorem centralInvolutions_le_omegaCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {H : Subgroup G} (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    centralInvolutions T ≤ (omegaOneCenterAmbient (pCore 2 H)).map H.subtype := by
  rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
  change omegaOneCenterAmbient (T : Subgroup G) ≤ omegaOneCenterAmbient (H.pCoreIn 2)
  have hHe := Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH
  have hTH : (T : Subgroup G) ≤ H := hH.2
  have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  intro z hz
  obtain ⟨hzT, hzpow, hzcentral⟩ := (mem_omegaOneCenterAmbient_iff _ z).mp hz
  have hzC : z ∈ centralizer (H.pCoreIn 2 : Set G) :=
    fun q hq => hzcentral q (hQT hq)
  exact (mem_omegaOneCenterAmbient_iff _ z).mpr
    ⟨hHe ⟨hH.2 hzT, hzC⟩, hzpow, fun q hq => hzcentral q (hQT hq)⟩

omit [Finite G] in
/-- The singleton overgroup hypothesis supplies its literal centralizer containment. -/
theorem centralizer_le_partner (T : Sylow 2 G) {Mc : Subgroup G}
    (hMc : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    centralizer (centralInvolutions T : Set G) ≤ Mc :=
  (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
    hMc ▸ Set.mem_singleton Mc).2

variable
  (hA : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
  (hC : ∀ (X : Type u) [Group X] [Finite X],
    ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
  (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
  (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
include hA hC hG hempty

/-- Source 14.1.6(3), with H∞ embedded by the original inclusion H → G. -/
theorem residual_le_centralizer_Z {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    (solvableResidual H).map H.subtype ≤ centralizer (centralInvolutions T : Set G) := by
  rintro x ⟨a, ha, rfl⟩ z hz
  obtain ⟨b, hb, rfl⟩ := centralInvolutions_le_omegaCore hG T hH hz
  exact congrArg H.subtype
    ((residual_le_centralizer_omegaCore hA hC hG T hempty hH ha) b hb)

/-- Every local component centralizes the actual central involutions of T. -/
theorem local_component_le_centralizer_Z {L : Subgroup G}
    (hL : L ∈ Chapter1.L G (T : Subgroup G)) :
    L ≤ centralizer (centralInvolutions T : Set G) := by
  let := Chapter1.mem_L_isPerfect hL
  exact (le_map_solvableResidual_of_isPerfect L (L ⊔ (T : Subgroup G)) le_sup_left).trans
    (residual_le_centralizer_Z hA hC hG T hempty ⟨hL.2.2, show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right⟩)

/-- Source 14.1.6(3), including containment in the chosen Mc. -/
theorem residual_le_partner {Mc H : Subgroup G}
    (hMc : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hH : H ∈ Chapter1.HOver G (T : Set G)) :
    (solvableResidual H).map H.subtype ≤ Mc :=
  (residual_le_centralizer_Z hA hC hG T hempty hH).trans (centralizer_le_partner T hMc)

/-- Every actual local component lies in the distinguished maximal local subgroup. -/
theorem local_component_le_partner {Mc L : Subgroup G}
    (hMc : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : L ∈ Chapter1.L G (T : Subgroup G)) : L ≤ Mc :=
  (local_component_le_centralizer_Z hA hC hG T hempty hL).trans (centralizer_le_partner T hMc)

/-- Source 14.1.6(2): equality of the original maximal local family with C(Mc). -/
theorem maximal_local_components_eq {Mc : Subgroup G}
    (hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    Chapter1.LStar G (T : Subgroup G) = Chapter1.cComponentsIn Mc := by
  have hMcH : Mc ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal hMc.1.1, hMc.2⟩
  have hforward {L : Subgroup G} (hL : L ∈ Chapter1.LStar G (T : Subgroup G)) :
      L ∈ Chapter1.cComponentsIn Mc := by
    have hLMc := local_component_le_partner hA hC hG T hempty hunique hL.1
    exact ⟨hLMc, (nonsolvable_uniqueness_of_theoremsAC hA hC hG T hL).component Mc
      ⟨hMcH.1, sup_le hLMc hMc.2⟩⟩
  apply Set.Subset.antisymm (fun L hL => hforward hL)
  intro L hL
  have hlocal := (Chapter1.lemma_1_2_6 T hMcH).2 ((Chapter1.lemma_1_2_6 T hMcH).1 hL)
  obtain ⟨K, hK, hLK⟩ := Chapter1.exists_mem_LStar_ge hlocal
  have hKM := hforward hK
  have he : L.subgroupOf Mc = K.subgroupOf Mc :=
    hL.2.eq_of_le hKM.2 (comap_mono hLK)
  have hLK' : L = K := by
    simpa only [map_subgroupOf_eq_of_le hL.1, map_subgroupOf_eq_of_le hKM.1] using
      congrArg (map Mc.subtype) he
  exact hLK' ▸ hK

/-- Every original C-component of Mc determines that same unique maximal
two-local overgroup; the literal join with T is retained. -/
theorem component_unique_maximal_overgroup {Mc L : Subgroup G}
    (hMc : Mc ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hL : L ∈ Chapter1.cComponentsIn Mc) :
    maximalTwoLocalOvergroups (L ⊔ (T : Subgroup G)) = {Mc} := by
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) :=
    (maximal_local_components_eq hA hC hG T hempty hMc hunique).symm ▸ hL
  have hu := nonsolvable_uniqueness_of_theoremsAC hA hC hG T hstar
  have hMcN := hu.normalizer_unique Mc hMc.1 (sup_le hL.1 hMc.2)
  ext M
  constructor
  · intro hM
    exact Set.mem_singleton_iff.mpr ((hu.normalizer_unique M hM.1 hM.2).trans hMcN.symm)
  · rintro rfl
    exact ⟨hMc.1, sup_le hL.1 hMc.2⟩

end CFSG.Quasithin.Chapter15.Section03.InitialSource
