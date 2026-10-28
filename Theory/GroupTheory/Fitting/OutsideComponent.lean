module
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
/-!
# A component outside a subgroup containing the Fitting preimage

If M contains O₂,F(G) but misses O₂,F*(G), an ordinary component in G/O₂(G)
lies outside the image of M. The C-component lifting correspondence gives
a literal C-component L of G with quasisimple L/O₂(L), still outside M.
When G has characteristic two, subnormal inheritance supplies F*(L)=O₂(L).

This is the component extraction used after A.4.4 in Aschbacher–Smith
13.3.12, printed p.889. No quotient component, lift, or model is assumed.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem exists_cComponent_outside_of_fitting_preimage_le
    (M : Subgroup G) (hf : twoFittingCore G ≤ M)
    (hg : ¬ (generalizedFitting (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≤ M) :
    ∃ L : Subgroup G, L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧ ¬ L ≤ M := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hQM : pCore 2 G ≤ M := twoCore_le_twoFittingCore.trans hf
  have hfit : fittingSubgroup (G ⧸ pCore 2 G) ≤ M.map q := by
    have hh := map_mono (f := q) hf
    change ((fittingSubgroup (G ⧸ pCore 2 G)).comap q).map q ≤ _ at hh
    rwa [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _] at hh
  have hex : ∃ B : Subgroup (G ⧸ pCore 2 G),
      IsComponent (G ⧸ pCore 2 G) B ∧ ¬ B ≤ M.map q := by
    by_contra! hh
    have hle : generalizedFitting (G ⧸ pCore 2 G) ≤ M.map q :=
      sup_le hfit (sSup_le fun B hB => hh B hB)
    have hc := comap_mono (f := q) hle
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hQM] at hc
    exact hg hc
  obtain ⟨B,hB,hnot⟩ := hex
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  obtain ⟨L,hL,he⟩ := hB.isCComponent.exists_map_quotient_eq (pCore 2 G)
  have hqi : IsQuasisimple (L.map q) := he ▸ hB.2
  let := hqi
  exact ⟨L,hL,IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL).symm,
    fun hLM => hnot (he ▸ map_mono hLM)⟩

theorem exists_characteristicTwo_cComponent_outside
    (M : Subgroup G) (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hf : twoFittingCore G ≤ M)
    (hg : ¬ (generalizedFitting (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) ≤ M) :
    ∃ L : Subgroup G, L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧
      generalizedFitting L = pCore 2 L ∧ ¬ L ≤ M := by
  obtain ⟨L,hL,hq,hout⟩ := exists_cComponent_outside_of_fitting_preimage_le M hf hg
  exact ⟨L,hL,hq,generalizedFitting_eq_pCore_of_selfCentralizing 2
    (subnormal_core_selfCentralizing hc L hL.subnormal),hout⟩
end Theory.GroupTheory
