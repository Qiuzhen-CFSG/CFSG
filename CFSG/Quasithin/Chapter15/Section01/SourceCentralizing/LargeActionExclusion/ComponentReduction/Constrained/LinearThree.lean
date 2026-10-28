module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.LinearThree.Setup
public import Theory.GroupTheory.ConjugateOrbitIndexTwo

/-!
# The normalizer contradiction for the binary SL3 block

The source residual identification makes S normalize L and hence U(L).
The two-coset calculation makes T normalize `U(L) ∨ U(L)^t`. Both factors
lie in T, and U(L) is nontrivial. If the second factor centralizes L,
their join is also L-invariant. Source 14.1.6(3) then places the perfect
selected component in Mc, contradicting its choice.

This proves the terminal implication in 15.1.24(2). The moving-section
calculation and conjugate cubic-action argument must still supply the
residual identity and conjugate-core centralization. They are explicit
premises below, not assertions of the full L3(2)-block exclusion.

Source: Aschbacher--Smith 15.1.24(2), printed p.1101, and 14.1.6(3), p.977.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The literal normalizer argument at the end of source 15.1.24(2).
The two geometric premises remain local obligations of the constrained
recognition owner; this is not the complete block exclusion. -/
theorem ExchangedSource.false_of_constrained_l3_commuting_layers
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (a : d.ConstrainedL3Alternative)
    (hSnL : d.S ≤ normalizer (d.L : Set G))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hc : d.linearThreeU.map (MulAut.conj t).toMonoidHom ≤ centralizer (d.L : Set G)) :
    False := by
  let U := d.linearThreeU
  have hU0 : U ≠ ⊥ := by
    exact fun he => a.block.2.1.blockU_ne_bot
      (((blockU d.L).map_eq_bot_iff_of_injective d.L.subtype_injective).mp he)
  have hUS : U ≤ d.S := by
    obtain ⟨P,hP⟩ := s.component_sylow
    have hcore : d.L.pCoreIn 2 ≤ d.SL := hP ▸ pCoreIn_le_sylow d.L P
    exact ((map_mono blockU_le_core).trans hcore).trans d.SL_le_S
  have hnU : normalizer (d.L : Set G) ≤ normalizer (U : Set G) :=
    normalizer_le_normalizer_characteristic_image d.L (blockU d.L)
  let W := U ⊔ U.map (MulAut.conj t).toMonoidHom
  have hWT : W ≤ (T : Subgroup G) := by
    apply sup_le (hUS.trans d.S_le_T)
    have hmap := map_mono (f := (MulAut.conj t).toMonoidHom) (hUS.trans d.S_le_T)
    have he : (T : Subgroup G).map (MulAut.conj t).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp ((T : Subgroup G).le_normalizer ht)
    exact hmap.trans he.le
  have hW0 : W ≠ ⊥ := fun he => hU0 (bot_unique (he ▸ (show U ≤ W from le_sup_left)))
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    have he := componentOrbit_eq_sup_of_index_two U (T : Subgroup G) d.S s.index
      (inf_le_right.trans (hSnL.trans hnU)) ht htS
    change (T : Subgroup G) ≤ normalizer ((U ⊔ U.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)
    rw [← he]
    exact le_normalizer_componentOrbit U (T : Subgroup G)
  have hLW : d.L ≤ normalizer (W : Set G) :=
    (le_inf (d.L.le_normalizer.trans hnU)
      ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup U _)
  let N := normalizer (W : Set G)
  have hN : N ∈ Chapter1.HOver G (T : Set G) :=
    ⟨Chapter1.mem_H_of_isTwoLocal ⟨W,hW0,T.isPGroup'.to_le hWT,rfl⟩,hTW⟩
  let := Chapter1.mem_L_isPerfect s.local_component
  exact d.L_not_le_Mc ((le_map_solvableResidual_of_isPerfect d.L N hLW).trans
    (residual_le_partner (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hG T hempty hu hN))

/-- The source residual identity supplies the normalization used by the terminal
contradiction. The conjugate-layer centralization is still a local obligation. -/
theorem ExchangedSource.false_of_constrained_l3_residual_geometry
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (a : d.ConstrainedL3Alternative)
    (hres : d.L = (primeToResidual 3 (centralizer (d.nineFixedPlane : Set G))).map
      (centralizer (d.nineFixedPlane : Set G)).subtype)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htS : t ∉ d.S)
    (hc : d.linearThreeU.map (MulAut.conj t).toMonoidHom ≤ centralizer (d.L : Set G)) :
    False := by
  have hSnL : d.S ≤ normalizer (d.L : Set G) := by
    conv_rhs => rw [hres]
    exact (s.fixes_planes.1.trans (normalizer_le_normalizer_centralizer _)).trans
      (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _))
  exact s.false_of_constrained_l3_commuting_layers hG hempty hu a hSnL ht htS hc

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
