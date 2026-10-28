module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.G2Parabolics
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2SylowFixers
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.SourceGeometry.Source

/-!
# The G₂ omega-center and literal residual centralizer

The faithful normalizer quotient acts on the original L. Its Sylow
omega-center fixes the component Sylow modulo Z(L), so the proved G₂
block fixer bound gives order at most two. The original central seed has
nontrivial image, giving equality. The already constructed pair of source
parabolics supplies literal O^{3′}(M ∩ L) escape; the source (**) argument
then identifies its S-centralizer with C_S(L).

This completes the G₂ constructor of ConstrainedAlternatives, preserving
both original primes, the actual marker and the exchanged-source consumer.
The latter uses the same original PreExclusionSource witness, as in the
ordinary-row consumers. Its centralizer obstruction now excludes this FF
row without an extra omega-center or residual-escape premise.

This internal continuation of SourceGeometry.Source uses the literal
componentPlusHom body only in its faithful-action proofs. Public boundaries
are unchanged. The stronger marked/opposite parabolic identities needed
by the full seven-row source statement, other small-block recognition,
general local-family Borel placement and catalogue exhaustiveness remain.
Original 15.1.14 retains its existing producer and final assembly owner.

Source: Aschbacher--Smith 15.1.22(**), (!), (2), printed pp.1098--1100;
15.1.20(2b), printed pp.1094--1095.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

private def plusAction (d : CaseIComponentData T M Mc V) : d.ComponentPlus →* MulAut d.L :=
  QuotientGroup.lift d.componentKernel
    (d.L.normalizerMonoidHom.comp (inclusion (show d.componentNormalizer ≤ normalizer (d.L : Set G) from inf_le_right)))
    (by
      intro x hx
      apply MulEquiv.ext
      intro y
      apply Subtype.ext
      change (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
      have hxy : (y : G) * (x : G) = (x : G) * (y : G) := hx y y.property
      rw [←hxy,mul_inv_cancel_right])

private theorem plusAction_injective (d : CaseIComponentData T M Mc V) :
    Function.Injective d.plusAction := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  ext x
  constructor
  · intro hx
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    change (x : G) * (y : G) * (x : G)⁻¹ = (y : G)
    have hxy : (y : G) * (x : G) = (x : G) * (y : G) := hx y y.property
    rw [←hxy,mul_inv_cancel_right]
  · intro hx
    change x.val ∈ centralizer (d.L : Set G)
    intro y hy
    have hh := congrArg (fun a : MulAut d.L => (a ⟨y,hy⟩ : G)) hx
    change (x : G)*y*(x : G)⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem plusAction_component (d : CaseIComponentData T M Mc V)
    (x : d.ComponentPlus) (y : d.L) :
    d.componentPlusHom (d.plusAction x y) = x * d.componentPlusHom y * x⁻¹ := by
  obtain ⟨n,rfl⟩ := QuotientGroup.mk'_surjective d.componentKernel x
  change d.plusMap _ = d.plusMap n * d.plusMap _ * (d.plusMap n)⁻¹
  rw [←map_inv,←map_mul,←map_mul]
  rfl

/-- The literal faithful normalizer omega-center is bounded by the G₂ natural fixed line. -/
theorem constrained_g2_plusOmega_bound (d : CaseIComponentData T M Mc V)
    (hb : ChapterC.IsG2TwoBlock d.L) (hs : Chapter1.IsSylowIn 2 d.SL d.L) :
    Nat.card d.plusOmega ≤ 2 := by
  obtain ⟨P,hP⟩ := hs
  let B := d.plusOmega.map d.plusAction
  have hB : ∀ a ∈ B, ∀ y ∈ P, a y * y⁻¹ ∈ center d.L := by
    rintro a ⟨x,hx,rfl⟩ y hy
    have hyS : (y : G) ∈ d.S := (hP ▸ mem_map_of_mem d.L.subtype hy).1
    have hyN : (y : G) ∈ d.sylowNormalizer := ⟨hyS,d.L.le_normalizer y.property⟩
    have hyplus : d.componentPlusHom y ∈ d.plus d.sylowNormalizer :=
      mem_map_of_mem d.plusMap hyN
    have hc := (mem_omegaOneCenterAmbient_iff _ _).mp hx |>.2.2
    have he : d.componentPlusHom (d.plusAction x y * y⁻¹) = 1 := by
      rw [map_mul,map_inv,d.plusAction_component,←hc _ hyplus,mul_inv_cancel_right,mul_inv_cancel]
    have hh : d.plusAction x y * y⁻¹ ∈ d.componentPlusHom.ker := he
    rwa [d.componentPlusHom_ker] at hh
  have hh := hb.central_sylow_fixers_card_le_two P B hB
  rwa [card_map_of_injective d.plusAction_injective] at hh

/-- The original central seed is nontrivial in that same omega-center, so its order is two. -/
theorem constrained_g2_plusOmega_card (d : CaseIComponentData T M Mc V)
    (h : PreparedChosenModule T M V) (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hb : ChapterC.IsG2TwoBlock d.L) (hs : Chapter1.IsSylowIn 2 d.SL d.L)
    (hn : d.S ≤ normalizer (d.L : Set G)) : Nat.card d.plusOmega = 2 := by
  have hZ1T := d.marked_le_sylow h hTM
  have hZS : centralInvolutions T ≤ d.S := fun z hz =>
    ⟨centralInvolutions_le_sylow T hz,
      centralizer_le hZ1T (centralInvolutions_le_centralizer_sylow T hz)⟩
  have hZne := d.central_seed_plus_ne_bot hu hZ1T (hZS.trans hn)
  have hne : d.plusOmega ≠ ⊥ := by
    intro he
    exact hZne (bot_unique (he ▸ d.central_seed_plus_le_omega hZ1T (hZS.trans hn)))
  have hlo := (one_lt_card_iff_ne_bot _).mpr hne
  have hhi := d.constrained_g2_plusOmega_bound hb hs
  omega

/-- The actual original G₂ row supplies the source centralizer identity and full G₂ alternative. -/
theorem PreExclusionSource.constrained_g2
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* DerivedModel) :
    Nat.card d.plusOmega = 2 ∧ ChapterC.IsG2TwoBlock d.L ∧
      d.ConstrainedCentralizerIdentity ∧ d.ConstrainedAlternatives := by
  have hb := s.constrained_g2_block (h := h) hG hempty hM hJ hu hf e
  obtain ⟨t,_,_,_,hout⟩ :=
    s.constrained_g2_parabolic_generation (h := h) hG hempty hM hJ hu hf e
  have hn := d.localFamily_g2_normalizes hG h
    ⟨d.L_component.1,s.local_component⟩ s.quasisimple t
  have hc := d.constrained_g2_plusOmega_card h hM.1.2 hu hb s.component_sylow hn
  have hcent : d.ConstrainedCentralizerIdentity :=
    s.source_residual_centralizer (h := h) hG hfull hM.1.2 hu hc hout
  exact ⟨hc,hb,hcent,.g2 hb hcent⟩

/-- Both later exchanged plane sizes retain the literal omega-center bound. -/
theorem ExchangedSource.constrained_g2_plusOmega_card
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V)
    (hf : generalizedFitting d.L = pCore 2 d.L)
    (e : d.normalizerImage d.L ≃* DerivedModel) : Nat.card d.plusOmega = 2 := by
  have hb := s.constrained_g2_block hG hempty hM hJ hu h hf e
  obtain ⟨t,_,_⟩ := s.constrained_g2_source_parabolics hG hempty hM hJ hu h hf e
  exact d.constrained_g2_plusOmega_card h hM.1.2 hu hb s.component_sylow
    (d.localFamily_g2_normalizes hG h ⟨d.L_component.1,s.local_component⟩ s.quasisimple t)

/-- The later exchanged-source obstruction now excludes the original G₂ FF row
on the same component and either original source prime. -/
theorem ExchangedSource.not_constrained_g2_of_preExclusion
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (x : d.ExchangedSource) (s : d.PreExclusionSource h.normalized p)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hfull : V = localModule T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hf : generalizedFitting d.L = pCore 2 d.L) :
    ¬ Nonempty (d.normalizerImage d.L ≃* DerivedModel) := by
  rintro ⟨e⟩
  obtain ⟨_,hb,hc,_⟩ := s.constrained_g2 (h := h) hG hempty hM hJ hfull hu hf e
  exact x.no_constrained_g2_centralizers hG hM.1.2 h hb hc

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open Atlas.G2.BinaryParabolicPair
variable {G : Type*} [Group G] [Finite G]

/-- The actual original marker supplies the G₂ centralizer and constrained
alternative, retaining its prime and the independent earlier residual premise. -/
theorem PreparedChosenModule.source_preExclusion_constrained_g2
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      (generalizedFitting d.L = pCore 2 d.L →
        Nonempty (d.normalizerImage d.L ≃* DerivedModel) →
        Nat.card d.plusOmega = 2 ∧ ChapterC.IsG2TwoBlock d.L ∧
          d.ConstrainedCentralizerIdentity ∧ d.ConstrainedAlternatives) := by
  obtain ⟨d,hZ,hr,s⟩ := h.component_of_preExclusionMarker
    hG T hempty hM hmany hJ hu hne hfull m hres
  exact ⟨d,hZ,hr,s,fun hf ⟨e⟩ =>
    s.constrained_g2 (h := h) hG hempty hM hJ hfull hu hf e⟩
end CFSG.Quasithin.Chapter15.Section01
