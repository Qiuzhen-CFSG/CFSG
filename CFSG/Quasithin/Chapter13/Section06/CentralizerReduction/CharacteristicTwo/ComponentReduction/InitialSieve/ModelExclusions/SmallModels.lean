module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelExclusions.QuotientAction
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.PSL3Three.SylowFixers
public import Theory.Mathieu.M11.Properties.ElementarySylowFixers

/-!
# Two concrete model exclusions from the central four-group

The faithful action on K/Z(K) produces four distinct pointwise fixers of
an actual Sylow two-subgroup. The concrete PSL₃(3) and M₁₁ calculations
bound this fixer by two, giving contradictions. The M₁₁ argument retains
the full component and uses Z(K)=O₂(K); it applies to central covers too.
The PSL₃(3) argument transports the arbitrary defining field to F₃.

These discharge the PSL₃(3) part of 1.1.5(3)(e) and the M₁₁ part of (f)
in the proof of 13.6.6. The other odd-linear and sporadic models remain
separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.501–503 and p.927; the intrinsic fixer calculations also
occur in E.6.8(5), printed p.248.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
open A5Module
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {T : Sylow 2 G}

/-- No component here has the M₁₁ model for its literal two-core quotient. -/
theorem not_m11_quotient (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M11) := by
  rintro ⟨e⟩
  obtain ⟨S, A, hA, hfix⟩ := exists_fixed_four_of_equiv K hK a
    ((componentImageEquivTwoCoreQuotient K hK hodd).trans e)
  let := hA
  let : IsElementaryAbelian 2 A := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := hA.exponent_two ▸ dvd_rfl }
  have hbound := Sporadic.Mathieu.m11_elementary_sylow_fixer_card_le_two S A hfix
  rw [hA.card_four] at hbound
  omega

/-- Exclude the PSL₃(3) part of source alternative (e). -/
theorem not_linear_three_three (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (a : ActionData s (T : Subgroup G) K) :
    ¬ ClassicalGroup.IsPSL K 3 3 := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = Fintype.card (ZMod 3) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF
  let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq hcard
  let eP : K ≃* Matrix.PSL3Three.PSL := e.trans (Atlas.fieldEquivPSL 3 eF)
  let eSL := eP.trans Matrix.PSL3Three.equiv.symm
  have hc : center K = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr eSL).toEquiv, Matrix.PSL3Three.center_eq_bot, card_bot]
  let eQ := (NormalizerAction.componentCentralQuotientEquiv K).symm.trans
    (((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans eP)
  obtain ⟨S, A, hA, hfix⟩ := exists_fixed_four_of_equiv K hK a eQ
  have hbound := Matrix.PSL3Three.SylowFixers.sylow_fixer_card_le_two S A hfix
  rw [hA.card_four] at hbound
  omega
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
