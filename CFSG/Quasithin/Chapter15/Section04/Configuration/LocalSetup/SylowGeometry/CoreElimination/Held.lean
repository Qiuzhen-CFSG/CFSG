module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.Held.Models

/-!
# Eliminating Held in the characteristic-two source branch

The actual single component satisfies every C.2.7 input. Its core quotient
is identified with its literal image in the starred local group using the
proved radical and kernel calculations. Every one of C.2.7's alternatives
then contradicts the retained Held model, including full SL₃ over every
binary field. All natural modules, marked parabolics and offender clauses
remain in the earlier universal theorem; none is replaced by a restricted
classifier.

Together with `ComponentElimination.source_held_characteristicTwo`, this
settles the extra Held alternative in both Fitting branches once the actual
contrary source context has been constructed. The universal C.2.7 remains
with its earlier source owner, and the adequate intrinsic embedding remains
with the final source assembly.
Source: Aschbacher--Smith, C.2.7 and 15.4.20, pp.145--147,1164.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
open BlockSieve BlockSieve.ExchangedCases BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- The retained Held component is impossible after actual characteristic-two
and source geometry have been constructed. The only classifier premise is
complete universal C.2.7, applied with all its original hypotheses. -/
theorem not_held_single_component (c27 : UniversalC27.{u})
    (hG : IsSimpleQTKE κ G) (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K))
    (e : Chapter1.XiQuotient K ≃* Held.He) : False := by
  have hKH : K ≤ H := h.closure ▸ EmbeddingReduction.normalClosureIn_le_overgroup _ _
  let eH := subgroupOfEquivOfLe hKH
  let eL : ((K.subgroupOf H) ⧸ pCore 2 (K.subgroupOf H)) ≃* Held.He :=
    (QuotientGroup.congr _ _ eH (pCore_map_iso 2 eH)).trans e
  let eStar := e.symm.trans (single_componentStarEquiv h hK)
  have halt (n : ℕ) (hn : n ≤ 8) (hb : ChapterC.IsAlternatingBlock (K.subgroupOf H) n) :
      False := by
    obtain ⟨f⟩ := hb.2.2.quotient_iso
    exact HeldModels.not_alternating hn ⟨eL.symm.trans f⟩
  have ha := (single_component_source_cases c27 hG h unique hK hq).2.2
  cases ha with
  | chi _ cases =>
    cases cases with
    | rankOne n hb _ _ =>
      obtain ⟨hn, _, F, hF, hfin, hcard, hm, _⟩ := hb
      exact HeldModels.not_even_rankOne hn (hm.of_mulEquiv eL.symm)
    | alternatingFive hb _ _ _ => exact halt 5 (by decide) hb
    | alternatingSevenDihedral hb _ _ => exact halt 7 (by decide) hb
    | alternatingSevenElementary hb _ _ _ => exact halt 7 (by decide) hb
  | alternating n _ hn hb _ => exact halt n hn hb
  | ahatSix hb _ _ =>
    have hc := Nat.card_congr (Subgroup.centerCongr eL).toEquiv
    rw [hb.2.2.1, Held.LocalPairs.center_eq_bot, card_bot] at hc
    omega
  | exceptionalSeven hb _ =>
    obtain ⟨f⟩ := hb.2.1
    exact HeldModels.not_alternating (by decide : 7 ≤ 8) ⟨eL.symm.trans f⟩
  | symplectic hb _ =>
    rcases hb with hb | hb
    · exact halt 6 (by decide) hb
    · obtain ⟨_, F, hF, hfin, hcard, ρ, ⟨m⟩, _⟩ := hb
      have hc : Nat.card Held.He = 979200 := by
        rw [Nat.card_congr (eL.symm.trans m.quotientIso).toEquiv,
          Theory.SpecificGroups.SymplecticFour.card_sp F, hcard]
        norm_num
      have hd := orderOf_dvd_natCard Held.b
      rw [Held.orderOf_b, hc] at hd
      norm_num at hd
  | gTwo hb _ =>
    obtain ⟨f⟩ := hb.quotient_iso
    have hc : Nat.card Held.He = 6048 := by
      rw [Nat.card_congr (eL.symm.trans f).toEquiv,
        Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
      exact Atlas.G2.BinaryException.card_H
    have hd := HeldModels.seventeen_dvd_card
    rw [hc] at hd
    norm_num at hd
  | linearThree branch =>
    obtain ⟨F, hF, hfin, n, hn, hcard, f, _⟩ := branch.2
    exact HeldModels.not_full_linearThree hn hcard ⟨eStar.trans f⟩
  | linearHigher n hn hm _ =>
    exact ComponentElimination.BinaryModels.sporadic_separation .he hn
      (by intro he; cases he) (hm.of_mulEquiv eStar)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
