module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Sections
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.GroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The original terminal module has dimension four in the A₇ case

Simplicity, normality and nontriviality identify the offender-generated
subgroup with the full quotient. The product and outer alternatives of
B.5.6 are incompatible with A₇. In its quasisimple alternative the
component is the whole actor. The source commutator identity makes the
original module fully moved; B.5.1(2) then removes its central kernel,
and B.4.2(7) supplies dimension four.

The full FF classification witness remains an explicit premise. This is
its dimension consequence, for either labeling of the original local
configuration; it does not prove either universal classification theorem.

Source: Aschbacher–Smith, final proof of 15.3.1, printed p.1155/PDF p.1172;
B.4.2, p.86, B.5.1, pp.99–103, and B.5.6, pp.104–105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination
open ExceptionalAction.ActionRecognition AlternatingSevenDimension

private theorem not_simple_product {D A B : Type*} [Group D] [IsSimpleGroup D]
    [Group A] [Group B] [Nontrivial A] [Nontrivial B] (e : (A × B) ≃* D) : False := by
  let : IsSimpleGroup (A × B) := e.isSimpleGroup
  let f := MonoidHom.fst A B
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
  · obtain ⟨b, h⟩ := exists_ne (1 : B)
    have hm : (1, b) ∈ f.ker := rfl
    rw [hb] at hm
    exact h (congrArg Prod.snd hm)
  · obtain ⟨a, h⟩ := exists_ne (1 : A)
    have hm : (a, 1) ∈ f.ker := ht ▸ mem_top _
    exact h hm

private theorem not_two_factors {D W : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (c : SourceTwoFactorCase ρ) : False := by
  let := factor_nontrivial (c.firstCase.factorModel ρ)
  let := factor_nontrivial (c.secondCase.factorModel ρ)
  exact not_simple_product c.product.equiv

private theorem not_outer_six_three {D W : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    [AddCommGroup W] [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (hD : Nat.card D = 2520) (c : OuterSixThreeCase ρ) : False := by
  let := c.product_normal ρ
  have hc : Nat.card (c.first ⊔ c.second : Subgroup D) = 1080 := by
    rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
      Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd]
  rcases (inferInstance : (c.first ⊔ c.second : Subgroup D).Normal).eq_bot_or_eq_top with hb | ht
  · rw [hb] at hc
    norm_num at hc
  · rw [ht, Nat.card_congr Subgroup.topEquiv.toEquiv, hD] at hc
    norm_num at hc

private theorem fitting_eq_top {D : Type*} [Group D] [Finite D] [IsSimpleGroup D]
    (hq : IsQuasisimple (generalizedFitting D)) : generalizedFitting D = ⊤ := by
  let := hq.simple
  let : Nontrivial (generalizedFitting D) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting D))).nontrivial
  exact (inferInstance : (generalizedFitting D).Normal).eq_bot_or_eq_top.resolve_left
    ((Subgroup.nontrivial_iff_ne_bot _).mp inferInstance)

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- In the A₇ case the source offender actor is the full quotient, by
simplicity and its already proved normality and nontriviality. -/
theorem source_offenderGroup_eq_top_of_alternatingSeven
    (e : coreQuotient H ≃* alternatingGroup (Fin 7)) : d.offenderGroup = ⊤ := by
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (coreQuotient H) := e.isSimpleGroup
  exact d.offenderGroup_normal.eq_bot_or_eq_top.resolve_left d.offenderGroup_ne_bot

/-- The full conditional classification forces dimension four on V₀ itself,
with no irreducibility, splitting, fixed-space or actor equality assumed. -/
theorem source_alternatingSeven_dimension
    (e : coreQuotient H ≃* alternatingGroup (Fin 7))
    (classification : SourceAlternative d.offenderAction) :
    Module.finrank (ZMod 2) (Additive (moduleClosure V)) = 4 := by
  let eN : d.offenderGroup ≃* alternatingGroup (Fin 7) :=
    (MulEquiv.subgroupCongr (source_offenderGroup_eq_top_of_alternatingSeven d e)).trans
      (Subgroup.topEquiv.trans e)
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup d.offenderGroup := eN.isSimpleGroup
  have hc : Nat.card d.offenderGroup = 2520 :=
    (Nat.card_congr eN.toEquiv).trans alternating_card
  rcases OrdinaryExclusions.remaining_source_cases d classification with h | h
  · obtain ⟨hq, ⟨c⟩⟩ := h
    exact original_dimension d.offenderAction hc (fitting_eq_top hq)
      d.offenderAction_moved_eq_top c
  · rcases h with h | h
    · exact (not_two_factors d.offenderAction h.some).elim
    · exact (not_outer_six_three d.offenderAction hc h.some).elim

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.MarkedElimination
