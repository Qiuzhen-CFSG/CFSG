module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Permutation.Sections.Existence.FullActor
import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.MarkedElimination.AlternatingSevenDimension.Orders
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Selecting B.5.1 for an alternating offender actor

Simplicity excludes the two-factor alternative. The outer-six-three product
has order 1080, which divides neither 360 nor 2520. Consequently the complete
source alternative supplies B.5.1, whose nontrivial normal F* is the whole
alternating offender actor. This keeps the original module and all six source
clauses; it does not identify the offender with the full quotient.

Source: Aschbacher–Smith, B.5.6, printed p.105, used in the final proof
of 15.3.1, p.1155 (combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation

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


variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- An actual A₆ or A₇ offender actor selects the full-component B.5.1 case. -/
theorem source_of_alternating_offender {n : ℕ} (hn : n = 6 ∨ n = 7)
    (eN : d.offenderGroup ≃* alternatingGroup (Fin n))
    (h : SourceAlternative d.offenderAction) :
    ∃ _ : QuasisimpleSourceConclusion d.offenderAction (generalizedFitting d.offenderGroup),
      generalizedFitting d.offenderGroup = ⊤ := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simp; omega)
  let : IsSimpleGroup d.offenderGroup := eN.isSimpleGroup
  rcases remaining_source_cases d h with h | h
  · obtain ⟨hq, ⟨c⟩⟩ := h
    let := hq.simple
    let : Nontrivial (generalizedFitting d.offenderGroup) :=
      (QuotientGroup.mk'_surjective (center (generalizedFitting d.offenderGroup))).nontrivial
    exact ⟨c, (inferInstance : (generalizedFitting d.offenderGroup).Normal).eq_bot_or_eq_top.resolve_left
      ((Subgroup.nontrivial_iff_ne_bot _).mp inferInstance)⟩
  · rcases h with ⟨⟨c⟩⟩ | ⟨⟨c⟩⟩
    · let := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
        (c.firstCase.factorModel d.offenderAction)
      let := MarkedElimination.AlternatingSevenDimension.factor_nontrivial
        (c.secondCase.factorModel d.offenderAction)
      exact (not_simple_product c.product.equiv).elim
    · have hp : Nat.card (c.first ⊔ c.second : Subgroup d.offenderGroup) = 1080 := by
        rw [← Nat.card_congr c.product.toEquiv, Nat.card_prod,
          Nat.card_congr c.firstEquiv.toEquiv, Nat.card_congr c.secondEquiv.toEquiv,
          nat_card_alternatingGroup]
        norm_num [Nat.factorial, Nat.card_congr Multiplicative.toAdd]
      have hd := (c.first ⊔ c.second : Subgroup d.offenderGroup).card_subgroup_dvd_card
      rw [hp, Nat.card_congr eN.toEquiv, nat_card_alternatingGroup] at hd
      rcases hn with rfl | rfl <;> norm_num [Nat.factorial] at hd
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
