module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder.Context
public import Mathlib.Data.ZMod.QuotientGroup

/-!
# Realizing the local coset certificate

The context uses exactly `localRelatorLetters`, so its relator loops hold by the
universal property of the literal seven-relator presentation. The defining tree
realizes all defining edges. Its only subgroup loop is positive `y`; the second
defining relator, `y⁹`, makes that cyclic subgroup finite of order at most nine.

Source: `../LocalPresentation.lean` and `../source/local_cover.json`.
-/

@[expose] public section

namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder

open Subgroup.CosetWordCertificate

theorem relator_holds (i : Fin 7) : eval localGenerator (localRelatorLetters i) = 1 := by
  have hh : FreeGroup.lift localGenerator = PresentedGroup.mk (Set.range localRelator) := by
    apply FreeGroup.ext_hom
    intro s
    exact FreeGroup.lift_apply_of
  change FreeGroup.lift localGenerator (localRelator i) = 1
  rw [hh]
  exact PresentedGroup.one_of_mem ⟨i, rfl⟩

theorem generator_pow_nine : localGenerator true ^ 9 = 1 := by
  simpa [localRelatorLetters, eval_cons, pow_succ', mul_assoc] using relator_holds 1

def cyclicSubgroup : Subgroup LocalPresented := Subgroup.zpowers (localGenerator true)

theorem cyclicSubgroup_finite_card_le :
    Finite cyclicSubgroup ∧ Nat.card cyclicSubgroup ≤ 9 := by
  have ho : IsOfFinOrder (localGenerator true) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨9, by decide, generator_pow_nine⟩
  refine ⟨ho.finite_zpowers.to_subtype, ?_⟩
  rw [cyclicSubgroup, Nat.card_zpowers]
  exact orderOf_le_of_pow_eq_one (by decide) generator_pow_nine

theorem context_valid :
    Valid context cyclicSubgroup localGenerator (definitions.repr localGenerator) := by
  apply definitions.valid
  · intro a ha
    simp only [decide_eq_true_eq] at ha
    subst a
    exact Subgroup.mem_zpowers (localGenerator true)
  · intro r
    dsimp [relatorWords]
    split
    · exact relator_holds _
    · exact eval_nil _

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalOrder
