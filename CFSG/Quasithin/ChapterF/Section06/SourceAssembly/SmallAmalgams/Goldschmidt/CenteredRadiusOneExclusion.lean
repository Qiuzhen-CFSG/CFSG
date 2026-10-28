module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalResidual
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The centered radius-one local obstruction

The geometric part of the radius-one argument constructs a normal odd subgroup
of order three in the relevant vertex stabilizer. This file records the exact
residual consequence separately: once the local quotient is symmetric-three,
the normal cubic subgroup forces the odd-core branch, hence a cyclic cubic
p-residual. The raw label and fixed-ball construction remains with the
centered-interval producer.

Source: Goldschmidt (1980), (6.8), printed pp.399--400.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt

variable {H : Type*} [Group H] [Finite H]

/-- A nontrivial normal odd subgroup forces the cyclic-cubic branch of a
symmetric-three quotient. The subgroup may be the normal cubic subgroup
constructed from the three radius-two labels modulo the centered involution. -/
theorem residual_cyclic_three_of_normal_three
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3))
    (T : Subgroup H) [T.Normal]
    (hTcard : Nat.card T = 3)
    (hT : T ≤ pPrimeCore 2 H) :
    Nonempty ((pResidual 2 H) ≃* Multiplicative (ZMod 3)) := by
  have hTne : T ≠ ⊥ := by
    intro h
    have : Nat.card T = 1 := by simp [h]
    omega
  have hOddne : pPrimeCore 2 H ≠ ⊥ := by
    intro h
    exact hTne (bot_unique (h ▸ hT))
  have hfit : generalizedFitting H ≠ pCore 2 H := by
    intro h
    apply hOddne
    exact (SymmetricThreeTwoCore.characteristic_two_iff e).mp h
  have hcard : Nat.card (pResidual 2 H) = 3 := by
    rw [SymmetricThreeTwoCore.residual_eq_oddCore e hfit]
    exact SymmetricThreeTwoCore.oddCore_card_of_not_characteristic_two e hfit
  exact ⟨mulEquivOfPrimeCardEq hcard (by simp)⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
