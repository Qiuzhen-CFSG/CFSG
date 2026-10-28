module
public import Theory.SpecificGroups.SymplecticFour.Sylow
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.SymmetricSix.CoreFreeSylowOvergroups
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics

/-!
# The Borel core over every finite binary field

The standard Borel is proper. At field order greater than two, simplicity
of the center-free symplectic group makes its normal core trivial. At order
two, the actual polar equivalence with S6 and the proper-Sylow-overgroup
calculation give the same conclusion. Thus coefficient-field recognition
retains a trivial marked Borel core even at the binary endpoint.

Source: Aschbacher--Smith E.2.7--9, printed pp.219--222.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The literal Borel has trivial normal core, including over the binary field. -/
theorem borel_normalCore_eq_bot : (borel (F := F)).normalCore = ⊥ := by
  let := Fintype.ofFinite F
  obtain ⟨n, _, hn⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ (n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
  have hB : borel (F := F) ≠ ⊤ := by
    intro he
    have hle : borel (F := F) ≤ pointParabolic := inf_le_left
    rw [he] at hle
    exact pointParabolic_ne_top (top_unique hle)
  by_cases htwo : (n : ℕ) = 1
  · have hF2 : Nat.card F = 2 := by simpa [htwo] using hF
    let e : Sp F ≃* Equiv.Perm (Fin 6) :=
      (Binary.fieldEquivSp (Binary.fieldEquivZModTwo F hF2)).trans Binary.symmetricSixEquiv.symm
    exact Theory.SpecificGroups.SymmetricSix.normalCore_eq_bot_of_sylow_le e
      (unipotentSylow hF n.pos) borel unipotent_le_borel hB
  · have hq : 3 < Nat.card F := by
      rw [hF]
      exact lt_of_lt_of_le (by decide : 3 < 2 ^ 2)
        (Nat.pow_le_pow_right (by decide) (by have := n.pos; omega))
    let := SimpleQuotients.isSimpleGroup hq
    let : IsSimpleGroup (Sp F) := EvenProjective.equiv.isSimpleGroup
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (borel (F := F)).normalCore
      inferInstance with h | h
    · exact h
    · exact (hB (top_unique (h ▸ normalCore_le (borel (F := F))))).elim

end Theory.SpecificGroups.SymplecticFour
