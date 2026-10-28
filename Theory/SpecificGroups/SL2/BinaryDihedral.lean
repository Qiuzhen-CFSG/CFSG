module

public import Theory.SpecificGroups.SL2.BinaryProjective
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic.FinCases

/-!
# Genuine binary rank-one models for the small-action sieve

The six explicit determinant-one matrices identify D₆ with SL₂(2).
Composing with the canonical central quotient gives the actual L₂(2)
model, and centerlessness transports from the odd dihedral group.
These comparisons supply the center hypothesis of `CoreAction` in the
cubic code exclusion, rather than assuming it along with the alternatives.

Source application: Aschbacher–Smith, Proposition 8.2.8(3–6), printed
pp.718–719 (PDF pp.735–736).
-/

public section
namespace Theory.SpecificGroups.BinaryDihedral
open Matrix

private def rotation (i : ZMod 3) : SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨if i = 0 then 1 else if i = 1 then !![0, 1; 1, 1] else !![1, 1; 1, 0], by
    fin_cases i <;> decide +kernel⟩
private def reflection (i : ZMod 3) : SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨if i = 0 then !![0, 1; 1, 0] else if i = 1 then !![1, 1; 0, 1] else !![1, 0; 1, 1], by
    fin_cases i <;> decide +kernel⟩
private def dihedralToSL : DihedralGroup 3 →* SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun x := match x with
    | .r i => rotation i
    | .sr i => reflection i
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

private noncomputable def dihedralEquivSL : DihedralGroup 3 ≃* SpecialLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective dihedralToSL (by decide +kernel)

/-- The six-matrix comparison followed by the canonical central quotient. -/
noncomputable def dihedralThreeEquivPSL2Two : DihedralGroup 3 ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  dihedralEquivSL.trans SpecialLinearGroup.sl2TwoEquivPSL2Two

/-- Odd dihedral model equivalences discharge the actual center condition. -/
theorem center_eq_bot_of_dihedral_model {Q : Type*} [Group Q] {m : ℕ}
    (e : Q ≃* DihedralGroup m) (hm : Odd m) (hne : m ≠ 1) :
    Subgroup.center Q = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have he : e x ∈ Subgroup.center (DihedralGroup m) := by
    apply Subgroup.mem_center_iff.mpr
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp hx z)
  rw [DihedralGroup.center_eq_bot_of_odd_ne_one hm hne] at he
  change x = 1
  exact (map_eq_one_iff e e.injective).mp (Subgroup.mem_bot.mp he)

/-- A genuine L₂(2) marking suffices for `CoreAction`'s centerlessness input. -/
theorem center_eq_bot_of_psl2Two_model {Q : Type*} [Group Q]
    (e : Q ≃* ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2)) :
    Subgroup.center Q = ⊥ :=
  center_eq_bot_of_dihedral_model (e.trans dihedralThreeEquivPSL2Two.symm)
    (by decide) (by decide)

end Theory.SpecificGroups.BinaryDihedral
