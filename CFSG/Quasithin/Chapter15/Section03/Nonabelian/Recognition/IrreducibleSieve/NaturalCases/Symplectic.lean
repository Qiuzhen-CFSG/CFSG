module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Defs
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.NaturalCases.Quadratic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.Representation.FirstCohomologySymplecticFour.LargeField

/-!
# Excluding the natural derived symplectic module

Over F₂ the degree is four and the source degree is at least six. Over larger
fields the literal matrix group is perfect; its natural action is transitive
on nonzero vectors, contradicting the source nonsingular quadratic form.
The exceptional derived-group convention is therefore retained throughout.

Source: Aschbacher--Smith, G.9.3(9) and 15.3.58, printed pp.354,1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

open Representation
open CFSG.Quasithin.ChapterG.Section09
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic
attribute [local instance] ZMod.algebra

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X : Subgroup H} {T : Sylow 2 H} {v : H} {s : ℕ}
  {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- G.9.3(9) is excluded at every field parameter, using the actual derived
matrix action even at its smallest field. -/
theorem SourceData.not_natural_symplecticFour (h : SourceData ρ X T v s)
    (K : Subgroup H) {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (hd : Module.finrank (ZMod 2) W = 4 * n) :
    ¬ Quasiequivalent (ρ.comp K.subtype) (SymplecticFourRecognition.binaryNatural F) := by
  have hn : 2 ≤ n := by have := h.six_le_degree; omega
  have hc : 2 < Nat.card F := by
    rw [hF]
    have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  apply h.not_nonzero_transitive_model K
  intro x y hx hy
  obtain ⟨g, hg⟩ := Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive hx hy
  refine ⟨⟨g, ?_⟩, hg⟩
  rw [OneCohomology.SymplecticFour.LargeField.commutator_eq_top hc]
  trivial

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
