module

public import Theory.SpecificGroups.SymmetricSix.Parabolics
public import Theory.Representation.FactorDegreeFiltration
public import Theory.Representation.BinaryPrimeDegree
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The binary flag module for A₆

The cosets of the explicit order-eight Borel form a transitive action on
45 points. The Borel is a two-group, so every irreducible binary module
is a quotient of this permutation module. A checked composition series
with simple factor degrees 1, 4 and 16 would therefore exclude degree eight
over F₂. Constructing that series remains a separate obligation.

An order-five subgroup forces degree at least four in every faithful
binary representation. Together these facts turn the proposed filtration
into a degree-four conclusion; they do not identify an arbitrary module
from its dimension.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3(9),
printed pp.354,356--357, and the six-letter quadrangle in I.5, pp.419--422.
The coefficient field throughout this module is literally `ZMod 2`.
-/

@[expose] public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation Representation
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter

/-- Flags as actual left cosets of the alternating Borel. -/
abbrev Flag := A6 ⧸ a6Borel

noncomputable instance : Fintype Flag := Fintype.ofFinite Flag

/-- The left action of A₆ on its Borel cosets. -/
noncomputable def flagAction : A6 →* Equiv.Perm Flag := MulAction.toPermHom A6 Flag

/-- The 45-dimensional binary permutation representation. -/
noncomputable def flagRepresentation : Representation (ZMod 2) A6 (Full Flag) :=
  (representation Flag).comp flagAction

/-- The Borel has index 45. -/
theorem flag_card : Nat.card Flag = 45 := a6Borel_index

/-- The stabilizer is the given subgroup, not just an isomorphic two-group. -/
theorem flag_stabilizer (g : A6) :
    g ∈ a6Borel ↔ flagAction g ((1 : A6) : Flag) = ((1 : A6) : Flag) := by
  change g ∈ a6Borel ↔ ((g * 1 : A6) : Flag) = ((1 : A6) : Flag)
  simp [QuotientGroup.eq]

/-- The actual coset action is transitive. -/
theorem flag_transitive (x : Flag) : ∃ g : A6, flagAction g ((1 : A6) : Flag) = x := by
  change ∃ g : A6, g • ((1 : A6) : Flag) = x
  exact MulAction.exists_smul_eq A6 _ x

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every irreducible binary module is an equivariant quotient of the flag module. -/
theorem flag_surjects (ρ : Representation (ZMod 2) A6 V) [ρ.IsIrreducible] :
    ∃ f : flagRepresentation.IntertwiningMap ρ, Function.Surjective f := by
  exact BinaryLinearThree.IrreducibleCatalogue.irreducible_permutation_quotient
    flagAction ((1 : A6) : Flag) a6Borel a6BorelSylow.isPGroup'
    flag_stabilizer flag_transitive ρ

/-- The order-five obstruction supplies an unconditional lower bound. -/
theorem degree_ge_four (ρ : Representation (ZMod 2) A6 V)
    (hρ : Function.Injective ρ) : 4 ≤ Module.finrank (ZMod 2) V := by
  have hd := Representation.BinaryPrimeDegree.orderOf_le_finrank ρ hρ
    (p := 5) (by decide) (by decide) (by rw [a6_order]; decide)
  rwa [Representation.BinaryPrimeDegree.orderOf_two_mod_five] at hd

/-- A literal filtration over F₂ excludes every degree between five and eight.
The filtration witness, including simplicity of its 16-dimensional factors,
is still required. -/
theorem degree_eq_four_of_filtration
    (hfiltration : FactorDegreeFiltration {d : ℕ | d = 1 ∨ d = 4 ∨ d = 16} flagRepresentation)
    (ρ : Representation (ZMod 2) A6 V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 8) :
    Module.finrank (ZMod 2) V = 4 := by
  have hdeg := BinaryPermutation.finrank_mem_of_factorDegreeFiltration
    flagAction ((1 : A6) : Flag) a6Borel a6BorelSylow.isPGroup'
    flag_stabilizer flag_transitive hfiltration ρ
  have hlo := degree_ge_four ρ hρ
  change Module.finrank (ZMod 2) V = 1 ∨ Module.finrank (ZMod 2) V = 4 ∨
    Module.finrank (ZMod 2) V = 16 at hdeg
  omega

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.SmallParameter
