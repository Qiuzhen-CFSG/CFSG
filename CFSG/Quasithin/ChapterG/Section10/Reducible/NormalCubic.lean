module
public import CFSG.Quasithin.ChapterG.Section10.Reducible.PairAction
public import Theory.GroupTheory.SymmetricThreePairCubic

/-!
# A normal cubic in the reducible G.10 action

The proper irreducible plane and its quotient give a faithful action in
S₃×S₃. Orbit generation makes the group nontrivial, and the trivial two-core
then gives a normal subgroup of order three. This is the precise reducible
input used in the original 14.3.15 contradiction.

Source: Aschbacher--Smith G.10.4--5 and 14.3.15, printed pp.359,994.
-/

public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- Every original reducible action has a normal cubic subgroup. -/
theorem normal_cubic_of_reducible (hred : ¬ Representation.IsIrreducible ρ) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  let : Nontrivial G := h.nontrivial_of_reducible hred
  obtain ⟨f,hf⟩ := h.reducible_symmetricThree_pair hred
  exact Theory.GroupTheory.SymmetricThreePair.exists_normal_cubic_of_injective
    f hf h.twoCore_eq_bot

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
