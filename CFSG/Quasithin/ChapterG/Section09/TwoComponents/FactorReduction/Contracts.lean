module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.TensorData
public import BenderSuzuki.MatrixGroups.Suzuki
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Remaining inputs to the G.9.3 factor reduction

These are theorem types and concrete model predicates, not proved source
results. The square-automorphism estimate is independent of quasithinness.
The Suzuki bound quantifies over every actual faithful irreducible binary
action of the matrix group. `LargeRankModel` records actual isomorphisms;
deriving it requires the central-cover restrictions and elimination of the
odd-field and sporadic cases, rather than a reading of A.1.34 as a theorem
about a centerless component.

Source: Aschbacher--Smith, G.9.3, printed p.356; A.1.34(3), printed pp.29--30.
-/

@[expose] public section

open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction

universe u v

/-- The group-theoretic estimate for a square of a centerless quasisimple
group. This definition alone supplies no witness. -/
def SquareAutomorphismRankTheorem : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [Theory.GroupTheory.IsQuasisimple S],
    Subgroup.center S = ⊥ → 0 < primeRank 2 (MulAut S) →
      primeRank 2 (MulAut (S × S)) ≤ 2 * primeRank 2 (MulAut S)

/-- The actual binary rank-one models remaining above component rank three.
The linear parameter is the rank of the given component, not a free label. -/
def LargeRankModel (S : Type u) [Group S] [Finite S] : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    Nat.card F = 2 ^ primeRank 2 S ∧ Nonempty (S ≃* SL(2,F))) ∨
  (∃ s : ℕ, 0 < s ∧ Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s))

/-- The lower bound supplied by defining-characteristic representation
classification for all faithful irreducible Suzuki actions. -/
def SuzukiBinaryDegreeTheorem : Prop :=
  ∀ (s : ℕ), 0 < s →
    ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W]
      (σ : Representation (ZMod 2) (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup s) W),
      Representation.IsIrreducible σ → Function.Injective σ →
        4 * (2 * s + 1) ≤ Module.finrank (ZMod 2) W

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction
