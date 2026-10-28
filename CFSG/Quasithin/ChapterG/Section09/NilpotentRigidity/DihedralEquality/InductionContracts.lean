module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts

/-!
# The remaining equality-induction interfaces

The induction runs over the number of dihedral factors, allowing arbitrary
finite index types so that the two subproducts in the source proof require
no change of coordinates. Its conclusion always concerns the actual whole
product acting on the given module; the embedding transport is separate.

The centralizer obligation ensures that a commuting involution fixes each
already classified summand. This is needed to prove that the complementary
actors fix the other spaces before gluing their inclusion-preserving
coordinates. Neither interface is asserted here as a source theorem.

Source: Aschbacher--Smith G.9.2, printed pp.352--353.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

universe u v

/-- Classification at a specified number of factors, uniformly over the
module and over finite index types. Strictly smaller instances are the
induction hypotheses, not assumptions on the representation being classified. -/
def EqualityAt (r : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = r →
    ∀ (p : ι → ℕ), (∀ i, (p i).Prime) → (∀ i, Odd (p i)) →
      ∀ (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
        [FiniteDimensional (ZMod 2) W],
        ∀ σ : Representation (ZMod 2) (∀ i, DihedralGroup (p i)) W,
          Function.Injective σ →
            ((∀ i, p i = 3) → Module.finrank (ZMod 2) W ≤ 2 * r →
              Nonempty (ClassifiedDecomposition σ ⊤ False)) ∧
            ((∃ i, p i = 5) → Module.finrank (ZMod 2) W ≤ 2 * (r + 1) →
              Nonempty (ClassifiedDecomposition σ ⊤ True))

/-- The positive-rank induction step. Its producer must construct the
actual factors and space coordinates from strictly smaller classifications. -/
def PositiveEqualityStep : Prop :=
  ∀ r, 0 < r → (∀ s, s < r → EqualityAt.{v} s) → EqualityAt.{v} r

/-- A commuting involution is trivial on a faithful classified action.
This is a separate small-module centralizer theorem, not a consequence
encoded in the definition of `ClassifiedDecomposition`. -/
def ClassifiedInvolutionCentralizerTheorem : Prop :=
  ∀ (G : Type u) [Group G] (W : Type v) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W],
    ∀ (σ : Representation (ZMod 2) G W) (H : Subgroup G) (exceptional : Prop),
      ClassifiedDecomposition σ H exceptional →
      Function.Injective (σ.comp H.subtype) →
      ∀ t : Module.End (ZMod 2) W, t * t = 1 →
        (∀ g : H, Commute t (σ g)) → t = 1

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
