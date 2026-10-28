module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.Inputs
public import Mathlib.Algebra.Group.ConjFinite

/-!
# Concrete certificates for the absolute M₂₄ degree window

Together with the trivial module, four small simple modules and eight larger
simple modules exhaust the simples if the number of odd-order conjugacy
classes is at most thirteen. The two families are automatically disjoint by
dimension. Modular trace independence, rather than an assumed completeness
field, proves exhaustion in `AbsoluteSpectrum`.

These are independent unproved construction contracts on the actual
Witt-design carrier. The small family can use the existing Golay code and
cocode, and two degree-forty-four modules. The large family needs only the
strict lower bound forty-eight, not a complete dimension or character table.
Neither family is assumed to contain an arbitrary representation.

Sources: Guralnick–Malle, Classification of 2F-modules I, Proposition 5.1,
M₂₄ paragraph, manuscript p.17; G. D. James, The modular characters of the
Mathieu groups, J. Algebra 27 (1973), 57–111. The ATLAS of Finite Group
Representations, https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/, lists
candidate models but does not supply these Lean certificates.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
open Sporadic.Mathieu
universe v

/-- Four actual pairwise inequivalent small simple modules over each closed
field. This is an existence contract, with no completeness premise. -/
def SmallModelsExist : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ (d : Fin 4 → ℕ) (ρ : ∀ i, Representation F M24 (Fin (d i) → F)),
      (∀ i, IsIrreducible (ρ i)) ∧
      (Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) ∧
      ∀ i, d i = 11 ∨ d i = 44

/-- Eight actual pairwise inequivalent simple modules outside the required
window. Their exact larger dimensions are not part of the contract. -/
def LargeModelsExist : Prop :=
  ∀ (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2],
    ∃ (d : Fin 8 → ℕ) (ρ : ∀ i, Representation F M24 (Fin (d i) → F)),
      (∀ i, IsIrreducible (ρ i)) ∧
      (Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j))) ∧
      ∀ i, 48 < d i

/-- An upper bound for the literal odd-order conjugacy classes of native M₂₄.
No abstract group name or externally supplied character table is used. -/
def OddClassBound : Prop :=
  Nat.card (ConjClasses.mk '' {g : M24 | ¬ 2 ∣ orderOf g}) ≤ 13

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
