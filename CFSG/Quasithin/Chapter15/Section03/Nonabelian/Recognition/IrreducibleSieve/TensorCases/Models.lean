module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Models
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.Models
public import Theory.Representation.SL2.BinarySmallModels

/-!
# Orthogonal and twisted tensor alternatives for the irreducible sieve

These are the literal model alternatives (7), (14)--(17) of G.9.3, independently
of the local hypotheses used in 15.3.58. In (14) only the component join is
identified with the tensor group, as required by the corrected source statement.
The minus and plus actions are actions of the actual quadratic-isometry groups.
The SL₃ tensor records its fixed half-field and the precise central kernel:
PSL₃(4) when the half-field exponent is one and SL₃(16) when it is two.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.9.3,
printed pp.353--357, and the proof of 15.3.58, printed p.1149.
-/

@[expose] public noncomputable section

open Representation
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases

open CFSG.Quasithin.ChapterG.Section09
open DefiningCharacteristic.LinearThreeRecognition

/-- The four-dimensional minus quadratic space over the indicated field. -/
abbrev MinusSpace (r : ℕ) := ClassicalOrthogonal.Minus.Space (GaloisField 2 r) 1

/-- The actual commutator group of the minus quadratic isometry group. -/
abbrev MinusGroup (r : ℕ) :=
  ClassicalOrthogonal.Minus.Omega (GaloisField 2 r) (MinusSpace r)
    (ClassicalOrthogonal.Minus.quadraticForm (GaloisField 2 r) 2)

/-- Scalar restriction of the defining minus orthogonal action. -/
def minusFour (r : ℕ) : Representation (ZMod 2) (MinusGroup r) (MinusSpace r) :=
  restrictScalars (ClassicalOrthogonal.subgroupNatural (MinusGroup r))

variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- Case (7) retains both the actual rank-one group and the literal minus
orthogonal action. No identification with a Hermitian model is inferred from
its dimension. -/
def MinusCase (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ Even n ∧
    Nonempty (K ≃* PSL(2, GaloisField 2 n)) ∧
    Quasiequivalent (ρ.comp K.subtype) (minusFour (n / 2)) ∧
    Module.finrank (ZMod 2) W = 2 * n ∧ n - 1 ≤ m

/-- Corrected case (14): the component action, including its degree and actor
rank, is the natural external tensor for PSL₃(2) × PSL₃(2). -/
def ProductCase (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop :=
  Quasiequivalent (ρ.comp K.subtype) TwoComponents.threeTensor ∧
    Module.finrank (ZMod 2) W = 9 ∧ m = 4

/-- Case (15) uses the actual split orthogonal module, not a product tag. -/
def PlusCase (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop :=
  ∃ n : ℕ, 1 < n ∧
    Quasiequivalent (ρ.comp K.subtype) (TwoComponents.fourOrthogonal n) ∧
    Module.finrank (ZMod 2) W = 4 * n ∧ 2 * n - 1 ≤ m

/-- Case (16), with the actual SL₂(8) coordinates and the specified scalar
extension. In characteristic two the SL₂ central kernel is trivial. -/
def TripleCase (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop :=
  ∃ e : K ≃* SL(2, GaloisField 2 3),
    Representation.SL2.BinarySmall.IsTriple
      ((ρ.comp K.subtype).comp e.symm.toMonoidHom) ∧
    Module.finrank (ZMod 2) W = 8 ∧ m = 3

/-- The matrix-entry field in case (17). -/
abbrev TensorField (n : ℕ) := GaloisField 2 (2 * n)

/-- The specified involutory Frobenius of the quadratic field extension. -/
def tensorConjugation (n : ℕ) : TensorField n ≃+* TensorField n :=
  iterateFrobeniusEquiv (TensorField n) 2 n

/-- The literal fixed half-field, not a second unrelated field of equal order. -/
def TensorHalfField (n : ℕ) : Subfield (TensorField n) :=
  FixedBy.subfield (TensorField n) (tensorConjugation n)

/-- The descended tensor action and its actual central quotient. The kernel
clauses distinguish PSL₃(4) from SL₃(16); an arbitrary central cover is not an
alternative. The scalar restriction is the given action on the original W. -/
def HalfFieldTensor (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (n : ℕ) : Prop :=
  ∃ π : SL(3, TensorField n) →* K, Function.Surjective π ∧
    ((n = 1 ∧ π.ker = Subgroup.center SL(3, TensorField n)) ∨
      (n = 2 ∧ π.ker = ⊥)) ∧
    ∃ scalar : Module (TensorHalfField n) W, letI := scalar
    letI : Algebra (ZMod 2) (TensorHalfField n) := ZMod.algebra (TensorHalfField n) 2
    letI : Module (ZMod 2) (TensorHalfField n) := Algebra.toModule
    ∃ τ : Representation (TensorHalfField n) K W,
      restrictScalars (k := ZMod 2) τ = ρ.comp K.subtype ∧
      Nonempty ((extendScalars (TensorField n) (τ.comp π)).Equiv
        (twistedTensor (TensorField n) (tensorConjugation n)))

/-- Case (17), including all source parameters and the genuine half-field
scalar-extension comparison. -/
def TwistedThreeCase (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ n ≤ 2 ∧ HalfFieldTensor ρ K n ∧
    Module.finrank (ZMod 2) W = 9 * n ∧ m = 4 * n

/-- Exactly the five orthogonal and twisted tensor alternatives allocated to
this sieve. This predicate has no dependency on `SourceData`. -/
inductive Alternative (ρ : Representation (ZMod 2) H W) (K : Subgroup H) (m : ℕ) : Prop
  | minus : MinusCase ρ K m → Alternative ρ K m
  | product : ProductCase ρ K m → Alternative ρ K m
  | plus : PlusCase ρ K m → Alternative ρ K m
  | triple : TripleCase ρ K m → Alternative ρ K m
  | twistedThree : TwistedThreeCase ρ K m → Alternative ρ K m

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.TensorCases
