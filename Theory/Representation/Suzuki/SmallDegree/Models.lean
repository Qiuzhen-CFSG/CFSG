module

public import Theory.Representation.Suzuki.NaturalMatrix
public import Theory.SpecificGroups.Suzuki.FieldAutomorphism
public import Theory.Representation.ExtendScalars
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Sort

/-!
# Concrete natural Frobenius tensors for Suzuki groups

A parameter is a subset of the `2*m+1` ordinary Frobenius positions. At each
selected position the factor is the actual four-dimensional matrix action,
pulled back along the corresponding power of entrywise squaring. Tensor
products are formed over the defining field, then scalars are extended.
Their dimensions are exactly `4^|I|`. This constructs the candidate family;
it does not assert its irreducibility, distinctness or exhaustion.

The usual exceptional-Frobenius parametrization can be reindexed by ordinary
Frobenius because `2*m+1` is odd. Sources: GLS3, 2.8.6(b), 2.8.8;
Guralnick–Malle, *Classification of 2F-modules, II*, §3.1 and Lemma 8.3.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

/-- The natural action before restriction to the binary field. -/
def naturalField (m : ℕ) : Representation (F m) (SuzukiMatrixGroup m) (W m) :=
  (generalLinearNatural 4).comp (SuzukiMatrixSubgroup m).subtype

/-- The natural factor at the indicated ordinary Frobenius position. -/
def factorRep (m i : ℕ) : Representation (F m) (SuzukiMatrixGroup m) (W m) :=
  (naturalField m).comp (suzukiFieldAutomorphism m ^ i).toMonoidHom

/-- Tensor carrier for a list of nontrivial Frobenius factors. -/
def WordModule (m : ℕ) : List ℕ → ModuleCat (F m)
  | [] => ModuleCat.of (F m) (F m)
  | _ :: l => ModuleCat.of (F m) (W m ⊗[F m] WordModule m l)

abbrev WordSpace (m : ℕ) (l : List ℕ) := WordModule m l

instance wordSpaceFiniteDimensional (m : ℕ) (l : List ℕ) :
    FiniteDimensional (F m) (WordSpace m l) := by
  induction l with
  | nil => change FiniteDimensional (F m) (F m); infer_instance
  | cons i l ih =>
    change FiniteDimensional (F m) (W m ⊗[F m] WordSpace m l)
    infer_instance

/-- Iterated tensor of the literal Frobenius matrix actions. -/
def wordRep (m : ℕ) : (l : List ℕ) →
    Representation (F m) (SuzukiMatrixGroup m) (WordSpace m l)
  | [] => Representation.trivial (F m) (SuzukiMatrixGroup m) (F m)
  | i :: l => (factorRep m i).tprod (wordRep m l)

@[simp] theorem finrank_wordSpace (m : ℕ) (l : List ℕ) :
    Module.finrank (F m) (WordSpace m l) = 4 ^ l.length := by
  induction l with
  | nil => exact Module.finrank_self (F m)
  | cons i l ih =>
    change Module.finrank (F m) (W m ⊗[F m] WordSpace m l) = _
    rw [Module.finrank_tensorProduct, ih]
    simp [W, pow_succ, Nat.mul_comm]

/-- Tensor parameters use each Frobenius position at most once. -/
abbrev Support (m : ℕ) := Finset (Fin (2 * m + 1))

/-- Increasing list of the selected ordinary Frobenius exponents. -/
def exponents {m : ℕ} (I : Support m) : List ℕ := (I.sort (· ≤ ·)).map Fin.val

/-- There are precisely `2^(2*m+1)` candidate parameters. -/
theorem support_card (m : ℕ) : Nat.card (Support m) = 2 ^ (2 * m + 1) := by
  simp [Support, Nat.card_eq_fintype_card]

variable (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K]

abbrev TensorSpace (I : Support m) := K ⊗[F m] WordSpace m (exponents I)

/-- A concrete tensor on the actual Suzuki matrix group. -/
def tensorRep (I : Support m) :
    Representation K (SuzukiMatrixGroup m) (TensorSpace m K I) :=
  extendScalars K (wordRep m (exponents I))

@[simp] theorem finrank_tensorSpace (I : Support m) :
    Module.finrank K (TensorSpace m K I) = 4 ^ I.card := by
  rw [Module.finrank_baseChange, finrank_wordSpace]
  simp [exponents]

/-- An actual intertwiner removes the tensor unit in a singleton support. -/
def singletonFieldEquiv (i : ℕ) : (wordRep m [i]).Equiv (factorRep m i) :=
  Representation.TensorProduct.rid (F m) (factorRep m i)

end Representation.SuzukiSmallDegree
