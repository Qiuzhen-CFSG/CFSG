module

public import Theory.Representation.Suzuki.SmallDegree.Models
public import Theory.Representation.Suzuki.SmallDegree.Arithmetic
public import Theory.Representation.Suzuki.SmallDegree.Twists
public import Theory.Representation.ReeF4.BinaryDegree.SchurDescent

/-!
# The Suzuki small-degree tensor reduction

The concrete Frobenius tensor family and its binary automorphism intertwiners
are re-exported here. For an actual equivalence of the absolute Schur module
to a nonempty tensor support, the field-period divisibility and the strict
degree bound force that support to be a singleton.

This reduction is shared by the independent classification and descent
proofs. Their unconditional assembly is re-exported by `SmallDegree`.
Sources: Guralnick–Malle, *Classification of 2F-modules, II*, §3.1 and
Lemma 8.3; Aschbacher–Smith, reduction preceding K.3.5, printed p.457.
-/

public noncomputable section
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural FrobeniusTensor

variable {m : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m) V) [ρ.IsIrreducible]
  [Algebra (F m) (Closure ρ)]

/-- The true Schur dimension tower applied to a concrete Suzuki tensor. -/
theorem binary_finrank_of_tensor_equiv (I : Support m)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I)) :
    Module.finrank (ZMod 2) V =
      4 ^ I.card * Module.finrank (ZMod 2) (SchurField ρ) := by
  rw [binary_finrank_eq ρ, e.toLinearEquiv.finrank_eq, finrank_tensorSpace, Nat.mul_comm]

/-- The source degree bound excludes every support with two or more factors.
Only the field-period divisibility remains an independent descent premise. -/
theorem support_card_eq_one_of_smallDegree (I : Support m) (hI : I.Nonempty)
    (e : (absoluteRep ρ).Equiv (tensorRep m (Closure ρ) I))
    (hperiod : 2 * m + 1 ∣ I.card * Module.finrank (ZMod 2) (SchurField ρ))
    (hsmall : Module.finrank (ZMod 2) V < 10 * (2 * m + 1)) : I.card = 1 :=
  tensor_support_eq_one (Finset.card_pos.mpr hI) (schurField_finrank_pos ρ)
    hperiod (binary_finrank_of_tensor_equiv ρ I e) hsmall

end Representation.SuzukiSmallDegree
