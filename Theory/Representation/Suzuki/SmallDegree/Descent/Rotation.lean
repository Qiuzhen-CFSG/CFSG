module

public import Theory.Representation.Suzuki.SmallDegree.Models
public import Theory.Representation.EndFieldFrobenius
public import Mathlib.Data.Nat.Periodic
public import Mathlib.Algebra.Group.Fin.Basic

/-!
# Frobenius rotation of concrete Suzuki tensors

Entrywise squaring raises the natural trace to its square. Multiplicativity
of tensor traces therefore identifies coefficient Frobenius with translation
of the support in the cyclic group of order `2*m+1`. Under the independent
tensor-irreducibility hypothesis, equality of characters constructs an actual
intertwining equivalence. Summing the positions of a translation-invariant
support gives the divisibility used in binary field descent.

The calculation uses precisely the matrix actions and sorted tensor words in
`Models`; no classification or field-of-definition assertion is assumed.
Source: GLS3, Remark 2.8.8; Guralnick–Malle, *Classification of 2F-modules, II*,
§3.1 and Lemma 8.3.
-/

public noncomputable section
open scoped TensorProduct Fin.NatCast
namespace Representation.SuzukiSmallDegree
open BenderSuzuki.MatrixGroups SuzukiNatural

private theorem automorphism_pow_entry (m r : ℕ) (g : SuzukiMatrixGroup m) (i j : Fin 4) :
    ((suzukiFieldAutomorphism m ^ r) g).val.val i j = g.val.val i j ^ (2 ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ']
    change (suzukiFieldAutomorphism m ((suzukiFieldAutomorphism m ^ r) g)).val.val i j = _
    rw [suzukiFieldAutomorphism_entry, ih, ← pow_mul, ← pow_succ]

private theorem character_factor (m i : ℕ) (g : SuzukiMatrixGroup m) :
    (factorRep m i).character g = (naturalField m).character g ^ (2 ^ i) := by
  change LinearMap.trace (F m) (W m) _ = LinearMap.trace (F m) (W m) _ ^ _
  change LinearMap.trace (F m) (W m)
    (((suzukiFieldAutomorphism m ^ i) g).val.val.toLin') =
      LinearMap.trace (F m) (W m) (g.val.val.toLin') ^ _
  rw [Matrix.trace_toLin'_eq, Matrix.trace_toLin'_eq]
  simp only [Matrix.trace, Matrix.diag, automorphism_pow_entry]
  exact (sum_pow_char_pow 2 i _ _).symm

private theorem character_word (m : ℕ) (l : List ℕ) (g : SuzukiMatrixGroup m) :
    (wordRep m l).character g =
      (l.map (fun i => (naturalField m).character g ^ (2 ^ i))).prod := by
  induction l with
  | nil =>
    change LinearMap.trace (F m) (F m) 1 = 1
    simp
  | cons i l ih =>
    change ((factorRep m i).tprod (wordRep m l)).character g = _
    rw [char_tensor, Pi.mul_apply, character_factor, ih]
    rfl

/-- The trace of the literal tensor action is the product of its Frobenius factor traces. -/
theorem character_tensor (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K]
    (I : Support m) (g : SuzukiMatrixGroup m) :
    (tensorRep m K I).character g =
      ∏ i ∈ I, algebraMap (F m) K ((naturalField m).character g) ^ (2 ^ i.val) := by
  change LinearMap.trace K _ ((wordRep m (exponents I) g).baseChange K) = _
  rw [LinearMap.trace_baseChange]
  change algebraMap (F m) K ((wordRep m (exponents I)).character g) = _
  rw [character_word]
  simp only [exponents, List.map_map]
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.sort_eq]
  change algebraMap (F m) K (∏ i ∈ I, _) = _
  simp only [map_prod, Function.comp_apply, map_pow]

/-- Translate the selected ordinary Frobenius positions in the cyclic group of order `2*m+1`. -/
@[expose] def rotateSupport {m : ℕ} (r : ℕ) (I : Support m) : Support m :=
  I.image (fun i => i + (r : Fin (2 * m + 1)))

/-- Summing a support fixed by translation shows that the field exponent divides
its cardinality times the translation period. -/
theorem support_period_dvd_card_mul {m : ℕ} (r : ℕ) (I : Support m)
    (h : rotateSupport r I = I) : 2 * m + 1 ∣ I.card * r := by
  have hs := congrArg (fun J : Support m => ∑ i ∈ J, i) h
  rw [rotateSupport, Finset.sum_image] at hs
  · rw [Finset.sum_add_distrib, Finset.sum_const] at hs
    have hz : I.card • (r : Fin (2 * m + 1)) = 0 := add_eq_left.mp hs
    apply Fin.natCast_eq_zero.mp
    rw [← nsmul_one r, ← mul_smul, nsmul_one] at hz
    exact hz
  · intro a ha b hb hab
    exact add_right_cancel hab

private theorem frobenius_period (m : ℕ) (x : F m) :
    Function.Periodic (fun i : ℕ => x ^ (2 ^ i)) (2 * m + 1) := by
  intro i
  dsimp only
  rw [pow_add, mul_comm (2 ^ i), pow_mul]
  have hc : x ^ (2 ^ (2 * m + 1)) = x := by
    let : Fintype (F m) := Fintype.ofFinite _
    have he : Nat.card (F m) = 2 ^ (2 * m + 1) := GaloisField.card 2 _ (by omega)
    rw [← he, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card x
  rw [hc]

/-- Coefficient Frobenius rotates the character of the actual tensor action. -/
theorem character_tensor_rotate (m : ℕ) (K : Type*) [Field K] [Algebra (F m) K]
    (r : ℕ) (I : Support m) (g : SuzukiMatrixGroup m) :
    (tensorRep m K (rotateSupport r I)).character g =
      (tensorRep m K I).character g ^ (2 ^ r) := by
  rw [character_tensor, character_tensor, rotateSupport, Finset.prod_image]
  · rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i hi
    rw [← pow_mul, ← pow_add, ← map_pow, ← map_pow]
    congr 1
    have he : (i + (r : Fin (2 * m + 1))).val = (i.val + r) % (2 * m + 1) := by
      simp [Fin.val_add, Fin.val_natCast, Nat.add_mod_mod]
    rw [he]
    exact (frobenius_period m _).map_mod_nat _
  · intro a ha b hb hab
    exact add_right_cancel hab

/-- Under tensor irreducibility, coefficient Frobenius gives an actual equivalence
to the tensor on the rotated support. -/
theorem tensor_frobenius_equiv_rotate (m : ℕ) (K : Type*) [Field K]
    [Algebra (F m) K] [CharP K 2] [IsAlgClosed K]
    (hirr : ∀ J : Support m, (tensorRep m K J).IsIrreducible)
    (r : ℕ) (I : Support m) :
    Nonempty ((frobeniusConjugate 2 r (tensorRep m K I)).Equiv
      (tensorRep m K (rotateSupport r I))) := by
  let := hirr I
  let := hirr (rotateSupport r I)
  let := frobeniusConjugate_isIrreducible 2 r (tensorRep m K I)
  apply (character_eq_iff_equiv_of_irreducible _ _).mp
  funext g
  rw [character_frobeniusConjugate, character_tensor_rotate]

end Representation.SuzukiSmallDegree
