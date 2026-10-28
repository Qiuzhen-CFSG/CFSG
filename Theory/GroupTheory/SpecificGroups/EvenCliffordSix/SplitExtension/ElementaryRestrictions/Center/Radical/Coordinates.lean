module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Reduction
import Mathlib.Tactic.FinCases

/-!
# Small coordinate certificates for radical centralizers

A nonconstant even six-vector has weight two or four. A permutation therefore
moves it to the first pair or its volume complement. An even involution
preserving that pair either fixes it pointwise, acting as one of the four
Klein-group permutations on the complement, or exchanges its two letters.
The latter case has signed correction one.

The certificates use the original permutations and binary vectors. A proved
five-coordinate equivalence enumerates the even vectors without repeatedly
constructing a filtered function space. The final homogeneous count is
8 + 8 + 4 + 4 = 24; no signs are counted at this stage. All finite checks are
performed by the kernel.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6a),
printed pp.410 and 412 (PDF pp.421 and 423), the split-extension calculation.
-/

@[expose] public section
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions.Radical
open Equiv

/-- The four even involutions on the complement of the first pair. -/
def pairActor (i : Fin 4) : Perm (Fin 6) :=
  ![1, swap 2 3 * swap 4 5, swap 2 4 * swap 3 5, swap 2 5 * swap 3 4] i

/-- Vector fibers retain the literal left-action mixed equation. -/
abbrev vectorFibers (i : Fin 4) (u : V) :=
  {q : Fin 4 × V // permuteVector (pairActor q.1) q.2 = q.2 ∧
    u + permuteVector (pairActor i) q.2 = q.2 + permuteVector (pairActor q.1) u}

/-- The only alternative to the four actors exchanges the first pair and
contributes a nonzero signed correction. -/
theorem pair_actor_cases (a : A) (ha : a ^ 2 = 1)
    (hv : permuteVector a.val Structure.leftA.vector = Structure.leftA.vector) :
    (∃ i : Fin 4, a.val = pairActor i) ∨
      (a.val 0 = 1 ∧ signedCorrection a.val Structure.leftA.vector = 1) := by
  have certificate : ∀ p : Perm (Fin 6), p ^ 2 = 1 →
      permuteVector p Structure.leftA.vector = Structure.leftA.vector →
      Perm.sign p = 1 →
      (∃ i : Fin 4, p = pairActor i) ∨
        (p 0 = 1 ∧ signedCorrection p Structure.leftA.vector = 1) := by
    decide +kernel
  exact certificate a.val (congrArg Subtype.val ha) hv (Perm.mem_alternatingGroup.mp a.property)

section VectorEnumeration

private abbrev Bits := F × F × F × F × F
private def fromBits (x : Bits) : V :=
  ⟨![x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2,
    x.1 + x.2.1 + x.2.2.1 + x.2.2.2.1 + x.2.2.2.2], by
    rw [BinaryPermutation.mem_core]
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    convert CharTwo.add_self_eq_zero
      (x.1 + x.2.1 + x.2.2.1 + x.2.2.2.1 + x.2.2.2.2) using 1; abel⟩
private def vectorEquiv : V ≃ Bits where
  toFun v := (v.val 0, v.val 1, v.val 2, v.val 3, v.val 4)
  invFun := fromBits
  left_inv v := by
    apply Subtype.ext
    funext i
    have hv : v.val 0 + v.val 1 + v.val 2 + v.val 3 + v.val 4 + v.val 5 = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc] using
        (BinaryPermutation.mem_core (Fin 6) v.val).mp v.property
    fin_cases i <;> try rfl
    exact CharTwo.add_eq_zero.mp hv
  right_inv v := rfl

private instance : Fintype V := Fintype.ofEquiv Bits vectorEquiv.symm

private def normalizers (i : Fin 15) : Perm (Fin 6) :=
  ![swap 1 1 * swap 0 0,
    swap 1 2 * swap 0 0,
    swap 1 3 * swap 0 0,
    swap 1 4 * swap 0 0,
    swap 1 5 * swap 0 0,
    swap 1 2 * swap 0 1,
    swap 1 3 * swap 0 1,
    swap 1 4 * swap 0 1,
    swap 1 5 * swap 0 1,
    swap 1 3 * swap 0 2,
    swap 1 4 * swap 0 2,
    swap 1 5 * swap 0 2,
    swap 1 4 * swap 0 3,
    swap 1 5 * swap 0 3,
    swap 1 5 * swap 0 4] i

/-- A nonconstant even vector becomes the first pair, up to volume complement. -/
theorem exists_normalization (v : V) (h0 : v ≠ 0) (hvol : v ≠ volumeVector) :
    ∃ p : Perm (Fin 6), permuteVector p v = Structure.leftA.vector ∨
      permuteVector p v = Structure.leftA.vector + volumeVector := by
  have certificate : ∀ v : V, v ≠ 0 → v ≠ volumeVector → ∃ i : Fin 15,
      permuteVector (normalizers i) v = Structure.leftA.vector ∨
        permuteVector (normalizers i) v = Structure.leftA.vector + volumeVector := by
    decide +kernel
  obtain ⟨i, hi⟩ := certificate v h0 hvol
  exact ⟨normalizers i, hi⟩

/-- The three nonidentity actors have exactly 24 homogeneous vector candidates. -/
theorem homogeneous_card (i : Fin 4) (hi : i ≠ 0) :
    Nat.card (vectorFibers i 0) = 24 := by
  have certificate : ∀ i : Fin 4, i ≠ 0 →
      ((Finset.univ : Finset (Fin 4 × V)).filter fun q =>
        permuteVector (pairActor q.1) q.2 = q.2 ∧
        (0 : V) + permuteVector (pairActor i) q.2 =
          q.2 + permuteVector (pairActor q.1) 0).card = 24 := by
    decide +kernel
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact certificate i hi

end VectorEnumeration
end EvenCliffordSix.SplitExtension.ElementaryRestrictions.Radical
