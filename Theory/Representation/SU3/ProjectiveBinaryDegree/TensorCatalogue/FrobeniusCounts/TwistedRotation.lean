module

public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.FrobeniusCounts.HermitianDual
public import Theory.Representation.EndFieldFrobenius

/-!
# Twisted word rotation and coefficient Frobenius

Left rotation of a tensor word exchanges natural and dual at the boundary.
The Hermitian Gram identity proves that this operation cancels one coefficient
Frobenius on characters. Iteration, irreducibility, and separation of the unitary
word catalogue identify the Frobenius stabilizer with the ordinary rotation
stabilizer of `w ++ dualWord w`.

The catalogue assertions are explicit hypotheses here. `FrobeniusCounts`
compares this stabilizer with the exact period of the actual binary Schur model.
Source: GLS III, Remark 2.8.8; Guralnick--Malle, §3.1, internal p.12.
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/FrobeniusCounts/TwistedRotation.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

public section
namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
open Representation.SL3.BinaryDefiningFactors
/-- Left shift with the A₂ graph involution on the label crossing the boundary. -/
@[expose] def twistedRotate : List Factor → List Factor
  | [] => []
  | a :: w => w ++ [dualFactor a]
@[simp] theorem twistedRotate_length (w : List Factor) :
    (twistedRotate w).length = w.length := by
  cases w <;> simp [twistedRotate]

theorem foldedWord_twistedRotate (w : List Factor) :
    foldedWord (twistedRotate w) = (foldedWord w).rotate 1 := by
  cases w with
  | nil => rfl
  | cons a w =>
      simp [foldedWord, twistedRotate, dualWord, List.rotate_cons_succ, List.append_assoc]

theorem foldedWord_injective : Function.Injective foldedWord := by
  intro u v h
  have hl := congrArg List.length h
  simp only [foldedWord_length] at hl
  have hl' : u.length = v.length := by omega
  have ht := congrArg (List.take u.length) h
  change (u ++ dualWord u).take u.length = (v ++ dualWord v).take u.length at ht
  rw [List.take_left, hl', List.take_left] at ht
  exact ht

@[simp] theorem twistedRotate_iterate_length (w : List Factor) (r : ℕ) :
    (twistedRotate^[r] w).length = w.length := by
  induction r with
  | zero => rfl
  | succ r ih =>
      rw [Function.iterate_succ_apply', twistedRotate_length, ih]

theorem foldedWord_twistedRotate_iterate (w : List Factor) (r : ℕ) :
    foldedWord (twistedRotate^[r] w) = (foldedWord w).rotate r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', foldedWord_twistedRotate, ih, List.rotate_rotate]
end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue


public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
variable {F K : Type*} [Field F] [Field K] [CharP K 2] [IsAlgClosed K]
  (J : HermitianForm 3 F)

private theorem word_character_square (ι : F →+* K) (w : List Factor)
    (g : J.specialSubgroup) :
    (word J ((frobenius K 2).comp ι) w).character g =
      (word J ι w).character g ^ 2 := by
  have he : (iterateFrobeniusEquiv K 2 1 : K →+* K) = frobenius K 2 := by
    ext x
    change x ^ (2 ^ 1) = x ^ 2
    rw [pow_one]
  have h := wordRep_character_comp (iterateFrobeniusEquiv K 2 1) ι w
    (specialLinearInclusion J g)
  rw [he] at h
  exact h

private theorem word_character_cons (ι : F →+* K) (a : Factor) (w : List Factor)
    (g : J.specialSubgroup) :
    (word J ι (a :: w)).character g =
      (factorRep ι a).character (specialLinearInclusion J g) *
        (word J ι w).character g ^ 2 := by
  change (wordRep ι (a :: w)).character (specialLinearInclusion J g) = _
  rw [wordRep_character_cons]
  rw [show (wordRep ((frobenius K 2).comp ι) w).character (specialLinearInclusion J g) =
    (word J ι w).character g ^ 2 from word_character_square J ι w g]

private theorem word_character_append_singleton (ι : F →+* K) (w : List Factor)
    (a : Factor) (g : J.specialSubgroup) :
    (word J ι (w ++ [a])).character g = (word J ι w).character g *
      (factorRep ι a).character (specialLinearInclusion J g) ^ (2 ^ w.length) := by
  have hnil : (word J ι []).character g = 1 :=
    wordRep_character_nil ι (specialLinearInclusion J g)
  induction w with
  | nil => simp [word_character_cons, hnil]
  | cons b w ih =>
      simp only [List.cons_append, word_character_cons, ih, mul_pow, List.length_cons,
        pow_succ, pow_mul]
      ring

/-- One left rotation, with the graph twist at the boundary, cancels one
coefficient Frobenius. -/
theorem word_character_twistedRotate (ι : F →+* K) (w : List Factor)
    (hc : ∀ x, J.conj x = x ^ (2 ^ w.length)) (g : J.specialSubgroup) :
    (word J ι (twistedRotate w)).character g ^ 2 = (word J ι w).character g := by
  cases w with
  | nil =>
      change (wordRep ι []).character (specialLinearInclusion J g) ^ 2 =
        (wordRep ι []).character (specialLinearInclusion J g)
      simp only [wordRep_character_nil, one_pow]
  | cons a w =>
      change (word J ι (w ++ [dualFactor a])).character g ^ 2 = _
      rw [word_character_append_singleton, mul_pow, ← pow_mul, ← pow_succ,
        factor_character_unitary_frobenius J ι (w.length + 1) hc,
        dualFactor_involutive, word_character_cons, mul_comm]

/-- The iterated twisted rotation cancels the same number of coefficient
Frobenius operations on the literal restricted tensor word. -/
theorem word_character_twistedRotate_iterate (ι : F →+* K) (w : List Factor)
    (hc : ∀ x, J.conj x = x ^ (2 ^ w.length)) (r : ℕ) (g : J.specialSubgroup) :
    (word J ι (twistedRotate^[r] w)).character g ^ (2 ^ r) = (word J ι w).character g := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply', pow_succ, mul_comm (2 ^ r), pow_mul]
      rw [word_character_twistedRotate J ι _ (by simpa using hc), ih]

/-- Under irreducibility and separation of the length-s unitary catalogue,
the coefficient Frobenius stabilizer is the rotation stabilizer of the folded
word. The original Hermitian form supplies the graph twist. -/
theorem word_frobenius_equiv_iff_folded_rotation (ι : F →+* K)
    (w : List Factor) (hc : ∀ x, J.conj x = x ^ (2 ^ w.length))
    (hirr : ∀ v : List Factor, v.length = w.length → IsIrreducible (word J ι v))
    (hunique : ∀ u v : List Factor, u.length = w.length → v.length = w.length →
      Nonempty ((word J ι u).Equiv (word J ι v)) → u = v) (r : ℕ) :
    Nonempty ((word J ι w).Equiv (frobeniusConjugate 2 r (word J ι w))) ↔
      (foldedWord w).rotate r = foldedWord w := by
  let : IsIrreducible (word J ι w) := hirr w rfl
  let : IsIrreducible (frobeniusConjugate 2 r (word J ι w)) :=
    frobeniusConjugate_isIrreducible 2 r _
  let : IsIrreducible (word J ι (twistedRotate^[r] w)) :=
    hirr _ (twistedRotate_iterate_length w r)
  constructor
  · rintro ⟨E⟩
    have heq : (word J ι (twistedRotate^[r] w)).character = (word J ι w).character := by
      funext g
      apply (iterateFrobeniusEquiv K 2 r).injective
      change (word J ι (twistedRotate^[r] w)).character g ^ (2 ^ r) =
        (word J ι w).character g ^ (2 ^ r)
      have hf := congrFun (char_iso E) g
      rw [character_frobeniusConjugate] at hf
      exact (word_character_twistedRotate_iterate J ι w hc r g).trans hf
    have hi := hunique _ _ (twistedRotate_iterate_length w r) rfl
      ((character_eq_iff_equiv_of_irreducible _ _).mp heq)
    rw [← foldedWord_twistedRotate_iterate, hi]
  · intro h
    have hi : twistedRotate^[r] w = w :=
      foldedWord_injective ((foldedWord_twistedRotate_iterate w r).trans h)
    apply (character_eq_iff_equiv_of_irreducible _ _).mp
    funext g
    rw [character_frobeniusConjugate]
    have hc' := word_character_twistedRotate_iterate J ι w hc r g
    rw [hi] at hc'
    exact hc'.symm
end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
