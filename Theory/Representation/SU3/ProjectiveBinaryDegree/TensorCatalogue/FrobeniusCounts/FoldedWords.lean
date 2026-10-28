module

public import Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.WordBounds
public import Theory.Representation.SL3.BinaryDefiningFactors.FrobeniusPeriod.RepeatedBlocks
import all Theory.Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue.WordBounds

/-!
# Counts in a unitary word from its exact folded rotation period

The graph involution exchanges natural and dual labels. Doubling a word as
`w ++ dualWord w` turns twisted rotation into ordinary rotation. If its exact
positive period is e, a natural label prevents e from dividing the original
length s. Thus 2*s/e is odd, and repeated-block counts imply that it divides
`naturalCount w`. Without natural labels, the half-length s is a period;
nontriviality then forces the analogous positive adjoint count.

The Schur-model consumer in `FrobeniusCounts` supplies the exact stabilizer and
nontriviality. This intentional implementation split uses an internal import of
`WordBounds` to construct its existing unexposed `PeriodCounts` predicate.

Source: GLS III, Remark 2.8.8; Guralnick--Malle, §3.1, internal p.12.
Reused from `CFSG/Quasithin/ChapterK/Section01To04/RankOne/UnitaryRecognition/MinimalDegree/FrobeniusCounts/FoldedWords.lean`, with the original
proofs retained in a reusable Theory namespace for Fong--Seitz I (4D).
-/

public section
namespace Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue

open Representation.SL3.BinaryDefiningFactors

/-- The A₂ graph involution on the four binary restricted labels. -/
@[expose] def dualFactor : Factor → Factor
  | .trivial => .trivial
  | .natural => .dual
  | .dual => .natural
  | .adjoint => .adjoint

/-- Apply the graph involution at every position. -/
@[expose] def dualWord (w : List Factor) : List Factor := w.map dualFactor

/-- The doubled word on which the graph-twisted shift is ordinary rotation. -/
@[expose] def foldedWord (w : List Factor) : List Factor := w ++ dualWord w

@[simp] theorem dualFactor_involutive (a : Factor) : dualFactor (dualFactor a) = a := by
  cases a <;> rfl

@[simp] theorem dualWord_dualWord (w : List Factor) : dualWord (dualWord w) = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      change dualFactor (dualFactor a) :: dualWord (dualWord w) = a :: w
      rw [dualFactor_involutive, ih]

@[simp] theorem dualWord_length (w : List Factor) : (dualWord w).length = w.length := by
  simp [dualWord]

@[simp] theorem foldedWord_length (w : List Factor) :
    (foldedWord w).length = 2 * w.length := by
  simp [foldedWord, dualWord]
  omega

private theorem naturalCount_dualWord (w : List Factor) :
    naturalCount (dualWord w) = naturalCount w := by
  simp only [dualWord, naturalCount, List.countP_map]
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.countP_cons, Function.comp_apply]
      cases a <;> simp [dualFactor, ih]

private theorem adjointCount_dualWord (w : List Factor) :
    adjointCount (dualWord w) = adjointCount w := by
  change List.count .adjoint (List.map dualFactor w) = List.count .adjoint w
  induction w with
  | nil => rfl
  | cons a w ih =>
      simp only [List.count_cons]
      cases a <;> simp [dualFactor, ih]

@[simp] theorem naturalCount_foldedWord (w : List Factor) :
    naturalCount (foldedWord w) = 2 * naturalCount w := by
  change List.countP _ (w ++ dualWord w) = _
  change List.countP _ (w ++ dualWord w) = 2 * List.countP _ w
  have hnc := naturalCount_dualWord w
  change List.countP _ (dualWord w) = naturalCount w at hnc
  rw [List.countP_append, hnc]
  change List.countP _ w + List.countP _ w = 2 * List.countP _ w
  omega

@[simp] theorem adjointCount_foldedWord (w : List Factor) :
    adjointCount (foldedWord w) = 2 * adjointCount w := by
  change List.count .adjoint (w ++ dualWord w) = _
  change List.count .adjoint (w ++ dualWord w) = 2 * List.count .adjoint w
  have hac := adjointCount_dualWord w
  change List.count .adjoint (dualWord w) = adjointCount w at hac
  rw [List.count_append, hac]
  change adjointCount w + adjointCount w = 2 * adjointCount w
  omega

private theorem foldedWord_rotate_length (w : List Factor) :
    (foldedWord w).rotate w.length = dualWord w ++ w := by
  change (w ++ dualWord w).rotate w.length = _
  rw [List.rotate_append_length_eq]

private theorem foldedWord_eq_dual_of_rotate_eq (w : List Factor)
    (h : (foldedWord w).rotate w.length = foldedWord w) :
    dualWord w = w := by
  rw [foldedWord_rotate_length w, foldedWord] at h
  have ht := congrArg (List.take w.length) h
  simpa [dualWord, List.take_append_of_le_length] using ht

private theorem naturalCount_eq_zero_of_dualWord_eq (w : List Factor)
    (h : dualWord w = w) : naturalCount w = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      have hc : dualFactor a :: dualWord w = a :: w := by
        simpa [dualWord] using h
      have ha : dualFactor a = a := (List.cons.inj hc).1
      have hw : dualWord w = w := (List.cons.inj hc).2
      cases a <;> simp_all [naturalCount, dualFactor]

private theorem dualWord_ne_of_naturalCount_pos (w : List Factor)
    (h : 0 < naturalCount w) : dualWord w ≠ w := by
  intro heq
  have hz := naturalCount_eq_zero_of_dualWord_eq w heq
  omega

private theorem dualWord_eq_of_naturalCount_eq_zero (w : List Factor)
    (h : naturalCount w = 0) : dualWord w = w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      cases a with
      | trivial =>
          have hw : naturalCount w = 0 := by simpa [naturalCount] using h
          simpa [dualWord, dualFactor] using ih hw
      | adjoint =>
          have hw : naturalCount w = 0 := by simpa [naturalCount] using h
          simpa [dualWord, dualFactor] using ih hw
      | natural => simp [naturalCount] at h
      | dual => simp [naturalCount] at h

private theorem folded_rotation_mul (u : List Factor) (e q : ℕ)
    (hrot : u.rotate e = u) : u.rotate (e * q) = u := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Nat.mul_succ, ← List.rotate_rotate, ih, hrot]

private theorem folded_rotation_of_dvd (u : List Factor) (e s : ℕ)
    (hes : e ∣ s) (hrot : u.rotate e = u) : u.rotate s = u := by
  obtain ⟨q, hq⟩ := hes
  rw [hq]
  exact folded_rotation_mul u e q hrot

/-! A period of the folded word gives the required numerical divisibility. -/

/-- An exact folded rotation period gives the two counts consumed by the
minimal-degree inequality. Nontriviality is retained explicitly here. -/
theorem periodCounts_of_folded_rotation
    (s e : ℕ) (w : List Factor)
    (hs : 0 < s) (hw : w.length = s) (hed : e ∣ 2 * s)
    (hlabels : 0 < naturalCount w + adjointCount w)
    (hmin : ∀ r, (foldedWord w).rotate r = foldedWord w → e ∣ r)
    (hrot : (foldedWord w).rotate e = foldedWord w) :
    PeriodCounts s e w := by
  unfold PeriodCounts
  by_cases hn : 0 < naturalCount w
  · have hnot : ¬ e ∣ s := by
      intro hes
      have hrot' : (foldedWord w).rotate s = foldedWord w :=
        folded_rotation_of_dvd (foldedWord w) e s hes hrot
      have hrot'' : (foldedWord w).rotate w.length = foldedWord w := by
        simpa [hw] using hrot'
      have hdual : dualWord w = w := foldedWord_eq_dual_of_rotate_eq w hrot''
      exact dualWord_ne_of_naturalCount_pos w hn hdual
    obtain ⟨r, hr⟩ := hed
    have hlen : (foldedWord w).length = e * r := by
      rw [foldedWord_length, hw]
      exact hr
    have hrpos : 0 < r := by
      apply Nat.pos_of_ne_zero
      intro hr0
      subst r
      simp at hr
      omega
    have hrep := List.eq_flatten_replicate_take_of_rotate_eq
      (foldedWord w) e r hrpos hlen hrot
    have hcount := congrArg naturalCount hrep
    rw [naturalCount_foldedWord, naturalCount_repeat] at hcount
    have hdiv : r ∣ 2 * naturalCount w := by
      refine ⟨naturalCount ((foldedWord w).take e), ?_⟩
      omega
    have hnotEven : ¬ Even r := by
      intro hev
      obtain ⟨q, hq⟩ := hev
      apply hnot
      refine ⟨q, ?_⟩
      have heq : 2 * s = 2 * (e * q) := by
        calc
          2 * s = e * r := hr
          _ = e * (q + q) := by rw [hq]
          _ = 2 * (e * q) := by ring
      exact Nat.mul_left_cancel (by decide) heq
    have hodd : Odd r := Nat.not_even_iff_odd.mp hnotEven
    have hcop : Nat.Coprime r 2 := Nat.coprime_two_right.mpr hodd
    have hdiv' : r ∣ naturalCount w :=
      hcop.dvd_of_dvd_mul_right (by simpa [Nat.mul_comm] using hdiv)
    refine Or.inl ⟨r, hrpos, ?_, ?_⟩
    · exact hr.symm
    · exact Nat.le_of_dvd hn hdiv'
  · have hn0 : naturalCount w = 0 := by omega
    have ha : 0 < adjointCount w := by omega
    have hdual : dualWord w = w := dualWord_eq_of_naturalCount_eq_zero w hn0
    have hrotS' : (foldedWord w).rotate w.length = foldedWord w := by
      rw [foldedWord_rotate_length]
      simp [foldedWord, hdual]
    have hrotS : (foldedWord w).rotate s = foldedWord w := by simpa [hw] using hrotS'
    have heS : e ∣ s := hmin s hrotS
    obtain ⟨r, hr⟩ := heS
    have hlen : (foldedWord w).length = e * (2 * r) := by
      rw [foldedWord_length, hw]
      calc
        2 * s = 2 * (e * r) := by rw [hr]
        _ = e * (2 * r) := by ring
    have hrpos : 0 < r := by
      apply Nat.pos_of_ne_zero
      intro hr0
      subst r
      simp at hr
      omega
    have htrpos : 0 < 2 * r := by omega
    have hrep := List.eq_flatten_replicate_take_of_rotate_eq
      (foldedWord w) e (2 * r) htrpos hlen hrot
    have hcount := congrArg adjointCount hrep
    rw [adjointCount_foldedWord, adjointCount_repeat] at hcount
    refine Or.inr ⟨r, hrpos, ?_, ?_⟩
    · exact hr.symm
    · have hAc : adjointCount w = r * adjointCount ((foldedWord w).take e) := by
        have heq : 2 * adjointCount w =
            2 * (r * adjointCount ((foldedWord w).take e)) := by
          calc
            2 * adjointCount w = (2 * r) * adjointCount ((foldedWord w).take e) := hcount
            _ = 2 * (r * adjointCount ((foldedWord w).take e)) := by ring
        exact Nat.mul_left_cancel (by decide) heq
      apply Nat.le_of_dvd ha
      exact ⟨adjointCount ((foldedWord w).take e), hAc⟩

end Representation.SU3.ProjectiveBinaryDegree.TensorCatalogue
