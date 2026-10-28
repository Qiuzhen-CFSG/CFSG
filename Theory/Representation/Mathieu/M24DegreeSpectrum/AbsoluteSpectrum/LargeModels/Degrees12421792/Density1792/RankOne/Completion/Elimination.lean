module

public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# A kernel-checked binary elimination criterion

An entry subtracts selected earlier rows from one original equation. The
checker validates that equation and its descending pivot. Soundness preserves
all original homogeneous solutions; one pivot at every coordinate forces a
solution to vanish, by induction on the coordinate. The final bridge decodes
exactly the update by the zeroth-coordinate covector, without transposition.

The concrete consumer is the fixed M₂₄ degree-1792 completion in `Completion`.
Source data and attribution: `source/README.md` and `../source/README.md`.
-/

@[expose] public section
open Thompson.BinaryMatrix Matrix
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionElimination

def dot {n : Nat} (r : Nat) (w : Fin n → ZMod 2) : ZMod 2 :=
  (fun i => bit r i.val) ⬝ᵥ w

lemma dot_xor {n : Nat} (r s : Nat) (w : Fin n → ZMod 2) :
    dot (r ^^^ s) w = dot r w + dot s w := by
  simp only [dot, bit_xor]
  exact add_dotProduct _ _ _

def reduceRow : Nat → Nat → List Nat → Nat
  | r, _, [] => r
  | r, c, b :: bs => reduceRow (if c % 2 == 1 then r ^^^ b else r) (c / 2) bs

lemma reduceRow_zero {n : Nat} (r c : Nat) (bs : List Nat) (w : Fin n → ZMod 2)
    (hr : dot r w = 0) (hb : ∀ b ∈ bs, dot b w = 0) :
    dot (reduceRow r c bs) w = 0 := by
  induction bs generalizing r c with
  | nil => exact hr
  | cons b bs ih =>
    apply ih
    · split_ifs
      · rw [dot_xor, hr, hb b (by simp), add_zero]
      · exact hr
    · intro a ha
      exact hb a (by simp [ha])

structure Entry where
  source : Nat
  coeff : Nat
  row : Nat

def checkEntries (n : Nat) (source : Nat → Nat) : Nat → List Nat → List Entry → Bool
  | _, _, [] => true
  | k, bs, e :: es =>
      (e.source < n) && (k < n) &&
      (reduceRow (source e.source) e.coeff bs == e.row) &&
      (e.row / 2 ^ (n - (k+1)) == 1) &&
      checkEntries n source (k+1) (e.row :: bs) es

def State {n : Nat} (k : Nat) (bs : List Nat) (w : Fin n → ZMod 2) : Prop :=
  (∀ b ∈ bs, dot b w = 0) ∧
  ∀ j, j < n → n ≤ j+k → ∃ r, dot r w = 0 ∧ r / 2^j = 1

lemma state_zero {n : Nat} (w : Fin n → ZMod 2) : State 0 [] w := by
  constructor
  · simp
  · intro j hj hjk
    omega

lemma checkEntries_sound {n : Nat} (source : Nat → Nat)
    (w : Fin n → ZMod 2) (hsrc : ∀ i, i < n → dot (source i) w = 0)
    (k : Nat) (bs : List Nat) (es : List Entry)
    (hc : checkEntries n source k bs es = true) (hs : State k bs w) :
    State (k + es.length) ((es.map Entry.row).reverse ++ bs) w := by
  induction es generalizing k bs with
  | nil => simpa using hs
  | cons e es ih =>
    simp only [checkEntries, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
    rcases hc with ⟨⟨⟨⟨hsource, hk⟩, he⟩, hp⟩, hc⟩
    have hz : dot e.row w = 0 := by
      rw [← he]
      exact reduceRow_zero _ _ _ _ (hsrc e.source hsource) hs.1
    have hs' : State (k+1) (e.row :: bs) w := by
      constructor
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hz
        · exact hs.1 b hb
      · intro j hj hjk
        by_cases hjk' : n ≤ j+k
        · exact hs.2 j hj hjk'
        · have hj' : j = n - (k+1) := by omega
          exact ⟨e.row, hz, hj' ▸ hp⟩
    simpa only [List.length_cons, List.map_cons, List.reverse_cons,
      List.append_assoc, List.singleton_append, Nat.add_assoc, Nat.add_comm 1] using
      ih (k+1) (e.row :: bs) hc hs'

lemma bit_pivot (r j i : Nat) (hr : r / 2^j = 1) (hi : j ≤ i) :
    bit r i = if i = j then 1 else 0 := by
  have h := congrArg (fun x => bit x (i-j)) hr
  simp only [bit, Nat.testBit_div_two_pow, Nat.sub_add_cancel hi] at h
  unfold bit
  rw [h]
  change (if (2^0 : Nat).testBit (i-j) then (1 : ZMod 2) else 0) = _
  simp only [Nat.testBit_two_pow, decide_eq_true_eq, show (0 = i-j) ↔ i = j by omega]

lemma state_complete {n : Nat} (bs : List Nat) (w : Fin n → ZMod 2)
    (hs : State n bs w) : w = 0 := by
  have hw : ∀ j, ∀ hj : j < n, w ⟨j, hj⟩ = 0 := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj
      obtain ⟨r, hr, hp⟩ := hs.2 j hj (by omega)
      have hd : dot r w = w ⟨j, hj⟩ := by
        unfold dot dotProduct
        rw [Finset.sum_eq_single ⟨j, hj⟩]
        · change bit r j * w ⟨j, hj⟩ = w ⟨j, hj⟩
          rw [bit_pivot r j j hp (by rfl), if_pos rfl, one_mul]
        · intro i _ hi
          change bit r i.val * w i = 0
          by_cases hij : i.val < j
          · rw [ih i.val hij i.isLt, mul_zero]
          · rw [bit_pivot r j i.val hp (by omega), if_neg (by
              intro he; apply hi; exact Fin.ext he), zero_mul]
        · simp
      exact hd.symm.trans hr
  ext i
  exact hw i.val i.isLt
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionElimination

namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionElimination

def sourceRow (rows : Array Nat) (u i : Nat) : Nat := rows[i]! ^^^ (u / 2^i % 2)

lemma bit_low (u i j : Nat) :
    bit (u / 2^i % 2) j = if j = 0 then bit u i else 0 := by
  change bit (u / 2^i % 2^1) j = _
  simp only [bit, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j = 0
  · subst j
    simp
  · have hj' : ¬j < 1 := by omega
    simp [hj, hj']

lemma sourceRow_eq {n : Nat} [NeZero n] (rows : Array Nat) (u : Nat) (i : Fin n) :
    (fun j : Fin n => bit (sourceRow rows u i.val) j.val) =
      (decode n rows + Matrix.vecMulVec (fun k : Fin n => bit u k.val)
        (Pi.single (0 : Fin n) (1 : ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) i := by
  ext j
  simp only [sourceRow, bit_xor, bit_low, Matrix.add_apply, decode,
    Matrix.vecMulVec_apply, Pi.single_apply, Fin.ext_iff, Fin.val_zero]
  by_cases hj : j.val = 0
  · simp [hj]
  · simp [hj]

lemma sourceRow_dot {n : Nat} [NeZero n] (rows : Array Nat) (u : Nat)
    (w : Fin n → ZMod 2)
    (hw : (decode n rows + Matrix.vecMulVec (fun k : Fin n => bit u k.val)
      (Pi.single 0 1)).mulVec w = 0) :
    ∀ i, i < n → dot (sourceRow rows u i) w = 0 := by
  intro i hi
  have h := congrFun hw ⟨i, hi⟩
  change _ ⬝ᵥ w = 0 at h
  rw [← sourceRow_eq rows u ⟨i, hi⟩] at h
  exact h
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.CompletionElimination
