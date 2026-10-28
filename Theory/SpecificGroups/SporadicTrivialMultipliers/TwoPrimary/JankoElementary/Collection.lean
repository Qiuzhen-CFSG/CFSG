module
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.BinarySpan
public import Theory.GroupTheory.CentralBinaryKernelSquares
import Mathlib.Tactic.Group

/-!
# Collection in a central binary extension

The square of an ordered binary word is a quadratic polynomial in its bits.
The coefficients are the generator squares and central pair commutators.
The collection argument follows the existing max2 calculation in
`Janko4.Model.InvolutionCentralizers.First.PlusType.Quadratic`, here with
narrow imports and without any model-specific assumptions.
-/

@[expose] public section
namespace Janko4.TwoPrimary.JankoElementary
open Subgroup Cardinality.KernelCount

/-- Evaluation of a Boolean exponent. -/
def bit {G : Type*} [One G] (t : G) (b : Bool) : G := if b then t else 1

/-- Binary dot product. -/
def dot : {n : ℕ} → (Fin n → Bool) → (Fin n → Bool) → Bool
  | 0, _, _ => false
  | _+1, v, w => (v 0 && w 0) ^^ dot (fun i => v i.succ) (fun i => w i.succ)

/-- Square polynomial, using only the strictly upper triangular twists. -/
def quadratic : {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → Bool) →
    (Fin n → Bool) → Bool
  | 0, _, _, _ => false
  | _+1, s, b, v => (v 0 && s 0) ^^ (quadratic (fun i => s i.succ)
      (fun i j => b i.succ j.succ) (fun i => v i.succ) ^^
        (v 0 && dot (fun i => v i.succ) (fun j => b 0 j.succ)))

lemma bit_xor {G : Type*} [Group G] (t : G) (ht : t ^ 2 = 1) (a b : Bool) :
    bit t (a ^^ b) = bit t a * bit t b := by
  cases a <;> cases b <;> simp [bit, ← pow_two, ht]

lemma bit_commute {G : Type*} [Group G] (t : G) (ht : t ∈ center G)
    (b : Bool) (g : G) : Commute (bit t b) g := by
  cases b
  · exact Commute.one_left _
  · exact ((mem_center_iff.mp ht) g).symm

lemma bit_injective {G : Type*} [One G] (t : G) (ht : t ≠ 1) :
    Function.Injective (bit t) := by
  intro a b h
  cases a <;> cases b <;> simp_all [bit]

private lemma twisted_mul {G : Type*} [Group G] (a b g s r : G)
    (ha : a * g = g * a * s) (hb : b * g = g * b * r) (hs : Commute s b) :
    (a * b) * g = g * (a * b) * (s * r) := by
  calc
    (a * b) * g = a * (b * g) := mul_assoc _ _ _
    _ = a * (g * b * r) := by rw [hb]
    _ = (a * g) * b * r := by simp only [mul_assoc]
    _ = (g * a * s) * b * r := by rw [ha]
    _ = g * (a * b) * (s * r) := by
      rw [mul_assoc (g * a) s b, hs.eq]
      simp only [mul_assoc]

lemma word_twist {G : Type*} [Group G] {n : ℕ}
    (e : Fin n → G) (v w : Fin n → Bool) (g t : G)
    (ht : t ∈ center G) (ht2 : t ^ 2 = 1)
    (he : ∀ i, e i * g = g * e i * bit t (w i)) :
    binaryProduct e v * g = g * binaryProduct e v * bit t (dot v w) := by
  induction n with
  | zero => simp [binaryProduct, dot, bit]
  | succ n ih =>
    rw [binaryProduct_succ, dot, bit_xor t ht2]
    apply twisted_mul
    · cases v 0 <;> simp [bit, he]
    · exact ih _ _ _ (fun i => he i.succ)
    · exact bit_commute t ht _ _

private lemma square_mul {G : Type*} [Group G] (a b t : G)
    (ht : t ∈ center G) (v : Bool) (h : b * a = a * b * bit t v) :
    (a * b) ^ 2 = a ^ 2 * b ^ 2 * bit t v := by
  simp only [pow_two]
  calc
    a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
    _ = a * (a * b * bit t v) * b := by rw [h]
    _ = a * a * (b * b) * bit t v := by
      simp only [mul_assoc]
      rw [(bit_commute t ht v b).eq]

/-- Collection proves the square polynomial in every group with the displayed
central generator squares and pair twists. -/
theorem word_square {G : Type*} [Group G] {n : ℕ}
    (e : Fin n → G) (s : Fin n → Bool) (b : Fin n → Fin n → Bool)
    (t : G) (ht : t ∈ center G) (ht2 : t ^ 2 = 1)
    (hs : ∀ i, e i ^ 2 = bit t (s i))
    (hb : ∀ i j, e j * e i = e i * e j * bit t (b i j))
    (v : Fin n → Bool) : binaryProduct e v ^ 2 = bit t (quadratic s b v) := by
  induction n with
  | zero => simp [binaryProduct, quadratic, bit]
  | succ n ih =>
    rw [binaryProduct_succ]
    have htail := ih (fun i => e i.succ) (fun i => s i.succ)
      (fun i j => b i.succ j.succ) (fun i => hs i.succ)
      (fun i j => hb i.succ j.succ) (fun i => v i.succ)
    have htwist := word_twist (fun i => e i.succ) (fun i => v i.succ)
      (fun i => b 0 i.succ) (e 0) t ht ht2 (fun i => hb 0 i.succ)
    cases hv : v 0
    · simpa [hv, quadratic] using htail
    · simp only [if_true]
      rw [square_mul _ _ t ht _ htwist, hs 0, htail]
      simp only [quadratic, hv, Bool.true_and, bit_xor t ht2, mul_assoc]

/-- Vanishing of the diagonal and upper triangular coefficients annihilates the form. -/
theorem quadratic_zero {n : ℕ} (s : Fin n → Bool) (b : Fin n → Fin n → Bool)
    (hs : ∀ i, s i = false) (hb : ∀ i j, i < j → b i j = false)
    (v : Fin n → Bool) : quadratic s b v = false := by
  have hd : ∀ (n : ℕ) (v w : Fin n → Bool), (∀ i, w i = false) → dot v w = false := by
    intro n v w hw
    induction n with
    | zero => rfl
    | succ n ih => simp [dot, hw, ih]
  induction n with
  | zero => rfl
  | succ n ih =>
    have ht := ih (fun i => s i.succ) (fun i j => b i.succ j.succ)
      (fun i => hs i.succ) (fun i j hij => hb i.succ j.succ (Fin.succ_lt_succ_iff.mpr hij)) (fun i => v i.succ)
    rw [quadratic, ht, hs 0, hd _ _ _ (fun i => hb 0 i.succ (Fin.succ_pos i))]
    simp

end Janko4.TwoPrimary.JankoElementary
