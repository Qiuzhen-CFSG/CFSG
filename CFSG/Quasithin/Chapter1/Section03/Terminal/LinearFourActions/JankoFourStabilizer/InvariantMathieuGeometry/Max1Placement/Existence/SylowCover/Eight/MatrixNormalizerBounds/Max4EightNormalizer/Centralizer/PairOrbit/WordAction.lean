module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Eight.MatrixNormalizerBounds.Max4EightNormalizer.Centralizer.PairOrbit.Transport

/-!
# Exact source-word interpretation of the thirteen-bit action

Collect increasing binary words using the certified generator squares and
commutators. Crossing a tail past the next leading factor contributes its
commutator column; merging repeated factors contributes their squares. An
inductive Boolean-sum identity identifies these corrections with the row formula
in `Arithmetic`, including the central coordinate. Folding this multiplication
law interprets both mask actions as right conjugation in the original source
subgroup.

Only the original-word relations exported by `Transport` are used. The finite
pair-orbit tree is independent of this result.

Source: retained ATLAS J4G1-max2W1 words and
TwoCoreCentralizer/NormalClosureControl/Certificates;
Kleidman–Wilson (1988), pp.484–510; Aschbacher–Smith A.3.12, pp.47–48.
-/

public section

open Janko4.Cardinality.KernelCount
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open NormalClosureControl NormalClosureControl.IntrinsicCenter LowerBound
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData

private def collectParity : {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → Bool) →
    (Fin n → Bool) → (Fin n → Bool) → Bool
  | 0, _, _, _, _ => false
  | _ + 1, s, c, a, b =>
    (a 0 && b 0 && s 0) ^^ ((b 0 && pairing (fun i => a i.succ) (fun i => c i.succ 0)) ^^
      collectParity (fun i => s i.succ) (fun i j => c i.succ j.succ)
        (fun i => a i.succ) (fun i => b i.succ))

private theorem central_bit_mul {G : Type*} [Group G] (z : G) (hz : z ^ 2 = 1)
    (a b : Bool) : bit z (a ^^ b) = bit z a * bit z b := by
  cases a <;> cases b <;> simp [bit, ← pow_two, hz]

private theorem central_bit_commute {G : Type*} [Group G] (z : G)
    (hz : z ∈ Subgroup.center G) (b : Bool) (g : G) : Commute (bit z b) g := by
  cases b
  · exact Commute.one_left _
  · exact ((Subgroup.mem_center_iff.mp hz) g).symm

private theorem bit_product {G : Type*} [Group G] (e z : G) (s a b : Bool)
    (hs : e ^ 2 = bit z s) :
    bit e a * bit e b = bit e (a ^^ b) * bit z (a && b && s) := by
  cases a <;> cases b <;> simp [bit, ← pow_two, hs]

private theorem collect_step {G : Type*} [Group G] (a b c d e f z : G)
    (hz : z ∈ Subgroup.center G) (p q r : Bool)
    (hab : a * b = e * bit z p) (hcb : c * b = b * c * bit z q)
    (hcd : c * d = f * bit z r) :
    (a * c) * (b * d) = (e * f) * (bit z p * (bit z q * bit z r)) := by
  calc
    (a * c) * (b * d) = a * (c * b) * d := by simp only [mul_assoc]
    _ = (a * b) * (c * d) * bit z q := by
      rw [hcb]
      simp only [mul_assoc]
      rw [(central_bit_commute z hz q d).eq]
    _ = (e * f) * (bit z p * (bit z q * bit z r)) := by
      rw [hab, hcd]
      simp only [mul_assoc]
      rw [← mul_assoc (bit z p), (central_bit_commute z hz p f).eq]
      simp only [mul_assoc]
      rw [(central_bit_commute z hz r (bit z q)).eq]

private theorem collect_product {G : Type*} [Group G] {n : ℕ}
    (e : Fin n → G) (s : Fin n → Bool) (c : Fin n → Fin n → Bool)
    (z : G) (hz : z ∈ Subgroup.center G) (hz2 : z ^ 2 = 1)
    (hs : ∀ i, e i ^ 2 = bit z (s i))
    (hc : ∀ i j, e i * e j = e j * e i * bit z (c i j))
    (a b : Fin n → Bool) :
    binaryProduct e a * binaryProduct e b =
      binaryProduct e (fun i => a i ^^ b i) * bit z (collectParity s c a b) := by
  induction n with
  | zero => simp [binaryProduct, collectParity, bit]
  | succ n ih =>
    have htail := ih (fun i => e i.succ) (fun i => s i.succ)
      (fun i j => c i.succ j.succ) (fun i => hs i.succ)
      (fun i j => hc i.succ j.succ) (fun i => a i.succ) (fun i => b i.succ)
    have htwist := binaryProduct_twist (fun i => e i.succ) (fun i => a i.succ)
      (fun i => c i.succ 0) (e 0) z hz hz2 (fun i => hc i.succ 0)
    have htwist' : binaryProduct (fun i => e i.succ) (fun i => a i.succ) * bit (e 0) (b 0) =
        bit (e 0) (b 0) * binaryProduct (fun i => e i.succ) (fun i => a i.succ) *
          bit z (b 0 && pairing (fun i => a i.succ) (fun i => c i.succ 0)) := by
      cases hb : b 0
      · simp [bit]
      · simpa only [bit, Bool.true_eq, ite_true, Bool.true_and] using htwist
    simp only [binaryProduct_succ, collectParity, central_bit_mul z hz2]
    exact collect_step (bit (e 0) (a 0)) (bit (e 0) (b 0)) _ _ _ _ z hz _ _ _
      (bit_product _ _ _ _ _ (hs 0)) htwist' htail



private def xorSum {n : ℕ} (f : Fin n → Bool) : Bool :=
  (List.ofFn f).foldr Bool.xor false

private theorem xorSum_succ {n : ℕ} (f : Fin (n + 1) → Bool) :
    xorSum f = (f 0 ^^ xorSum (fun i => f i.succ)) := by
  simp only [xorSum, List.ofFn_succ, List.foldr_cons]

private theorem xorSum_false (n : ℕ) : xorSum (fun _ : Fin n => false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => rw [xorSum_succ, ih, Bool.false_xor]

private theorem xorSum_xor {n : ℕ} (f g : Fin n → Bool) :
    xorSum (fun i => f i ^^ g i) = (xorSum f ^^ xorSum g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorSum_succ, ih, Bool.xor_assoc, Bool.xor_left_comm]

private theorem xorSum_and {n : ℕ} (b : Bool) (f : Fin n → Bool) :
    xorSum (fun i => b && f i) = (b && xorSum f) := by
  cases b
  · simp only [Bool.false_and, xorSum_false]
  · simp only [Bool.true_and]

private theorem collectParity_eq_rows {n : ℕ} (s : Fin n → Bool)
    (c : Fin n → Fin n → Bool) (a b : Fin n → Bool) :
    collectParity s c a b = xorSum (fun i => a i && ((s i && b i) ^^
      xorSum (fun j => decide (j < i) && b j && c i j))) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [collectParity, xorSum_succ, Fin.not_lt_zero, decide_false,
      Bool.false_and, xorSum_false, Bool.xor_false, Fin.succ_pos,
      decide_true, Bool.true_and, Fin.succ_lt_succ_iff]
    rw [ih]
    have hrow : (fun i : Fin n => a i.succ && ((s i.succ && b i.succ) ^^
        ((b 0 && c i.succ 0) ^^ xorSum (fun j : Fin n =>
          decide (j < i) && b j.succ && c i.succ j.succ)))) =
        (fun i : Fin n => (b 0 && (a i.succ && c i.succ 0)) ^^
          (a i.succ && ((s i.succ && b i.succ) ^^ xorSum (fun j : Fin n =>
            decide (j < i) && b j.succ && c i.succ j.succ)))) := by
      funext i
      simp only [Bool.and_xor_distrib_left, Bool.and_comm,
        Bool.and_left_comm, Bool.xor_left_comm]
    rw [hrow, xorSum_xor, xorSum_and]
    change _ = (a 0 && (s 0 && b 0) ^^ ((b 0 && pairing _ _) ^^ _))
    simp only [Bool.and_comm, Bool.and_left_comm]

private theorem collectParity_eq_correction (a b : ℕ) :
    collectParity (fun i : Fin 13 => decide (i.val ≠ 0)) commutatorForm
      (fun i => a.testBit i.val) (fun i => b.testBit i.val) = correction a b :=
  collectParity_eq_rows _ _ _ _

private theorem source_factor_square (i : Fin 13) :
    kernelFactor i ^ 2 = bit (kernelFactor 0) (decide (i.val ≠ 0)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.val_zero, ne_eq, not_true_eq_false, decide_false, bit, Bool.false_eq_true,
      ite_false] using source_factor_zero_square
  · simpa [bit] using source_factor_succ_square j

private theorem maskProduct_mul_correction (a b : ℕ) :
    maskProduct kernelFactor a * maskProduct kernelFactor b =
      maskProduct kernelFactor (a ^^^ b) * bit (kernelFactor 0) (correction a b) := by
  have h := collect_product kernelFactor (fun i => decide (i.val ≠ 0)) commutatorForm
    (kernelFactor 0) source_factor_zero_central source_factor_zero_square
    source_factor_square source_factor_commutator (fun i => a.testBit i.val)
    (fun i => b.testBit i.val)
  rw [collectParity_eq_correction] at h
  simpa only [maskProduct, binaryProduct, Nat.testBit_xor] using h


private theorem bool_testBit_zero (b : Bool) : b.toNat.testBit 0 = b := by
  cases b <;> decide

private theorem bool_testBit_succ (b : Bool) (i : ℕ) : b.toNat.testBit (i + 1) = false := by
  cases b <;> simp [Nat.testBit_add_one]

private theorem maskProduct_central (m : ℕ) (b : Bool) :
    maskProduct kernelFactor (m ^^^ b.toNat) =
      maskProduct kernelFactor m * bit (kernelFactor 0) b := by
  simp only [maskProduct, List.ofFn_succ, List.prod_cons, Fin.val_zero,
    Nat.testBit_xor, bool_testBit_zero, Fin.val_succ, bool_testBit_succ, Bool.xor_false]
  change bit (kernelFactor 0) (m.testBit 0 ^^ b) * _ = (bit (kernelFactor 0) (m.testBit 0) * _) * _
  rw [central_bit_mul _ source_factor_zero_square]
  rw [mul_assoc, (central_bit_commute _ source_factor_zero_central b _).eq, ← mul_assoc]

/-- The complete mask product agrees with multiplication of the original source words. -/
theorem source_mask_multiply (a b : ℕ) :
    maskProduct kernelFactor (maskMultiply a b) =
      maskProduct kernelFactor a * maskProduct kernelFactor b := by
  rw [maskMultiply, maskProduct_central, maskProduct_mul_correction]

private theorem maskProduct_zero : maskProduct kernelFactor 0 = 1 := by
  simp [maskProduct]

private theorem mask_fold_sound (f : Fin 13 → ℕ) (m : ℕ)
    (l : List (Fin 13)) (r : ℕ) :
    maskProduct kernelFactor
      (l.foldl (fun r i => if m.testBit i.val then maskMultiply r (f i) else r) r) =
    maskProduct kernelFactor r *
      (l.map (fun i => if m.testBit i.val then maskProduct kernelFactor (f i) else 1)).prod := by
  induction l generalizing r with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons, List.map_cons, List.prod_cons, ih]
    cases m.testBit i.val <;>
      simp only [Bool.false_eq_true, ite_false, ite_true,
        source_mask_multiply, one_mul, mul_assoc]

private theorem maskAction_sound (useY : Bool) (m : ℕ) :
    maskProduct kernelFactor (maskAction useY m) =
      maskProduct (fun i => maskProduct kernelFactor
        (if useY then Certificates.yMasks i else Certificates.xMasks i)) m := by
  rw [maskAction, mask_fold_sound, maskProduct_zero, one_mul]
  simp only [List.finRange, List.map_ofFn, maskProduct]
  rfl

/-- Arithmetic's full thirteen-bit action is right conjugation in the original max2 subgroup. -/
theorem source_action_law : SourceActionLaw := by
  intro useY m
  cases useY
  · change sourceX⁻¹ * maskProduct kernelFactor m.val * sourceX = _
    rw [source_product_action_x, maskAction_sound]
    rfl
  · change sourceY⁻¹ * maskProduct kernelFactor m.val * sourceY = _
    rw [source_product_action_y, maskAction_sound]
    rfl

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.MatrixNormalizerBounds.Max4EightCentralizer.PairOrbitData
