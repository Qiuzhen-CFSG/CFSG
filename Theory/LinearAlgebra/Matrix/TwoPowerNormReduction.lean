module

public import Theory.LinearAlgebra.Matrix.BinaryIdempotentPlane
public import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Reducing involution norms over two-power residue rings

Write an involutory matrix as `T = I + 2 M`. Its doubled norm is `4 (I + M)`,
and `M² + M` is killed by four. Thus `I + M` becomes idempotent modulo
`2^(n-2)`. Cancellation in `ZMod` identifies each norm equation with the
pullback of the corresponding idempotent equation over this smaller ring.

The binary label of a top-torsion vector is nonzero exactly when the vector
is nonzero. Reduction modulo two also detects units, supplying the local
ring input for lifting idempotents. These statements prepare the independent
fiber-cardinality and idempotent-classification arguments.

Source context: the elementary homocyclic norm calculation in the
MacWilliams–Sah bound quoted by Janko–Thompson, Math. Z. 113 (1970), 1.1,
printed p.385. The cancellation proof follows the arithmetic argument of
the private `HomocyclicFourTorsion.reduction_zero_iff` in
`Theory/GroupTheory/PGroup/HomocyclicFourTorsionCoordinates.lean`, reproduced
at the matrix layer to avoid a dependency on group-action coordinates.
-/

public section

open Matrix
namespace TwoPowerNorm

/-- The vector of top two-torsion with the prescribed binary label. -/
def topVector (n : ℕ) (w : BinaryIdempotentPlane.Vec) : Fin 2 → ZMod (2 ^ n) :=
  fun i => (2 : ZMod (2 ^ n)) ^ (n - 1) * ((w i).val : ZMod (2 ^ n))

@[simp] theorem topVector_apply (n : ℕ) (w : BinaryIdempotentPlane.Vec) (i : Fin 2) :
    topVector n w i = (2 : ZMod (2 ^ n)) ^ (n - 1) * ((w i).val : ZMod (2 ^ n)) := by
  unfold topVector
  rfl

/-- Vanishing in a quotient residue ring is scalar annihilation in the original ring. -/
lemma cast_eq_zero_iff_mul_eq_zero {N k t : ℕ} [NeZero N]
    (ht : 0 < t) (hN : N = t * k) (hdiv : k ∣ N) (z : ZMod N) :
    ZMod.castHom hdiv (ZMod k) z = 0 ↔ (t : ZMod N) * z = 0 := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  conv_rhs => rw [← ZMod.natCast_zmod_val z, ← Nat.cast_mul,
    ZMod.natCast_eq_zero_iff]
  conv_rhs => lhs; rw [hN]
  exact (Nat.mul_dvd_mul_iff_left ht).symm

/-- Equality after residue reduction is equality after multiplication by the complementary factor. -/
lemma cast_eq_iff_mul_eq {N k t : ℕ} [NeZero N]
    (ht : 0 < t) (hN : N = t * k) (hdiv : k ∣ N) (x y : ZMod N) :
    ZMod.castHom hdiv (ZMod k) x = ZMod.castHom hdiv (ZMod k) y ↔
      (t : ZMod N) * x = (t : ZMod N) * y := by
  rw [← sub_eq_zero, ← map_sub, cast_eq_zero_iff_mul_eq_zero ht hN hdiv,
    mul_sub, sub_eq_zero]

/-- An involution written as `I + 2 M` has doubled norm `4 (I + M)`. -/
lemma norm_eq_four_mulVec {R : Type*} [CommRing R]
    (T M : Matrix (Fin 2) (Fin 2) R) (hM : T = 1 + (2 : R) • M)
    (v : Fin 2 → R) : (2 : R) • (v + T.mulVec v) =
      (4 : R) • ((1 + M).mulVec v) := by
  rw [hM, add_mulVec, one_mulVec, smul_mulVec, add_mulVec, one_mulVec]
  ext i
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- The involution equation annihilates the idempotence defect by four. -/
lemma four_smul_defect_eq_zero {R : Type*} [CommRing R]
    (T M : Matrix (Fin 2) (Fin 2) R) (hT : T ^ 2 = 1)
    (hM : T = 1 + (2 : R) • M) : (4 : R) • (M * M + M) = 0 := by
  have h : (4 : Matrix (Fin 2) (Fin 2) R) * (M * M + M) = 0 := by
    calc
      _ = T ^ 2 - 1 := by
        rw [hM, Algebra.smul_def, map_ofNat]
        noncomm_ring
      _ = 0 := by rw [hT]; simp
  simpa only [Algebra.smul_def, map_ofNat] using h

/-- The reduced matrix `I + M` is idempotent modulo `2^(n-2)`. -/
lemma reduced_idempotent (n : ℕ) (hn : 2 ≤ n)
    (T M : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n))) (hT : T ^ 2 = 1)
    (hM : T = 1 + (2 : ZMod (2 ^ n)) • M) :
    let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
    (1 + M.map r) * (1 + M.map r) = 1 + M.map r := by
  let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
  change (1 + M.map r) * (1 + M.map r) = 1 + M.map r
  have hN : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show 4 = 2 ^ 2 from rfl, ← pow_add, Nat.add_sub_cancel' hn]
  have hdef : (M * M + M).map r = 0 := by
    ext i j
    apply (cast_eq_zero_iff_mul_eq_zero (by decide : 0 < 4) hN (pow_dvd_pow 2 (Nat.sub_le n 2)) _).mpr
    exact congrFun (congrFun (four_smul_defect_eq_zero T M hT hM) i) j
  have hh : M.map r * M.map r + M.map r = 0 := by
    simpa only [← RingHom.mapMatrix_apply, map_add, map_mul, map_zero] using hdef
  calc
    _ = 1 + M.map r + (M.map r * M.map r + M.map r) := by noncomm_ring
    _ = _ := by rw [hh, add_zero]

/-- Every top vector is annihilated by two. -/
lemma topVector_two_smul (n : ℕ) (hn : 1 ≤ n) (w : BinaryIdempotentPlane.Vec) :
    (2 : ZMod (2 ^ n)) • topVector n w = 0 := by
  ext i
  change 2 * (2 ^ (n - 1) * ((w i).val : ZMod (2 ^ n))) = 0
  rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hn]
  have h : (2 : ZMod (2 ^ n)) ^ n = 0 := by
    exact_mod_cast (ZMod.natCast_eq_zero_iff (2 ^ n) (2 ^ n)).mpr dvd_rfl
  rw [h, zero_mul]

/-- A nonzero binary label gives a nonzero top vector. -/
lemma topVector_ne_zero (n : ℕ) (hn : 1 ≤ n) (w : BinaryIdempotentPlane.Vec)
    (hw : w ≠ 0) : topVector n w ≠ 0 := by
  intro h
  apply hw
  funext i
  have hi := congrFun h i
  change (2 : ZMod (2 ^ n)) ^ (n - 1) * ((w i).val : ZMod (2 ^ n)) = 0 at hi
  have hval : (w i).val < 2 := ZMod.val_lt _
  have hlt : 2 ^ (n - 1) < 2 ^ n := by
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  have hval0 : (w i).val = 0 := by
    by_contra hh
    have hv : (w i).val = 1 := by omega
    rw [hv, Nat.cast_one, mul_one] at hi
    have hd : 2 ^ n ∣ 2 ^ (n - 1) := by
      apply (ZMod.natCast_eq_zero_iff _ _).mp
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hi
    exact (not_le.mpr hlt) (Nat.le_of_dvd (by positivity) hd)
  exact (ZMod.val_eq_zero _).mp hval0

/-- The original norm equation is the pullback of the reduced matrix equation. -/
lemma norm_eq_top_iff_reduced (n : ℕ) (hn : 3 ≤ n)
    (T M : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n)))
    (hM : T = 1 + (2 : ZMod (2 ^ n)) • M)
    (w : BinaryIdempotentPlane.Vec) (v : Fin 2 → ZMod (2 ^ n)) :
    let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
    (2 : ZMod (2 ^ n)) • (v + T.mulVec v) = topVector n w ↔
      (1 + M.map r).mulVec (r ∘ v) = topVector (n - 2) w := by
  let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
  change _ ↔ (1 + M.map r).mulVec (r ∘ v) = _
  let u : Fin 2 → ZMod (2 ^ n) := fun i => 2 ^ (n - 3) * ((w i).val : ZMod (2 ^ n))
  have hN : 2 ^ n = 4 * 2 ^ (n - 2) := by
    rw [show 4 = 2 ^ 2 from rfl, ← pow_add]
    congr 1; omega
  have htop : topVector n w = (4 : ZMod (2 ^ n)) • u := by
    ext i
    change (2 : ZMod (2 ^ n)) ^ (n - 1) * ((w i).val : ZMod (2 ^ n)) =
      4 * (2 ^ (n - 3) * ((w i).val : ZMod (2 ^ n)))
    rw [← mul_assoc, show (4 : ZMod (2 ^ n)) = 2 ^ 2 from by norm_num, ← pow_add]
    congr 2; omega
  have hmaptop : r ∘ u = topVector (n - 2) w := by
    funext i
    change r (2 ^ (n - 3) * ((w i).val : ZMod (2 ^ n))) = _
    simp only [map_mul, map_pow, map_ofNat, map_natCast, topVector]
    congr 2
  have hmap : r ∘ (1 + M).mulVec v = (1 + M.map r).mulVec (r ∘ v) := by
    funext i
    have hm : (1 + M).map r = 1 + M.map r := by
      exact (r.mapMatrix.map_add 1 M).trans (by rw [map_one]; rfl)
    exact (r.map_mulVec (1 + M) v i).trans
      (congrArg (fun A => (A.mulVec (r ∘ v)) i) hm)
  rw [norm_eq_four_mulVec T M hM, htop, ← hmaptop, ← hmap]
  simp only [funext_iff, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  exact forall_congr' fun i =>
    (cast_eq_iff_mul_eq (by decide : 0 < 4) hN
      (pow_dvd_pow 2 (Nat.sub_le n 2)) _ _).symm

/-- A residue nonzero modulo two is a unit modulo a positive power of two. -/
lemma binary_cast_detects_units (n : ℕ) (hn : 1 ≤ n)
    (h2 : 2 ∣ 2 ^ n) (x : ZMod (2 ^ n))
    (hx : ZMod.castHom h2 (ZMod 2) x ≠ 0) : IsUnit x := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, Ne, ZMod.natCast_eq_zero_iff] at hx
  have h := (ZMod.isUnit_natCast_iff_not_dvd_pow Nat.prime_two (by omega : 0 < n)).mpr hx
  simpa only [ZMod.natCast_zmod_val] using h

/-- Reduction of `I + M` through the smaller residue ring preserves its binary matrix. -/
lemma reduced_binary_eq (n : ℕ)
    (M : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n)))
    (h2 : 2 ∣ 2 ^ n) (h2' : 2 ∣ 2 ^ (n - 2)) :
    let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
    (1 + M.map r).map (ZMod.castHom h2' (ZMod 2)) =
      1 + M.map (ZMod.castHom h2 (ZMod 2)) := by
  intro r
  let s := ZMod.castHom h2' (ZMod 2)
  change s.mapMatrix (1 + r.mapMatrix M) = 1 + _
  rw [map_add, map_one]
  congr 1
  ext i j
  change (s.comp r) (M i j) = _
  rw [show s.comp r = ZMod.castHom h2 (ZMod 2) from ZMod.castHom_comp h2' _]
  rfl

/-- The binary reduction of `I + M` is idempotent. -/
lemma binary_idempotent (n : ℕ) (hn : 3 ≤ n)
    (T M : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ n))) (hT : T ^ 2 = 1)
    (hM : T = 1 + (2 : ZMod (2 ^ n)) • M) (h2 : 2 ∣ 2 ^ n) :
    let Q := 1 + M.map (ZMod.castHom h2 (ZMod 2))
    Q * Q = Q := by
  let r := ZMod.castHom (pow_dvd_pow 2 (Nat.sub_le n 2)) (ZMod (2 ^ (n - 2)))
  have h2' : 2 ∣ 2 ^ (n - 2) := dvd_pow_self 2 (by omega)
  let s := ZMod.castHom h2' (ZMod 2)
  have hid := congrArg s.mapMatrix (reduced_idempotent n (by omega) T M hT hM)
  simp only [map_mul] at hid
  change (1 + M.map r).map s * (1 + M.map r).map s = (1 + M.map r).map s at hid
  have heq : (1 + M.map r).map s = 1 + M.map (ZMod.castHom h2 (ZMod 2)) :=
    reduced_binary_eq n M h2 h2'
  rw [heq] at hid
  exact hid

end TwoPowerNorm
