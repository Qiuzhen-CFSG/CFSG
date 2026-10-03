module

public import Theory.LinearAlgebra.Matrix.TwoPowerNormReduction
public import Theory.LinearAlgebra.Matrix.IdempotentLift
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Fibers of idempotent planes over two-power residue rings

An idempotent matrix over `ZMod (2^m)` is determined up to invertible
intertwining by its binary reduction. The six nontrivial binary projections
have explicit idempotent lifts with kernels parametrized by one residue-ring
coordinate. Thus every nontrivial idempotent has a kernel of size `2^m`.

An idempotent's fiber over a vector is nonempty exactly when it fixes that
vector; translation then identifies the fiber with its kernel. For a top
two-torsion vector, fixing it is equivalent to fixing its binary label.
Together with rigidity of the zero and identity reductions, this gives the
binary weighted fiber formula.

Source context: the elementary homocyclic norm calculation in the
MacWilliams–Sah bound quoted by Janko–Thompson, Math. Z. 113 (1970), 1.1,
printed p.385. The lifting argument uses the elementary invertible
intertwiner constructed in `Theory.LinearAlgebra.Matrix.IdempotentLift`.
-/

public section

open Matrix
namespace TwoPowerNorm

/-- The six binary rank-one projections, lifted over any coefficient ring. -/
private def standard {R : Type*} [Ring R] (k : Fin 6) : Matrix (Fin 2) (Fin 2) R :=
  ![!![1, 0; 0, 0], !![1, 1; 0, 0], !![1, 0; 1, 0],
    !![0, 0; 0, 1], !![0, 0; 1, 1], !![0, 1; 0, 1]] k

private def param {R : Type*} [Ring R] (k : Fin 6) (x : R) : Fin 2 → R :=
  ![![0, x], ![-x, x], ![0, x], ![x, 0], ![x, -x], ![x, 0]] k

private def coord {R : Type*} (k : Fin 6) (v : Fin 2 → R) : R :=
  if k.val < 3 then v 1 else v 0

private lemma standard_idempotent {R : Type*} [CommRing R] (k : Fin 6) :
    (standard k : Matrix (Fin 2) (Fin 2) R) * standard k = standard k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [standard, Matrix.mul_apply, Fin.sum_univ_two]

private lemma map_standard {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (k : Fin 6) : (standard k).map f = standard k := by
  fin_cases k <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [standard]

set_option maxRecDepth 8192 in
private lemma binary_cases : ∀ Q : BinaryIdempotentPlane.Mat,
    Q * Q = Q → Q ≠ 0 → Q ≠ 1 → ∃ k : Fin 6, Q = standard k := by
  decide

private def standardKernelEquiv {R : Type*} [CommRing R] (k : Fin 6) :
    {u : Fin 2 → R // (standard k).mulVec u = 0} ≃ R where
  toFun u := coord k u
  invFun x := ⟨param k x, by
    fin_cases k <;> ext i <;> fin_cases i <;>
      simp [standard, param, mulVec, dotProduct, Fin.sum_univ_two]⟩
  left_inv u := by
    apply Subtype.ext
    have h0 := congrFun u.property 0
    have h1 := congrFun u.property 1
    fin_cases k <;> ext i <;> fin_cases i <;>
      simp_all [standard, param, coord, mulVec, dotProduct, Fin.sum_univ_two]
    · linear_combination -h0
    · linear_combination -h1
  right_inv x := by fin_cases k <;> simp [coord, param]

private def unitVecEquiv {R : Type*} [CommRing R]
    (U : (Matrix (Fin 2) (Fin 2) R)ˣ) : (Fin 2 → R) ≃ (Fin 2 → R) where
  toFun := (U : Matrix (Fin 2) (Fin 2) R).mulVec
  invFun := (↑U⁻¹ : Matrix (Fin 2) (Fin 2) R).mulVec
  left_inv v := by rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
  right_inv v := by rw [mulVec_mulVec, Units.mul_inv, one_mulVec]

private lemma kernel_card_intertwiner {R : Type*} [CommRing R]
    (B P : Matrix (Fin 2) (Fin 2) R) (U : (Matrix (Fin 2) (Fin 2) R)ˣ)
    (hU : B * (U : Matrix (Fin 2) (Fin 2) R) = (U : Matrix (Fin 2) (Fin 2) R) * P) :
    Nat.card {u : Fin 2 → R // B.mulVec u = 0} =
      Nat.card {u : Fin 2 → R // P.mulVec u = 0} := by
  apply Eq.symm
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (unitVecEquiv U)
  intro u
  have hh : B.mulVec (unitVecEquiv U u) = unitVecEquiv U (P.mulVec u) := by
    change B.mulVec ((U : Matrix (Fin 2) (Fin 2) R).mulVec u) =
      (U : Matrix (Fin 2) (Fin 2) R).mulVec (P.mulVec u)
    rw [mulVec_mulVec, hU, ← mulVec_mulVec]
  rw [hh]
  have hz : unitVecEquiv U 0 = 0 := by
    change (U : Matrix (Fin 2) (Fin 2) R).mulVec 0 = 0
    exact mulVec_zero _
  exact ⟨fun h => by rw [h, hz], fun h => (unitVecEquiv U).injective (h.trans hz.symm)⟩

private def fixedFiberEquivKernel {R : Type*} [CommRing R]
    (B : Matrix (Fin 2) (Fin 2) R) (y : Fin 2 → R) (hy : B.mulVec y = y) :
    {u : Fin 2 → R // B.mulVec u = y} ≃ {u : Fin 2 → R // B.mulVec u = 0} where
  toFun u := ⟨u - y, by rw [mulVec_sub, u.property, hy, sub_self]⟩
  invFun u := ⟨u + y, by rw [mulVec_add, u.property, hy, zero_add]⟩
  left_inv u := by apply Subtype.ext; exact sub_add_cancel _ _
  right_inv u := by apply Subtype.ext; exact add_sub_cancel_right _ _

/-- A matrix fixes a top two-torsion vector precisely when its binary
reduction fixes the vector’s label. -/
lemma fixes_topVector_iff (m : ℕ) (hm : 1 ≤ m)
    (B : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ m)))
    (w : BinaryIdempotentPlane.Vec) (h2 : 2 ∣ 2 ^ m) :
    B.mulVec (topVector m w) = topVector m w ↔
      (B.map (ZMod.castHom h2 (ZMod 2))).mulVec w = w := by
  let r := ZMod.castHom h2 (ZMod 2)
  let v : Fin 2 → ZMod (2 ^ m) := fun i => ((w i).val : ZMod (2 ^ m))
  have htop : topVector m w = (2 : ZMod (2 ^ m)) ^ (m - 1) • v := by
    ext i
    exact topVector_apply m w i
  have hv : r ∘ v = w := by
    funext i
    change r ((w i).val : ZMod (2 ^ m)) = w i
    rw [map_natCast, ZMod.natCast_zmod_val]
  have hmap : r ∘ B.mulVec v = (B.map r).mulVec w := by
    funext i
    exact (r.map_mulVec B v i).trans (congrArg (fun u => (B.map r).mulVec u i) hv)
  have hN : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  rw [htop, mulVec_smul]
  change _ ↔ (B.map r).mulVec w = w
  rw [← hmap, ← hv]
  simp only [funext_iff, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  apply forall_congr'
  intro i
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    (cast_eq_iff_mul_eq (by positivity : 0 < 2 ^ (m - 1)) hN h2
      (B.mulVec v i) (v i)).symm

/-- An idempotent with nontrivial binary reduction has a kernel of size `2^m`. -/
lemma idempotent_nontrivial_kernel_card (m : ℕ) (hm : 1 ≤ m)
    (B : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ m))) (hB : B * B = B)
    (h2 : 2 ∣ 2 ^ m) (h0 : B.map (ZMod.castHom h2 (ZMod 2)) ≠ 0)
    (h1 : B.map (ZMod.castHom h2 (ZMod 2)) ≠ 1) :
    Nat.card {u : Fin 2 → ZMod (2 ^ m) // B.mulVec u = 0} = 2 ^ m := by
  let r := ZMod.castHom h2 (ZMod 2)
  have hrB : B.map r * B.map r = B.map r := by rw [← Matrix.map_mul, hB]
  obtain ⟨k, hk⟩ := binary_cases (B.map r) hrB h0 h1
  obtain ⟨U, hU, _⟩ := exists_unit_intertwiner_of_idempotent_map_eq r
    (binary_cast_detects_units m hm h2) B (standard k) hB
    (standard_idempotent k) (hk.trans (map_standard r k).symm)
  exact (kernel_card_intertwiner B (standard k) U hU).trans
    ((Nat.card_congr (standardKernelEquiv k)).trans (Nat.card_zmod _))

private lemma idempotent_eq_zero_of_map_eq_zero {R K : Type*}
    [CommRing R] [CommRing K] [Nontrivial K]
    (r : R →+* K) (hr : ∀ x, r x ≠ 0 → IsUnit x)
    (B : Matrix (Fin 2) (Fin 2) R) (hB : B * B = B)
    (h0 : B.map r = 0) : B = 0 := by
  obtain ⟨U, hU, _⟩ := exists_unit_intertwiner_of_idempotent_map_eq r hr B 0 hB
    (by simp [IsIdempotentElem]) (by simpa using h0)
  have hh := congrArg (fun A => A * (↑U⁻¹ : Matrix (Fin 2) (Fin 2) R)) hU
  simpa only [mul_zero, zero_mul, mul_assoc, Units.mul_inv, mul_one] using hh

private lemma idempotent_eq_one_of_map_eq_one {R K : Type*}
    [CommRing R] [CommRing K] [Nontrivial K]
    (r : R →+* K) (hr : ∀ x, r x ≠ 0 → IsUnit x)
    (B : Matrix (Fin 2) (Fin 2) R) (hB : B * B = B)
    (h1 : B.map r = 1) : B = 1 := by
  obtain ⟨U, hU, _⟩ := exists_unit_intertwiner_of_idempotent_map_eq r hr B 1 hB
    (by simp [IsIdempotentElem]) (by simpa using h1)
  have hh := congrArg (fun A => A * (↑U⁻¹ : Matrix (Fin 2) (Fin 2) R)) hU
  simpa only [mul_one, mul_assoc, Units.mul_inv] using hh

/-- Fibers over nonzero top two-torsion vectors have the binary projection
weights: zero for the zero reduction, one for the identity, and `2^m` for
a nontrivial projection fixing the binary label. -/
lemma idempotent_fiber_card (m : ℕ) (hm : 1 ≤ m)
    (B : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ m))) (hB : B * B = B)
    (w : BinaryIdempotentPlane.Vec) (hw : w ≠ 0) (h2 : 2 ∣ 2 ^ m) :
    Nat.card {u : Fin 2 → ZMod (2 ^ m) // B.mulVec u = topVector m w} =
      BinaryIdempotentPlane.weight 1 (2 ^ m) (B.map (ZMod.castHom h2 (ZMod 2))) w := by
  classical
  let r := ZMod.castHom h2 (ZMod 2)
  change _ = BinaryIdempotentPlane.weight 1 (2 ^ m) (B.map r) w
  rw [BinaryIdempotentPlane.weight_eq]
  by_cases h0 : B.map r = 0
  · rw [if_pos h0]
    have hB0 := idempotent_eq_zero_of_map_eq_zero r
      (binary_cast_detects_units m hm h2) B hB h0
    have : IsEmpty {u : Fin 2 → ZMod (2 ^ m) // B.mulVec u = topVector m w} :=
      ⟨fun u => topVector_ne_zero m hm w hw (by simpa [hB0] using u.property.symm)⟩
    simp
  rw [if_neg h0]
  by_cases h1 : B.map r = 1
  · rw [if_pos h1]
    have hB1 := idempotent_eq_one_of_map_eq_one r
      (binary_cast_detects_units m hm h2) B hB h1
    subst B
    simp
  rw [if_neg h1]
  by_cases hwfix : (B.map r).mulVec w = w
  · rw [if_pos hwfix]
    have hfix := (fixes_topVector_iff m hm B w h2).mpr hwfix
    exact (Nat.card_congr (fixedFiberEquivKernel B (topVector m w) hfix)).trans
      (idempotent_nontrivial_kernel_card m hm B hB h2 h0 h1)
  · rw [if_neg hwfix]
    have hnfix := mt (fixes_topVector_iff m hm B w h2).mp hwfix
    have : IsEmpty {u : Fin 2 → ZMod (2 ^ m) // B.mulVec u = topVector m w} :=
      ⟨fun u => hnfix (by rw [← u.property, mulVec_mulVec, hB])⟩
    simp

end TwoPowerNorm
