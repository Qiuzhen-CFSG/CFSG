module

public import Theory.LinearAlgebra.Matrix.BinaryIdempotentPlane
public import Theory.GroupTheory.PGroup.HomocyclicNormalizedBinaryAction
public import Theory.LinearAlgebra.Matrix.TwoPowerNormFibers
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.Logic.Equiv.Prod

/-!+# Summing homocyclic automorphism norm fibers

The four-element binary idempotent image of a homocyclic action has two
different weighted sums on nonzero binary vectors. This module transfers a
single-automorphism fiber calculation to the fibers over the whole action.
The product subtype is decomposed into a sigma type of individual fibers.

Source context: the homocyclic case of the MacWilliams–Sah bound, quoted in
Janko–Thompson, Math. Z. 113 (1970), 1.1, printed p.385. The binary matrix
calculation is in `Theory.LinearAlgebra.Matrix.BinaryIdempotentPlane`.
-/

namespace HomocyclicFourNormProfile

open BinaryIdempotentPlane

/-- A binary profile with positive line multiplicity distinguishes two
nonidentity involutions by their total action-norm fiber cardinalities. -/
public theorem exists_ne_norm_fiber_card_of_binary_profile
    {D : Type*} [Group D] [Finite D] (A : Subgroup (MulAut D)) [Finite A]
    (f : A →* Multiplicative Mat) (hi : Function.Injective f)
    (hc : Nat.card A = 4) (hp : ∀ a, (f a).toAdd * (f a).toAdd = (f a).toAdd)
    (j : Vec → D) (hj : ∀ w, w ≠ 0 → (j w) ^ 2 = 1 ∧ j w ≠ 1)
    (base line : ℕ) (hline : 0 < line)
    (hprofile : ∀ (a : A) (w : Vec), w ≠ 0 →
      Nat.card {d : D // (d * ((a : MulAut D) d)) ^ 2 = j w} =
        weight base line (1 + (f a).toAdd) w) :
    ∃ x y : D, x ^ 2 = 1 ∧ x ≠ 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
      Nat.card {t : A × D // (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = x} ≠
      Nat.card {t : A × D // (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = y} := by
  classical
  let : Fintype A := Fintype.ofFinite A
  obtain ⟨w, z, hw, hz, hwsum, hzsum⟩ := exists_weight_sums f hi hc hp base line
  have hcard (v : Vec) (hv : v ≠ 0) :
      Nat.card {t : A × D // (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = j v} =
        ∑ a, weight base line (1 + (f a).toAdd) v := by
    rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
      (fun (a : A) (d : D) => (d * ((a : MulAut D) d)) ^ 2 = j v)), Nat.card_sigma]
    exact Finset.sum_congr rfl fun a _ => hprofile a v hv
  refine ⟨j w, j z, (hj w hw).1, (hj w hw).2, (hj z hz).1, (hj z hz).2, ?_⟩
  rw [hcard w hw, hcard z hz, hwsum, hzsum]
  omega

/-- The norm fibers of a faithful elementary four action on a rank-two
homocyclic group are not all equal. -/
public theorem exists_ne_norm_fiber_card_of_homocyclic
    {D : Type*} [Group D] [Finite D] [IsMulCommutative D]
    (n : ℕ) (hn : 3 ≤ n)
    (e : D ≃* (Multiplicative (ZMod (2 ^ n)) ×
      Multiplicative (ZMod (2 ^ n))))
    (A : Subgroup (MulAut D)) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 4)
    (hfix : ∀ a ∈ A, ∀ d : D, d ^ 2 = 1 → a d = d)
    (hfaith : ∀ a ∈ A, (∀ d : D, d ^ 4 = 1 → a d = d) → a = 1) :
    ∃ x y : D, x ^ 2 = 1 ∧ x ≠ 1 ∧ y ^ 2 = 1 ∧ y ≠ 1 ∧
      Nat.card {t : A × D // (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = x} ≠
      Nat.card {t : A × D // (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = y} := by
  classical
  obtain ⟨E, T, f, hfi, hfp, hcoord, hhalf⟩ :=
    HomocyclicNormalizedBinaryAction.exists_compatible_actions
      n hn e A hfix hfaith
  let j : BinaryIdempotentPlane.Vec → D := fun w =>
    E.symm (Multiplicative.ofAdd (TwoPowerNorm.topVector n w))
  have hj (w : BinaryIdempotentPlane.Vec) (hw : w ≠ 0) :
      (j w) ^ 2 = 1 ∧ j w ≠ 1 := by
    refine ⟨?_, ?_⟩
    · apply E.injective
      rw [map_pow, E.apply_symm_apply, map_one]
      change Multiplicative.ofAdd ((2 : ℕ) • TwoPowerNorm.topVector n w) =
        Multiplicative.ofAdd 0
      have hz : (2 : ℕ) • TwoPowerNorm.topVector n w = 0 := by
        funext i
        simpa only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] using
          congrFun (TwoPowerNorm.topVector_two_smul n (by omega) w) i
      rw [hz]
    · intro h
      have hh := congrArg (fun d : D => (E d).toAdd) h
      apply TwoPowerNorm.topVector_ne_zero n (by omega) w hw
      simpa [j] using hh
  have hprofile (a : A) (w : BinaryIdempotentPlane.Vec) (hw : w ≠ 0) :
      Nat.card {d : D // (d * ((a : MulAut D) d)) ^ 2 = j w} =
        BinaryIdempotentPlane.weight 16 (2 ^ (n + 2)) (1 + (f a).toAdd) w := by
    obtain ⟨M, hM, hMred⟩ := hhalf a
    have ha : a ^ 2 = 1 := by
      apply Subtype.ext
      exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := A)
        (a : MulAut D) a.property
    have hTa : (T a) ^ 2 = 1 := by
      simpa [pow_two] using congrArg T ha
    let F : D ≃ (Fin 2 → ZMod (2 ^ n)) :=
      E.toEquiv.trans Multiplicative.ofAdd.symm
    let q : (Fin 2 → ZMod (2 ^ n)) → Prop := fun v =>
      (2 : ZMod (2 ^ n)) • (v + (T a).mulVec v) =
        TwoPowerNorm.topVector n w
    have hjE : E (j w) = Multiplicative.ofAdd (TwoPowerNorm.topVector n w) := by
      simp [j]
    have hiff (d : D) :
        ((d * ((a : MulAut D) d)) ^ 2 = j w) ↔ q (F d) := by
      change ((d * ((a : MulAut D) d)) ^ 2 = j w) ↔
        (2 : ZMod (2 ^ n)) •
          ((E d).toAdd + (T a).mulVec (E d).toAdd) =
            TwoPowerNorm.topVector n w
      constructor
      · intro h
        have he := congrArg (fun q : D => (E q).toAdd) h
        rw [map_pow, map_mul, toAdd_pow, toAdd_mul, hcoord a d] at he
        rw [hjE] at he
        ext i
        have hi := congrFun he i
        change (2 • ((E d).toAdd + (T a).mulVec (E d).toAdd)) i =
          TwoPowerNorm.topVector n w i at hi
        simpa only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] using hi
      · intro h
        apply E.injective
        rw [map_pow, map_mul]
        apply Multiplicative.ofAdd.injective
        change ((E d * E ((a : MulAut D) d)) ^ 2).toAdd =
          (E (j w)).toAdd
        rw [toAdd_pow, toAdd_mul, hcoord a d, hjE]
        change (2 : ℕ) • ((E d).toAdd + (T a).mulVec (E d).toAdd) =
          TwoPowerNorm.topVector n w
        ext i
        have hi := congrFun h i
        simpa only [Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat] using hi
    have hcard := Nat.card_congr (Equiv.subtypeEquiv F hiff)
    rw [hcard]
    change Nat.card {v : Fin 2 → ZMod (2 ^ n) // q v} = _
    rw [TwoPowerNorm.norm_fiber_card n hn (T a) M hTa hM w hw
      (show 2 ∣ 2 ^ n from dvd_trans (by decide : 2 ∣ 8) (pow_dvd_pow 2 hn))]
    simp [hMred]
  apply exists_ne_norm_fiber_card_of_binary_profile A f hfi hA hfp j hj
    16 (2 ^ (n + 2)) (by positivity)
  intro a w hw
  exact hprofile a w hw

end HomocyclicFourNormProfile
