module

public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.BinaryModel
public import Theory.GroupTheory.PGroup.AnisotropicFactors

/-!
# Consequences of marked binary normal forms

Given an actual multiplicative normal form carrying the two intrinsic factors
to their binary planes, the first-factor centralizer condition makes the
polar pairing with that plane nondegenerate. An isomorphism carries literal
square fibers to model fibers, each of which has four central lifts. Thus
balanced square fibers in the original group give balanced quadratic fibers.

`MarkedCoordinates` is an intermediate mathematical witness. This module
proves consequences of that witness; it does not assert its existence from
the factor data. That construction is required before recognition applies.
Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3
and the proof of 46.14, printed pp.29–30,251,257–258.
-/

@[expose] public section
namespace Theory.GroupTheory.AnisotropicRecognition

/-- A marked normal form; its existence must be proved from the factor data. -/
structure MarkedCoordinates {K : Type*} [Group K] (F : AnisotropicFactors K) where
  matrix : Cross
  equiv : K ≃* Word matrix
  map_z : equiv (F.z : K) = centralWord matrix cz
  map_u : equiv (F.u : K) = centralWord matrix cu
  first_mem : ∀ x : K, x ∈ F.A ↔ (equiv x).vector.2 = 0
  second_mem : ∀ x : K, x ∈ F.B ↔ (equiv x).vector.1 = 0

variable {K : Type*} [Group K] (F : AnisotropicFactors K) (C : MarkedCoordinates F)

theorem firstNondegenerate_of_coordinates : FirstNondegenerate C.matrix := by
  intro v ha hb
  have hx : C.equiv.symm (lift C.matrix v) ∈ Subgroup.center K := by
    rw [← F.centralizer_A]
    intro a haA
    apply C.equiv.injective
    simp only [map_mul, C.equiv.apply_symm_apply]
    apply (commute_iff _ _).mpr
    exact (commute_firstPlane C.matrix v ha hb _ ((C.first_mem a).mp haA)).symm
  have hxA : C.equiv.symm (lift C.matrix v) ∈ F.A :=
    (show Subgroup.center K ≤ F.A from F.inf_eq ▸ inf_le_left) hx
  have hxB : C.equiv.symm (lift C.matrix v) ∈ F.B :=
    (show Subgroup.center K ≤ F.B from F.inf_eq ▸ inf_le_right) hx
  have hv2 := (C.first_mem _).mp hxA
  have hv1 := (C.second_mem _).mp hxB
  simp only [C.equiv.apply_symm_apply] at hv1 hv2
  exact Prod.ext hv1 hv2

theorem map_zu : C.equiv ((F.z * F.u : Subgroup.center K) : K) =
    centralWord C.matrix czu := by
  change C.equiv ((F.z : K) * (F.u : K)) = _
  rw [map_mul, C.map_z, C.map_u]
  apply Word.ext <;> simp [centralWord, cz, cu, czu, cocycle]

theorem zu_ne_one : F.z * F.u ≠ 1 := by
  have hz : F.z * F.z = 1 := by
    let := F.center_elementary
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (Subgroup.center K)) F.z
  intro h
  exact F.distinct (mul_left_cancel (h.trans hz.symm)).symm

theorem fiberCount_eq_of_squareFiber_eq {x y : K} {c d : Central}
    (hx : C.equiv x = centralWord C.matrix c)
    (hy : C.equiv y = centralWord C.matrix d)
    (h : Nat.card {a : K // a ^ 2 = x} = Nat.card {a : K // a ^ 2 = y}) :
    fiberCount C.matrix c = fiberCount C.matrix d := by
  have he : 4 * fiberCount C.matrix c = 4 * fiberCount C.matrix d := by
    rw [← squareFiber_card, ← squareFiber_card, ← hx, ← hy,
      ← squareFiber_card_eq C.equiv x, ← squareFiber_card_eq C.equiv y]
    exact h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 4) he

theorem balanced_of_coordinates
    (h : ∀ c d : Subgroup.center K, c ≠ 1 → d ≠ 1 →
      Nat.card {x : K // x ^ 2 = (c : K)} = Nat.card {x : K // x ^ 2 = (d : K)}) :
    Balanced C.matrix := by
  constructor
  · exact fiberCount_eq_of_squareFiber_eq F C C.map_z C.map_u
      (h F.z F.u F.z_ne_one F.u_ne_one)
  · exact fiberCount_eq_of_squareFiber_eq F C C.map_u (map_zu F C)
      (h F.u (F.z * F.u) F.u_ne_one (zu_ne_one F))

end Theory.GroupTheory.AnisotropicRecognition
