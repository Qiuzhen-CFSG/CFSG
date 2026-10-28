module

public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Tactic.Ring

/-!
# Scalar centralizers over prime-power rings

A matrix whose reduction is nonscalar has centralizer spanned by itself and
one. If two reductions do not commute, their common centralizer is scalar:
one entry of their commutator is a unit, forcing the second coefficient to vanish.
This works over every commutative ring with a field reduction detecting units.

For rank-two homocyclic groups, automorphisms are matrices over Z/p^a.
Reduction equal to one fixes the full subgroup of elements killed by p.
The coordinate equivalence and this compatibility retain every positive exponent.
These calculations support Aschbacher--Smith A.3.6(4), pp.43--45, and the
outer-group argument in 11.4.3, p.778.
-/

public noncomputable section
namespace HomocyclicCentralizer
open Matrix
variable {R F : Type*} [CommRing R] [Field F]

private theorem linear_of_upper_unit
    (A B : Matrix (Fin 2) (Fin 2) R) (hA : IsUnit (A 0 1)) (hAB : A * B = B * A) :
    ∃ a b : R, B = a • 1 + b • A := by
  obtain ⟨u, hu⟩ := hA
  let z : R := ↑u⁻¹
  have hz : A 0 1 * z = 1 := by rw [← hu]; exact u.val_inv
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 0) hAB
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) hAB
  simp only [mul_apply, Fin.sum_univ_two] at h00 h01
  refine ⟨B 0 0 - (B 0 1 * z) * A 0 0, B 0 1 * z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · linear_combination -B 0 1 * hz
  · linear_combination z * h00 - B 1 0 * hz
  · linear_combination z * h01 - (B 1 1 - B 0 0) * hz

private theorem linear_of_diag_unit
    (A B : Matrix (Fin 2) (Fin 2) R) (hA : IsUnit (A 0 0 - A 1 1)) (hAB : A * B = B * A) :
    ∃ a b : R, B = a • 1 + b • A := by
  obtain ⟨u, hu⟩ := hA
  let z : R := ↑u⁻¹
  have hz : (A 0 0 - A 1 1) * z = 1 := by rw [← hu]; exact u.val_inv
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 0 1) hAB
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) hAB
  simp only [mul_apply, Fin.sum_univ_two] at h01 h10
  refine ⟨B 0 0 - ((B 0 0 - B 1 1) * z) * A 0 0, (B 0 0 - B 1 1) * z, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  · linear_combination z * h01 - B 0 1 * hz
  · linear_combination -z * h10 - B 1 0 * hz
  · linear_combination (B 0 0 - B 1 1) * hz

theorem linear_of_nonscalar_reduction
    (r : R →+* F) (hr : ∀ x, r x ≠ 0 → IsUnit x)
    (A B : Matrix (Fin 2) (Fin 2) R)
    (hA : ¬ ∃ a : F, r.mapMatrix A = a • 1) (hAB : A * B = B * A) :
    ∃ a b : R, B = a • 1 + b • A := by
  by_cases hu : r (A 0 1) = 0
  · by_cases hl : r (A 1 0) = 0
    · have hd : r (A 0 0 - A 1 1) ≠ 0 := by
        intro he
        have heq : r (A 0 0) = r (A 1 1) := sub_eq_zero.mp (by simpa only [map_sub] using he)
        apply hA
        refine ⟨r (A 0 0), ?_⟩
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hu, hl, heq]
      exact linear_of_diag_unit A B (hr _ hd) hAB
    · obtain ⟨a, b, hh⟩ := linear_of_upper_unit A.transpose B.transpose (hr _ hl)
        (by simpa only [transpose_mul] using congrArg Matrix.transpose hAB.symm)
      exact ⟨a, b, by simpa using congrArg Matrix.transpose hh⟩
  · exact linear_of_upper_unit A B (hr _ hu) hAB

theorem scalar_of_centralizes_noncommuting_reduction
    (r : R →+* F) (hr : ∀ x, r x ≠ 0 → IsUnit x)
    (A B C : Matrix (Fin 2) (Fin 2) R)
    (hn : r.mapMatrix A * r.mapMatrix B ≠ r.mapMatrix B * r.mapMatrix A)
    (hAC : A * C = C * A) (hBC : B * C = C * B) : ∃ a : R, C = a • 1 := by
  have hA : ¬ ∃ a : F, r.mapMatrix A = a • 1 := by
    rintro ⟨a, ha⟩
    apply hn
    rw [ha, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  obtain ⟨a, b, he⟩ := linear_of_nonscalar_reduction r hr A C hA hAC
  have hcomm : b • (A * B - B * A) = 0 := by
    rw [he] at hBC
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, one_mul] at hBC
    exact (smul_sub _ _ _).trans (sub_eq_zero.mpr (add_left_cancel hBC.symm))
  have hn' : ∃ i j, r ((A * B - B * A) i j) ≠ 0 := by
    by_contra! hz
    apply hn
    apply sub_eq_zero.mp
    rw [← map_mul, ← map_mul, ← map_sub]
    ext i j
    exact hz i j
  obtain ⟨i, j, hij⟩ := hn'
  have hb : b = 0 := (hr _ hij).mul_left_eq_zero.mp (congrFun (congrFun hcomm i) j)
  exact ⟨a, by simpa only [hb, zero_smul, add_zero] using he⟩


open Subgroup

theorem centralizer_le_center_of_noncommutative_reduction
    (r : R →+* F) (hr : ∀ x, r x ≠ 0 → IsUnit x)
    (U : Subgroup (GeneralLinearGroup (Fin 2) R))
    (hn : ¬ IsMulCommutative (U.map (GeneralLinearGroup.map r))) :
    centralizer (U : Set (GeneralLinearGroup (Fin 2) R)) ≤
      center (GeneralLinearGroup (Fin 2) R) := by
  have hex : ∃ a b : U,
      r.mapMatrix a.val.val * r.mapMatrix b.val.val ≠
        r.mapMatrix b.val.val * r.mapMatrix a.val.val := by
    by_contra! hh
    apply hn
    apply IsMulCommutative.of_comm
    rintro ⟨a, x, hx, rfl⟩ ⟨b, y, hy, rfl⟩
    apply Subtype.ext
    apply Units.ext
    exact hh ⟨x, hx⟩ ⟨y, hy⟩
  obtain ⟨a, b, hab⟩ := hex
  intro c hc
  obtain ⟨k, hk⟩ := scalar_of_centralizes_noncommuting_reduction r hr
    a.val.val b.val.val c.val hab
    (congrArg Units.val (hc a.val a.property))
    (congrArg Units.val (hc b.val b.property))
  apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
  refine ⟨k, ?_⟩
  rw [hk]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

theorem unit_of_primePower_reduction_ne_zero {p a : ℕ} [Fact p.Prime]
    (ha : 1 ≤ a) (x : ZMod (p ^ a))
    (hx : ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt ha)) (ZMod p) x ≠ 0) : IsUnit x := by
  have hval : ¬ p ∣ x.val := by
    intro hd
    apply hx
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
    exact hd
  have hh := (ZMod.isUnit_natCast_iff_not_dvd_pow (a := x.val)
    (Fact.out : p.Prime) (show 0 < a from ha)).mpr hval
  rwa [ZMod.natCast_zmod_val] at hh


open scoped MatrixGroups

def homocyclicAutEquiv {P : Type*} [Group P] {N : ℕ}
    (e : P ≃* Multiplicative (Fin 2 → ZMod N)) :
    MulAut P ≃* GL (Fin 2) (ZMod N) := by
  let tag := AddEquiv.additiveMultiplicative (Fin 2 → ZMod N)
  let al : MulAut (Multiplicative (Fin 2 → ZMod N)) ≃*
      ((Fin 2 → ZMod N) ≃ₗ[ZMod N] (Fin 2 → ZMod N)) :=
    { toFun := fun a =>
        { tag.symm.trans (a.toAdditive.trans tag) with
          map_smul' := ZMod.map_smul (tag.symm.trans (a.toAdditive.trans tag)) }
      invFun := fun a => MulEquiv.toAdditive.symm (tag.trans (a.toAddEquiv.trans tag.symm))
      left_inv := by intro a; ext; rfl
      right_inv := by intro a; ext; rfl
      map_mul' := by intros; ext; rfl }
  exact (MulAut.congr e).trans (al.trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod N) (Fin 2 → ZMod N)).symm.trans
      GeneralLinearGroup.toLin.symm))

theorem homocyclicAutEquiv_apply {P : Type*} [Group P] {N : ℕ}
    (e : P ≃* Multiplicative (Fin 2 → ZMod N)) (a : MulAut P) (x : P) :
    (e (a x)).toAdd = (homocyclicAutEquiv e a).val *ᵥ (e x).toAdd := by
  have hh := GeneralLinearGroup.toLin_apply (homocyclicAutEquiv e a) (e x).toAdd
  simpa [homocyclicAutEquiv, MulAut.congr_apply, GeneralLinearGroup.toLin,
    LinearMap.GeneralLinearGroup.generalLinearEquiv] using hh



private theorem entry_annihilates {p a : ℕ} [Fact p.Prime] (ha : 1 ≤ a)
    (c x : ZMod (p ^ a))
    (hc : ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt ha)) (ZMod p) c = 0)
    (hx : (p : ZMod (p ^ a)) * x = 0) : c * x = 0 := by
  have hd : p ∣ c.val := by
    rwa [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hc
  obtain ⟨k, hk⟩ := hd
  rw [← ZMod.natCast_zmod_val c, hk, Nat.cast_mul]
  calc
    (p : ZMod (p ^ a)) * k * x = (k : ZMod (p ^ a)) * ((p : ZMod (p ^ a)) * x) := by ring
    _ = 0 := by rw [hx, mul_zero]

theorem homocyclic_fixes_torsion_of_reduction_one
    {P : Type*} [Group P] {p a : ℕ} [Fact p.Prime] (ha : 1 ≤ a)
    (e : P ≃* Multiplicative (Fin 2 → ZMod (p ^ a))) (α : MulAut P)
    (hα : GeneralLinearGroup.map
      (ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt ha)) (ZMod p))
      (homocyclicAutEquiv e α) = 1)
    (x : P) (hx : x ^ p = 1) : α x = x := by
  let A := (homocyclicAutEquiv e α).val
  let r := ZMod.castHom (dvd_pow_self p (Nat.ne_of_gt ha)) (ZMod p)
  have hA : r.mapMatrix (A - 1) = 0 := by
    rw [map_sub, map_one]
    exact sub_eq_zero.mpr (congrArg Units.val hα)
  have hv : ∀ i, (p : ZMod (p ^ a)) * (e x).toAdd i = 0 := by
    have hh := congrArg (fun x : P => (e x).toAdd) hx
    simp only [map_pow, map_one] at hh
    change p • (e x).toAdd = 0 at hh
    intro i
    simpa only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] using congrFun hh i
  have hD : (A - 1) *ᵥ (e x).toAdd = 0 := by
    funext i
    change ∑ j, (A - 1) i j * (e x).toAdd j = 0
    apply Finset.sum_eq_zero
    intro j _
    exact entry_annihilates ha ((A - 1) i j) ((e x).toAdd j)
      (congrFun (congrFun hA i) j) (hv j)
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [homocyclicAutEquiv_apply]
  exact sub_eq_zero.mp (by simpa only [Matrix.sub_mulVec, Matrix.one_mulVec] using hD)

end HomocyclicCentralizer
