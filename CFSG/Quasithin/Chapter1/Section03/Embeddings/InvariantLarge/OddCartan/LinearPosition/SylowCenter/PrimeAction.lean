module

public import Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.SpecificGroups.Quaternion.PresentationHom
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.Sylow
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Pointwise Sylow fixers of prime-field SL₂

For q > 3 prime with q congruent to one modulo four, an automorphism of
SL₂(q) fixing a Sylow two-subgroup pointwise is trivial. A square root of
minus one and the Weyl matrix give a noncommutative quaternion image;
Sylow conjugacy puts such an image inside every Sylow two-subgroup.

The actual central-quotient automorphism theorem expresses each SL₂
automorphism as inner times diagonal times field: perfectness gives
faithful descent, and the prime field has no nontrivial field automorphism.
The resulting GL₂ conjugator centralizes a noncommutative subgroup, hence
is scalar. This is the action fact used for the whole ambient Sylow center
in the linear Cartan argument.

Source: Aschbacher–Smith, proof of 1.3.4, printed pp.510–511. The
inner–diagonal–field theorem is the proved A₁ calculation in
`Theory.SpecificGroups.PSL2.OuterSolvable.OddCoverage`, sourced to GLS3,
Theorem 2.5.12 and §2.7.
-/

public section

open Subgroup Matrix
open scoped MatrixGroups
open Theory.PSL2 Theory.PSL2.OuterSolvable

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan

private theorem diagonal_conjugation {F : Type*} [Field F] (u : Fˣ)
    (M : Matrix (Fin 2) (Fin 2) F) :
    !![M 0 0, (u : F) * M 0 1; (↑u⁻¹ : F) * M 1 0, M 1 1] =
      !![(u : F), 0; 0, 1] * M * !![(↑u⁻¹ : F), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two,
      mul_assoc, mul_comm]

private theorem sl2_aut_linear {q : ℕ} [Fact q.Prime] (hq : Odd q) (hlarge : 3 < q)
    (a : MulAut SL(2, ZMod q)) :
    ∃ A : GL (Fin 2) (ZMod q), ∀ x,
      SpecialLinearGroup.toGL (a x) = A * SpecialLinearGroup.toGL x * A⁻¹ := by
  let : _root_.Group.IsPerfect SL(2, ZMod q) :=
    GorensteinWalter.sl2_isPerfect_of_card_gt_three (ZMod q) (by simpa using hlarge)
  let Q := Subgroup.quotientAut (center SL(2, ZMod q))
  obtain ⟨g, u, σ, ha⟩ := odd_semilinear_coverage
    (K := ZMod q)
    (by rw [ringChar.eq (ZMod q) q]; rcases hq with ⟨k, hk⟩; omega)
    (by simpa using hlarge) (Q a)
  have hs : σ = 1 := Subsingleton.elim _ _
  rw [hs, map_one, mul_one] at ha
  obtain ⟨g, rfl⟩ := quotientMap_surjective (ZMod q) g
  have hconj : Q (MulAut.conj g) = MulAut.conj (quotientMap (ZMod q) g) := by
    ext x
    obtain ⟨x, rfl⟩ := quotientMap_surjective (ZMod q) x
    change (Subgroup.quotientAut (center SL(2, ZMod q)) (MulAut.conj g))
      (QuotientGroup.mk' (center SL(2, ZMod q)) x) = _
    rw [Subgroup.quotientAut_apply_mk]
    change quotientMap (ZMod q) (g * x * g⁻¹) = _
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have ha' : a = MulAut.conj g * slDiagonalHom u := by
    apply MulAut.quotient_center_injective
    rw [map_mul, hconj]
    exact ha
  let d := GeneralLinearGroup.diagonalPair (ZMod q) (u, 1)
  have hd (x : SL(2, ZMod q)) :
      SpecialLinearGroup.toGL (slDiagonalHom u x) =
        d * SpecialLinearGroup.toGL x * d⁻¹ := by
    apply Units.ext
    exact diagonal_conjugation u x.val
  refine ⟨SpecialLinearGroup.toGL g * d, fun x => ?_⟩
  rw [ha']
  change SpecialLinearGroup.toGL (g * slDiagonalHom u x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, hd]
  group

/-- Prime-field SL₂ automorphisms fixing a noncommutative subgroup pointwise are trivial. -/
private theorem sl2_prime_aut_eq_one_of_noncommutative_fixed {q : ℕ} [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (U : Subgroup SL(2, ZMod q))
    (hU : ¬ IsMulCommutative U) (a : MulAut SL(2, ZMod q))
    (ha : ∀ x ∈ U, a x = x) : a = 1 := by
  let f : SL(2, ZMod q) →* GL (Fin 2) (ZMod q) := SpecialLinearGroup.toGL
  have hf : Function.Injective f := SpecialLinearGroup.toGL_injective
  have hV : ¬ IsMulCommutative (U.map f) := by
    intro hc
    apply hU
    exact IsMulCommutative.of_comm fun x y =>
      (U.equivMapOfInjective f hf).injective (by
        simpa only [map_mul] using hc.is_comm.comm
          (U.equivMapOfInjective f hf x) (U.equivMapOfInjective f hf y))
  obtain ⟨A, hA⟩ := sl2_aut_linear hq hlarge a
  have hAC : A ∈ centralizer (U.map f : Set (GL (Fin 2) (ZMod q))) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    have h := hA x
    rw [ha x hx] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  obtain ⟨u, rfl⟩ := GeneralLinearGroup.centralizer_le_scalar_of_noncommutative _ hV hAC
  apply MulEquiv.ext
  intro x
  apply hf
  change f (a x) = f x
  rw [hA x, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem sl2_exists_noncommutative_two_subgroup {q : ℕ} [Fact q.Prime]
    (_hlarge : 3 < q) (hmod : q % 4 = 1) :
    ∃ U : Subgroup SL(2, ZMod q), IsPGroup 2 U ∧ ¬ IsMulCommutative U := by
  obtain ⟨r, hr⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : q % 4 ≠ 3)
  have hr2 : r * r = -1 := hr.symm
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr2
  have htwo : (2 : ZMod q) ≠ 0 := by
    apply CharP.cast_ne_zero_of_ne_of_prime (ZMod q) Nat.prime_two
    omega
  have hrn : -r ≠ r := by
    intro h
    apply mul_ne_zero htwo hr0
    rw [two_mul]
    exact (congrArg (fun t => t + r) h.symm).trans (neg_add_cancel r)
  let a : SL(2, ZMod q) := ⟨!![r, 0; 0, -r], by simp [det_fin_two, hr2]⟩
  let b : SL(2, ZMod q) := ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩
  have ha2 : a ^ 2 = -1 := by
    apply Subtype.ext
    change (!![r, 0; 0, -r] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^ 2 = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, hr2]
  have hb2 : b ^ 2 = a ^ 2 := by
    rw [ha2]
    apply Subtype.ext
    change (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) ^ 2 = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two]
  have ha4 : a ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha2]
    simp
  have hba : b * a = a⁻¹ * b := by
    apply (eq_inv_mul_iff_mul_eq).mpr
    apply Subtype.ext
    change (!![r, 0; 0, -r] : Matrix (Fin 2) (Fin 2) (ZMod q)) *
      (!![0, -1; 1, 0] * !![r, 0; 0, -r]) = !![0, -1; 1, 0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hr2]
  have hab : a * b ≠ b * a := by
    intro h
    have h01 := congrArg (fun x : SL(2, ZMod q) => x.val 0 1) h
    apply hrn
    change (!![r, 0; 0, -r] * !![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 =
      (!![0, -1; 1, 0] * !![r, 0; 0, -r] : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 at h01
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
  let f := QuaternionGroup.liftOfRelations a b ha4 hb2 hba
  have hfA : f (.a 1) = a := QuaternionGroup.liftOfRelations_a_one a b ha4 hb2 hba
  have hfB : f (.xa 0) = b := QuaternionGroup.liftOfRelations_xa_zero a b ha4 hb2 hba
  refine ⟨f.range, ?_, ?_⟩
  · exact (IsPGroup.of_card (p := 2) (n := 3) (by norm_num [QuaternionGroup.card])).of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
  · intro hc
    apply hab
    have h := congrArg Subtype.val (hc.is_comm.comm
      (⟨f (.a 1), ⟨.a 1, rfl⟩⟩ : f.range) (⟨f (.xa 0), ⟨.xa 0, rfl⟩⟩ : f.range))
    simpa only [Subgroup.coe_mul, hfA, hfB] using h

/-- For q congruent to one modulo four, every SL₂(q) Sylow two-subgroup is noncommutative. -/
private theorem sl2_sylow_not_isMulCommutative {q : ℕ} [Fact q.Prime]
    (hlarge : 3 < q) (hmod : q % 4 = 1) (P : Sylow 2 SL(2, ZMod q)) :
    ¬ IsMulCommutative P := by
  obtain ⟨U, hU, hn⟩ := sl2_exists_noncommutative_two_subgroup hlarge hmod
  obtain ⟨Q, hQ⟩ := hU.exists_le_sylow
  intro hc
  apply hn
  let f : U →* P := (Sylow.equiv Q P).toMonoidHom.comp (Subgroup.inclusion hQ)
  have hf : Function.Injective f := (Sylow.equiv Q P).injective.comp (Subgroup.inclusion_injective hQ)
  exact IsMulCommutative.of_comm fun x y => hf (by
    simpa only [map_mul] using hc.is_comm.comm (f x) (f y))

/-- The pointwise fixer of a Sylow two-subgroup in Aut(SL₂(q)) is trivial
for the prime-field, q congruent to one modulo four case. -/
theorem sl2_prime_sylow_aut_eq_one {q : ℕ} [Fact q.Prime]
    (hq : Odd q) (hlarge : 3 < q) (hmod : q % 4 = 1)
    (P : Sylow 2 SL(2, ZMod q)) (a : MulAut SL(2, ZMod q))
    (ha : ∀ x ∈ (P : Subgroup SL(2, ZMod q)), a x = x) : a = 1 :=
  sl2_prime_aut_eq_one_of_noncommutative_fixed hq hlarge (P : Subgroup SL(2, ZMod q))
    (sl2_sylow_not_isMulCommutative hlarge hmod P) a ha

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
