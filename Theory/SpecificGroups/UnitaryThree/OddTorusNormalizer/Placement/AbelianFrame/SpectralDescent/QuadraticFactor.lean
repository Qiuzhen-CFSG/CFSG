module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.Basic
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Placement.AbelianFrame.SpectralDescent.SplitAssembly
import Mathlib.FieldTheory.Fixed
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
/-!
# Splitting the quadratic factor of a unitary cubic

An anisotropic eigenvector of a special unitary matrix has an eigenvalue `a`
of norm one. The actual matrix characteristic polynomial is
`X³ - t X² + conj(t) X - 1`, where `t` is its trace. Its root equation gives
`conj(t) = a * (t - a) + a⁻¹`.

In characteristic two, choose `s² = a`. The square map is bijective, so `s`
also has norm one and `d = (t - a) * s` belongs to the fixed field. Removing
`X - a` and changing variable by `s` leaves `X² - d X + 1`. Every quadratic
over a finite field splits over its quadratic extension: an irreducible
quadratic divides `X^(q²) - X`, while a reducible quadratic has a root and
splits, including the repeated-root case.

The subgroup application uses the literal anisotropic representative supplied
by `commonEigenline_rep_spectral_data`. It discharges the splitting premise of
`exists_commonEigenbasis_of_split_charpolys`; construction of the common line
from reducibility remains with the separate invariant-line argument.

This is the spectral descent step supporting GLS4, Chapter 4, Lemma 3.11(a),
`refs/KGroup/GLS4/Chapter4.tex`, lines 585–603. The elementary matrix identities
follow the same conventions as `AbelianFrame.CanonicalFrame` and
`Theory.SpecificGroups.SL3.PRegularClasses.TraceParameters`.
-/

public section

open Matrix Polynomial BenderSuzuki.MatrixGroups

namespace UnitaryThree.OddTorusNormalizer.AbelianFrame
variable {E : Type*} [Field E]

private theorem quadratic_splits_in_square_extension
    {K : Type*} [Field K] [Finite K] [Finite E] [Algebra K E]
    (hcard : Nat.card E = Nat.card K ^ 2) (p : K[X]) (hp : p.natDegree = 2) :
    (p.map (algebraMap K E)).Splits := by
  by_cases hi : Irreducible p
  · have hd := hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp
        (show p.natDegree ∣ 2 by rw [hp])
    have hd' := Polynomial.map_dvd (algebraMap K E) hd
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, ← hcard] at hd'
    apply (Polynomial.splits_X_pow_nat_card_sub_X (K := E)).of_dvd _ hd'
    apply sub_ne_zero.mpr
    intro he
    have he' := congrArg Polynomial.natDegree he
    simp only [natDegree_X_pow, natDegree_X] at he'
    exact (ne_of_gt (Finite.one_lt_card (α := E))) he'
  · have hr : ∃ x : K, p.eval x = 0 := by
      by_contra! h
      apply hi
      apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · simp [hp]
      · exact h
    obtain ⟨x, hx⟩ := hr
    exact (Polynomial.Splits.of_natDegree_eq_two hp hx).map _

private theorem special_det (J : HermitianForm 3 E) (g : J.specialSubgroup) :
    g.val.val.det = 1 := by
  have hd := ((J.mem_specialSubgroup_iff g.val).mp g.property).2
  have h := congrArg (fun d : Eˣ => (d : E)) hd
  rw [GeneralLinearGroup.val_det_apply, Units.val_one] at h
  exact h

private theorem special_inverse_trace (J : HermitianForm 3 E) (g : J.specialSubgroup) :
    (g.val.val)⁻¹.trace = J.conj g.val.val.trace := by
  have hu := ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  have hJ := isUnit_iff_ne_zero.mpr J.form_nondegenerate
  have hinv : (g.val.val)⁻¹ = J.form⁻¹ * J.conjTranspose g.val.val * J.form := by
    apply Matrix.inv_eq_left_inv
    calc
      J.form⁻¹ * J.conjTranspose g.val.val * J.form * g.val.val =
          J.form⁻¹ * (J.conjTranspose g.val.val * J.form * g.val.val) := by
            simp only [mul_assoc]
      _ = 1 := by rw [hu, Matrix.nonsing_inv_mul _ hJ]
  rw [hinv, Matrix.trace_mul_cycle, Matrix.mul_nonsing_inv _ hJ, one_mul]
  simp only [Matrix.trace, Matrix.diag, HermitianForm.conjTranspose, map_sum]

private theorem special_charpoly_cubic (J : HermitianForm 3 E) (g : J.specialSubgroup) :
    (specialNatural J g).charpoly =
      X ^ 3 - C g.val.val.trace * X ^ 2 + C (J.conj g.val.val.trace) * X - 1 := by
  have hc (A : Matrix (Fin 3) (Fin 3) E) :
      A.charpoly = X ^ 3 - C A.trace * X ^ 2 + C A.adjugate.trace * X - C A.det := by
    simp only [Matrix.charpoly, Matrix.det_fin_three, Matrix.charmatrix_apply_eq,
      Matrix.trace, Matrix.diag, Fin.sum_univ_three, Matrix.adjugate_fin_three]
    simp
    ring
  have ha : g.val.val.adjugate = (g.val.val)⁻¹ := by
    rw [Matrix.inv_def, special_det, Ring.inverse_one, one_smul]
  change (Matrix.toLin' g.val.val).charpoly = _
  rw [Matrix.charpoly_toLin', hc, special_det, map_one, ha, special_inverse_trace]

private theorem special_eigenvalue_norm (J : HermitianForm 3 E) (g : J.specialSubgroup)
    (v : Fin 3 → E) (a : E)
    (hv : dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) ≠ 0)
    (he : specialNatural J g v = a • v) : J.conj a * a = 1 := by
  let : Star E := ⟨J.conj⟩
  let : InvolutiveStar E := ⟨J.conj_involutive⟩
  let : StarMul E := ⟨fun r s => by
    change J.conj (r * s) = J.conj s * J.conj r
    rw [map_mul, mul_comm]⟩
  let : StarRing E := ⟨fun r s => by
    change J.conj (r + s) = J.conj r + J.conj s
    rw [map_add]⟩
  have hi : dotProduct (fun i => J.conj ((specialNatural J g v) i))
      (J.form.mulVec (specialNatural J g v)) =
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) := by
    change star (g.val.val *ᵥ v) ⬝ᵥ J.form *ᵥ (g.val.val *ᵥ v) =
      star v ⬝ᵥ J.form *ᵥ v
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul]
    change star v ᵥ* (J.conjTranspose g.val.val * J.form * g.val.val) ⬝ᵥ v = _
    rw [(J.mem_specialSubgroup_iff g.val).mp g.property |>.1]
    exact (Matrix.dotProduct_mulVec _ _ _).symm
  rw [he] at hi
  have hs : dotProduct (fun i => J.conj ((a • v) i)) (J.form.mulVec (a • v)) =
      (J.conj a * a) * dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) := by
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, Matrix.mulVec_smul,
      dotProduct, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs] at hi
  exact (mul_right_cancel₀ hv (hi.trans (one_mul _).symm))

private theorem cubic_splits_of_norm_one_root [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (t a : E) (ha : J.conj a * a = 1)
    (hr : a ^ 3 - t * a ^ 2 + J.conj t * a - 1 = 0) :
    (X ^ 3 - C t * X ^ 2 + C (J.conj t) * X - 1).Splits := by
  have ha0 : a ≠ 0 := by
    intro hz
    simp [hz] at ha
  have hca : J.conj a = a⁻¹ := eq_inv_of_mul_eq_one_left ha
  have ht : J.conj t = a * (t - a) + a⁻¹ := by
    apply (mul_right_cancel₀ ha0)
    rw [add_mul, inv_mul_cancel₀ ha0]
    linear_combination hr
  obtain ⟨s, hs⟩ := surjective_frobenius E 2 a
  change s ^ 2 = a at hs
  have hs0 : s ≠ 0 := by
    intro hz
    apply ha0
    rw [← hs, hz, zero_pow (by decide)]
  have hsnorm : J.conj s * s = 1 := by
    apply frobenius_inj E 2
    change (J.conj s * s) ^ 2 = 1 ^ 2
    rw [mul_pow, ← map_pow, hs, ha, one_pow]
  have hcs : J.conj s = s⁻¹ := eq_inv_of_mul_eq_one_left hsnorm
  have hd : J.conj ((t - a) * s) = (t - a) * s := by
    rw [map_mul, map_sub, ht, hca, add_sub_cancel_right, hcs, ← hs]
    field_simp
  let K := FixedBy.subfield E J.conj
  let d : K := ⟨(t - a) * s, hd⟩
  let p : K[X] := X ^ 2 - C d * X + 1
  have hp : p.natDegree = 2 := by
    dsimp [p]
    compute_degree!
  have hk : Nat.card K = q := hfixed
  have hsplit : (X ^ 2 - C ((t - a) * s) * X + 1 : E[X]).Splits := by
    have hh := quadratic_splits_in_square_extension
      (E := E) (K := K) (by rw [hk, hcard]) p hp
    simpa only [p, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_mul, map_X, map_C, Polynomial.map_one, d,
      Subfield.algebraMap_ofSubfield, Subfield.coe_subtype] using hh
  have hscale : (C a⁻¹ *
      ((X ^ 2 - C ((t - a) * s) * X + 1).comp (C s * X))).Splits := by
    apply Splits.C_mul
    apply hsplit.comp_of_natDegree_le_one
    compute_degree!
  have hcoeff : (C a : E[X]) * C a⁻¹ = 1 := by
    rw [← C_mul, mul_inv_cancel₀ ha0, map_one]
  have hfactor : (X ^ 3 - C t * X ^ 2 + C (J.conj t) * X - 1 : E[X]) =
      (X - C a) * (C a⁻¹ *
        ((X ^ 2 - C ((t - a) * s) * X + 1).comp (C s * X))) := by
    simp only [add_comp, sub_comp, pow_comp, mul_comp, X_comp, C_comp, one_comp,
      ht, map_add, map_mul, map_sub]
    have hsq : (C s : E[X]) ^ 2 = C a := by rw [← map_pow, hs]
    ring_nf
    rw [hsq]
    linear_combination -(X * C t * C a - X * C a ^ 2 - X ^ 2 * C t + X ^ 3 - 1) * hcoeff
  rw [hfactor]
  exact (Splits.X_sub_C a).mul hscale

/-- An anisotropic eigenvector forces the whole three-dimensional special-unitary
characteristic polynomial to split over the matrix field. -/
theorem special_charpoly_splits_of_anisotropic_eigenvector [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (_hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (g : J.specialSubgroup) (v : Fin 3 → E) (a : E)
    (hv : dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) ≠ 0)
    (he : specialNatural J g v = a • v) :
    (specialNatural J g).charpoly.Splits := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard)
  have hv0 : v ≠ 0 := by
    intro hz
    simp [hz] at hv
  have heig : Module.End.HasEigenvector (specialNatural J g) a v :=
    ⟨Module.End.mem_eigenspace_iff.mpr he, hv0⟩
  have hr := (Module.End.hasEigenvalue_iff_isRoot_charpoly (specialNatural J g) a).mp
    (Module.End.hasEigenvalue_of_hasEigenvector heig)
  change Polynomial.eval a (specialNatural J g).charpoly = 0 at hr
  rw [special_charpoly_cubic] at hr ⊢
  apply cubic_splits_of_norm_one_root J (2 ^ n) hcard hfixed _ a
    (special_eigenvalue_norm J g v a hv he)
  simpa only [eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_one] using hr

open scoped LinearAlgebra.Projectivization

/-- A supplied common eigenline, together with the source no-Borel hypothesis,
gives splitting for every literal special-unitary operator of the subgroup. -/
theorem special_charpolys_split_of_commonEigenline [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hB : SpecialNoBorel J H)
    {l : ℙ E (Fin 3 → E)} (hl : l ∈ commonEigenlines J H) :
    ∀ h : H, (specialNatural J h.val).charpoly.Splits := by
  obtain ⟨hv, he⟩ := commonEigenline_rep_spectral_data J H hB hl
  intro h
  obtain ⟨a, ha⟩ := he h
  exact special_charpoly_splits_of_anisotropic_eigenvector J hn hcard hfixed
    h.val l.rep a hv ha

open scoped IsMulCommutative

/-- This discharges the splitting premise of simultaneous diagonalization for
an odd abelian subgroup with a supplied common eigenline. -/
theorem exists_commonEigenbasis_of_commonEigenline [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (H : Subgroup J.specialSubgroup) (hodd : Odd (Nat.card H)) [IsMulCommutative H]
    (hB : SpecialNoBorel J H) {l : ℙ E (Fin 3 → E)} (hl : l ∈ commonEigenlines J H) :
    ∃ b : Module.Basis (Fin 3) E (Fin 3 → E), IsCommonEigenbasis J H b :=
  exists_commonEigenbasis_of_split_charpolys J hcard H hodd
    (special_charpolys_split_of_commonEigenline J hn hcard hfixed H hB hl)

end UnitaryThree.OddTorusNormalizer.AbelianFrame
