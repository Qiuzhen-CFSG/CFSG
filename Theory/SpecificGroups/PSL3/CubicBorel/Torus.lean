module

public import Theory.SpecificGroups.PSL3.CubicBorel.Reduction
public import Theory.SpecificGroups.PSL3.CartanActions.ActorCoverage
public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage.RootRigidity
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Comparison of triangular cubic actions in PSL₃

The kernel of GL₃ conjugation on PSL₃ is scalar: perfectness of SL₃
makes its central-quotient action faithful, and commuting with elementary
matrices forces a scalar. Thus a triangular cubic actor has scalar cube.
Dividing its diagonal entries by the last entry makes all three diagonal
parameters cube roots of unity, without changing the induced action.

The normalized determinant of the supplied outer actor is nonidentity;
otherwise its diagonal and unipotent factors would both be inner.
This determinant generates the cube roots of unity. A power therefore
cancels the other actor's normalized determinant. The remaining diagonal
matrix has determinant one and cube one, and represents an actual cubic
(or identity) element in the projective split torus. The two original
unitriangular factors are retained in the resulting simultaneous formulas.

This proof works over every field. In particular it makes no restriction
on whether nine divides q-1 and never discards the projective scalar kernel.
Perfectness is reused from the attributed ATLAS port via ActorCoverage;
its license and source attribution remain in that imported development.
The scalar-kernel argument follows the existing OddInvolutionFixed.Graph
calculation in this repository.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final paragraph
of 15.3.37, printed p.1135, and the torus discussion in A.3.18, pp.52--53.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.CartanActions Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.CubicBorel
variable {F : Type*} [Field F]

private def diagonal : (Fin 3 → Fˣ) →* GL (Fin 3) F where
  toFun := diagonalGL
  map_one' := by apply Units.ext; simp [diagonalGL]
  map_mul' a b := by apply Units.ext; simp [diagonalGL, diagonal_mul_diagonal]

private theorem scalar_action (a : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) a) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := projection_surjective F y
  change projection F (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) a) x) = projection F x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

private theorem scalar_of_trivial_action (g : GL (Fin 3) F)
    (hg : linearConj F g = 1) : ∃ a : Fˣ, GeneralLinearGroup.scalar (Fin 3) a = g := by
  have hs : linearConjSL F g = 1 :=
    ActorCoverage.centerAction_injective F (hg.trans (map_one _).symm)
  have hc (x : SL(3,F)) : g * SpecialLinearGroup.toGL x = SpecialLinearGroup.toGL x * g := by
    have he := congrArg SpecialLinearGroup.toGL (DFunLike.congr_fun hs x)
    rw [linearConjSL_toGL] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hz : g ∈ center (GL (Fin 3) F) := by
    apply GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr
    apply Matrix.mem_range_scalar_of_commute_transvectionStruct
    intro t
    exact (congrArg Units.val (hc ⟨t.toMatrix, by simp⟩)).symm
  rwa [GeneralLinearGroup.center_eq_range_scalar] at hz

private theorem triangular_diagonal_ne_zero (g : GL (Fin 3) F)
    (hg : g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0) (i : Fin 3) :
    g.val i i ≠ 0 := by
  have hn := (GeneralLinearGroup.det g).ne_zero
  change Matrix.det g.val ≠ 0 at hn
  rw [Matrix.det_fin_three] at hn
  simp only [hg.1, hg.2.1, hg.2.2, mul_zero, zero_mul, sub_zero, add_zero] at hn
  fin_cases i
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).1
  · exact (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hn).1).2
  · exact (mul_ne_zero_iff.mp hn).2

private theorem triangular_cube_diagonal (g : GL (Fin 3) F)
    (hg : g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0) (i : Fin 3) :
    (g ^ 3).val i i = g.val i i ^ 3 := by
  change (g.val ^ 3) i i = _
  fin_cases i <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, hg.1, hg.2.1, hg.2.2]

/-- A scalar normalization makes every diagonal parameter cubic. The matrix
itself can still have a nontrivial unitriangular factor. -/
private theorem triangular_cubic_factorization (g : GL (Fin 3) F)
    (hg : g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0)
    (hcube : linearConj F g ^ 3 = 1) :
    ∃ (u : PSL(3,F)) (d : Fin 3 → Fˣ), u ∈ unipotent F ∧
      (∀ i, d i ^ 3 = 1) ∧ linearConj F g = MulAut.conj u * linearConj F (diagonal d) := by
  let a (i : Fin 3) : Fˣ := Units.mk0 _ (triangular_diagonal_ne_zero g hg i)
  let v : U F := ⟨g.val 0 1 / (a 1 : F), g.val 1 2 / (a 2 : F), g.val 0 2 / (a 2 : F)⟩
  have hfactor : g = SpecialLinearGroup.toGL (specialLinear F v) * diagonal a := by
    apply Units.ext
    change g.val = matrix F v * Matrix.diagonal (fun i => (a i : F))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_diagonal, matrix, v, a, hg.1, hg.2.1, hg.2.2,
        triangular_diagonal_ne_zero g hg]
  obtain ⟨s, hs⟩ := scalar_of_trivial_action (g ^ 3) (by rw [map_pow, hcube])
  have hacube (i : Fin 3) : a i ^ 3 = s := by
    apply Units.ext
    have hh := congrArg (fun m : GL (Fin 3) F => m.val i i) hs
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hh
    rw [triangular_cube_diagonal g hg i] at hh
    exact hh.symm
  let d : Fin 3 → Fˣ := fun i => a i * (a 2)⁻¹
  have hd (i : Fin 3) : d i ^ 3 = 1 := by
    simp only [d, mul_pow, inv_pow, hacube, mul_inv_cancel]
  have hdiag : diagonal a = diagonal d * GeneralLinearGroup.scalar (Fin 3) (a 2) := by
    apply Units.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.scalar (Fin 3) _
    rw [Matrix.scalar_apply, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp [d]
  refine ⟨projective F v, d, (projective_range F).le ⟨v, rfl⟩, hd, ?_⟩
  rw [hfactor, map_mul, linearConj_toGL, hdiag, map_mul, scalar_action, mul_one]
  rfl

private theorem diagonal_eq_torus (d : Fin 3 → Fˣ) (hd : d 0 * d 1 * d 2 = 1) :
    diagonal d = SpecialLinearGroup.toGL (torusSL F (d 0, d 2)) := by
  have hm : d 1 = (d 0 * d 2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hd)
  apply Units.ext
  change Matrix.diagonal _ = (torusSL F (d 0, d 2)).val
  rw [torusSL_val]
  congr 1
  funext i
  fin_cases i <;> simp [hm]

private theorem determinant_cubic (d : Fin 3 → Fˣ) (hd : ∀ i, d i ^ 3 = 1) :
    (d 0 * d 1 * d 2) ^ 3 = 1 := by simp only [mul_pow, hd, one_mul]

private theorem cubic_diagonal_comparison (a b : Fin 3 → Fˣ)
    (ha : ∀ i, a i ^ 3 = 1) (hb : ∀ i, b i ^ 3 = 1)
    (hane : a 0 * a 1 * a 2 ≠ 1) :
    ∃ (k : ℕ) (z : PSL(3,F)), z ∈ torus F ∧ z ^ 3 = 1 ∧
      linearConj F (diagonal b) = MulAut.conj z * linearConj F (diagonal a) ^ k := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hprim : IsPrimitiveRoot (a 0 * a 1 * a 2) 3 :=
    IsPrimitiveRoot.iff_orderOf.mpr (orderOf_eq_prime (determinant_cubic a ha) hane)
  obtain ⟨k, _, hk⟩ := hprim.eq_pow_of_mem_rootsOfUnity
    ((mem_rootsOfUnity 3 (b 0 * b 1 * b 2)).mpr (determinant_cubic b hb))
  let c : Fin 3 → Fˣ := b * (a ^ k)⁻¹
  have hc (i : Fin 3) : c i ^ 3 = 1 := by
    have hak : (a i ^ k) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm k 3, pow_mul, ha, one_pow]
    simp only [c, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, mul_pow, inv_pow, hb, hak,
      inv_one, one_mul]
  have hdet : c 0 * c 1 * c 2 = 1 := by
    change (b 0 * (a 0 ^ k)⁻¹) * (b 1 * (a 1 ^ k)⁻¹) * (b 2 * (a 2 ^ k)⁻¹) = 1
    calc
      _ = (b 0 * b 1 * b 2) * ((a 0 * a 1 * a 2) ^ k)⁻¹ := by
        simp only [mul_pow, mul_inv]
        ac_rfl
      _ = 1 := by rw [hk, mul_inv_cancel]
  have heq : diagonal b = diagonal c * diagonal a ^ k := by
    rw [← map_pow, ← map_mul]
    congr 1
    dsimp only [c]
    group
  refine ⟨k, torusMap F (c 0, c 2), ⟨_, rfl⟩, ?_, ?_⟩
  · rw [← map_pow]
    have hh : (c 0, c 2) ^ 3 = (1 : Fˣ × Fˣ) := Prod.ext (hc 0) (hc 2)
    rw [hh, map_one]
  · rw [heq, diagonal_eq_torus c hdet, map_mul, map_pow, linearConj_toGL]
    rfl

/-- Compare the actual triangular cubic actors using their normalized diagonal
parameters. A nontrivial determinant generates all cube roots of unity. -/
theorem triangularCubicComparison (F : Type*) [Field F] : TriangularCubicComparison F := by
  intro d₀ g hd hg hout hd3 hg3
  obtain ⟨u, a, hu, ha, hda⟩ := triangular_cubic_factorization d₀ hd hd3
  obtain ⟨v, b, hv, hb, hgb⟩ := triangular_cubic_factorization g hg hg3
  have hane : a 0 * a 1 * a 2 ≠ 1 := by
    intro he
    apply hout
    rw [hda, diagonal_eq_torus a he, linearConj_toGL]
    exact ⟨u * torusMap F (a 0, a 2), map_mul MulAut.conj _ _⟩
  obtain ⟨k, z, hz, hz3, hba⟩ := cubic_diagonal_comparison a b ha hb hane
  refine ⟨k, u, v, z, linearConj F (diagonal a), hu, hv, hz, hz3, hda, ?_⟩
  rw [hgb, hba, mul_assoc]

end Matrix.PSL3.CubicBorel
