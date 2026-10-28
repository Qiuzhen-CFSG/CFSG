module

public import Theory.AlgebraicGroup.RootSystems.CliffordSplitLipschitz
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module
/-!
# Clifford curves from orthogonal isotropic pairs

For orthogonal isotropic vectors `u, v`, the Clifford element `1 + a • (u v)`
is an even unit of norm one. Its conjugation sends a vector `w` to
`w + a • (B(v,w) • u - B(u,w) • v)`. The split reverse normalizer theorem
therefore puts this element in the generated Spin group, in every characteristic.

These are the elementary Clifford calculations underlying the type-D root
curves in GLS3, §§1.10–1.12 (`refs/KGroup/GLS3/Chapter1.tex`). No inverse
of the Spin cover is used to infer regularity.
-/

public section
namespace Theory.AlgebraicGroup.CliffordIsotropicPair
open _root_.CliffordAlgebra
open scoped Pointwise
universe u
variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
variable (Q : QuadraticForm k V) (u v : V)
variable (hu : Q u = 0) (hv : Q v = 0) (huv : Q.IsOrtho u v)

include hv huv in
lemma bivector_sq : (ι Q u * ι Q v) * (ι Q u * ι Q v) = 0 := by
  rw [mul_assoc, ← mul_assoc (ι Q v), ι_mul_ι_comm_of_isOrtho huv.symm]
  simp [mul_assoc, ι_sq_scalar, hv]

lemma bivector_comm (w : V) :
    (ι Q u * ι Q v) * ι Q w - ι Q w * (ι Q u * ι Q v) =
      Q.polarBilin v w • ι Q u - Q.polarBilin u w • ι Q v := by
  calc
    _ = ι Q u * (algebraMap k _ (Q.polarBilin v w) - ι Q w * ι Q v) -
        ι Q w * (ι Q u * ι Q v) := by
      rw [mul_assoc, ι_mul_ι_comm (Q := Q) v w]
      rfl
    _ = Q.polarBilin v w • ι Q u -
        (algebraMap k _ (Q.polarBilin u w) - ι Q w * ι Q u) * ι Q v -
        ι Q w * (ι Q u * ι Q v) := by
      rw [mul_sub, ← mul_assoc (ι Q u), ι_mul_ι_comm (Q := Q) u w]
      rw [← Algebra.commutes, ← Algebra.smul_def]
      rfl
    _ = _ := by
      rw [sub_mul, ← Algebra.smul_def, mul_assoc]
      abel

include hu hv huv in
lemma bivector_sandwich (w : V) :
    (ι Q u * ι Q v) * ι Q w * (ι Q u * ι Q v) = 0 := by
  have hc := bivector_comm Q u v w
  have he := sub_eq_iff_eq_add.mp hc
  rw [he, add_mul, sub_mul, smul_mul_assoc, smul_mul_assoc]
  have h1 : ι Q u * (ι Q u * ι Q v) = 0 := by
    rw [← mul_assoc, ι_sq_scalar, hu, map_zero, zero_mul]
  have h2 : ι Q v * (ι Q u * ι Q v) = 0 := by
    rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho huv.symm]
    simp [mul_assoc, ι_sq_scalar, hv]
  rw [h1, h2, mul_assoc, bivector_sq Q u v hv huv]
  simp

include hv huv in
lemma curve_mul (a b : k) :
    (1 + a • (ι Q u * ι Q v)) * (1 + b • (ι Q u * ι Q v)) =
      1 + (a + b) • (ι Q u * ι Q v) := by
  simp only [add_mul, mul_add, one_mul, mul_one,
    smul_mul_assoc, mul_smul_comm, bivector_sq Q u v hv huv]
  simp only [smul_zero, add_zero, add_smul]
  abel

include hu hv huv in
lemma curve_conj (a : k) (w : V) :
    (1 + a • (ι Q u * ι Q v)) * ι Q w * (1 - a • (ι Q u * ι Q v)) =
      ι Q (w + a • (Q.polarBilin v w • u - Q.polarBilin u w • v)) := by
  have h (x y : CliffordAlgebra Q) :
      (1 + x) * y * (1 - x) = y + (x * y - y * x) - x * y * x := by
    noncomm_ring
  rw [h, smul_mul_assoc, mul_smul_comm, ← smul_sub,
    bivector_comm Q u v, smul_mul_assoc, mul_smul_comm,
    bivector_sandwich Q u v hu hv huv]
  simp [map_add, map_sub, map_smul]

include huv in
lemma curve_star (a : k) :
    star (1 + a • (ι Q u * ι Q v)) = 1 - a • (ι Q u * ι Q v) := by
  rw [star_add, star_one, _root_.CliffordAlgebra.star_smul, star_mul,
    star_ι, star_ι, neg_mul_neg, ι_mul_ι_comm_of_isOrtho huv.symm]
  simp [sub_eq_add_neg]

lemma curve_even (a : k) :
    1 + a • (ι Q u * ι Q v) ∈ even Q := by
  exact (even Q).add_mem (even Q).one_mem
    ((even Q).smul_mem (ι_mul_ι_mem_evenOdd_zero Q u v) a)

include hv huv in
noncomputable def curveUnit (a : k) : (CliffordAlgebra Q)ˣ where
  val := 1 + a • (ι Q u * ι Q v)
  inv := 1 + (-a) • (ι Q u * ι Q v)
  val_inv := by rw [curve_mul Q u v hv huv]; simp
  inv_val := by rw [curve_mul Q u v hv huv]; simp

variable [IsAlgClosed k] [FiniteDimensional k V]
include hu hv huv in
lemma curve_mem_spin (s : SplitQuadraticForm Q) (hs : 0 < s.rank) (a : k) :
    1 + a • (ι Q u * ι Q v) ∈ spinGroup Q := by
  let z := curveUnit Q u v hv huv a
  have heven : (z : CliffordAlgebra Q) ∈ even Q := curve_even Q u v a
  have hconj (b : k) :
      ConjAct.toConjAct (curveUnit Q u v hv huv b) • LinearMap.range (ι Q) ≤
        LinearMap.range (ι Q) := by
    rw [Submodule.pointwise_smul_def, Submodule.map_le_iff_le_comap]
    rintro _ ⟨w, rfl⟩
    change (1 + b • (ι Q u * ι Q v)) * ι Q w *
      (1 + (-b) • (ι Q u * ι Q v)) ∈ LinearMap.range (ι Q)
    rw [neg_smul, ← sub_eq_add_neg, curve_conj Q u v hu hv huv]
    exact LinearMap.mem_range_self _ _
  have hinv : z⁻¹ = curveUnit Q u v hv huv (-a) := by
    apply Units.ext
    rfl
  have hnormal : ConjAct.toConjAct z • LinearMap.range (ι Q) =
      LinearMap.range (ι Q) := by
    apply le_antisymm (hconj a)
    have hle : ConjAct.toConjAct z⁻¹ • LinearMap.range (ι Q) ≤
        LinearMap.range (ι Q) := by rw [hinv]; exact hconj (-a)
    have h := smul_mono_right (ConjAct.toConjAct z) hle
    simpa only [map_inv, smul_inv_smul] using h
  have hlip : z ∈ lipschitzGroup Q :=
    mem_lipschitzGroup_of_mem_even_of_conjAct_smul_range_ι_eq_of_split
      s hs heven hnormal
  have hstar : star (z : CliffordAlgebra Q) = (↑z⁻¹ : CliffordAlgebra Q) := by
    change star (1 + a • (ι Q u * ι Q v)) = 1 + (-a) • (ι Q u * ι Q v)
    rw [curve_star Q u v huv]
    simp [sub_eq_add_neg]
  exact spinGroup.mem_iff.mpr ⟨pinGroup.units_mem_iff.mpr
    ⟨hlip, by rw [Unitary.mem_iff, hstar]; exact ⟨z.inv_val, z.val_inv⟩⟩, heven⟩

end Theory.AlgebraicGroup.CliffordIsotropicPair
