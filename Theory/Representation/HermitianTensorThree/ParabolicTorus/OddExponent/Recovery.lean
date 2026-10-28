module
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.OddExponent.Inputs
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import all Theory.Representation.HermitianTensorThree.ImageOuter.Normalizer.Actions

/-!
# Recovering natural parabolics from the Hermitian action

The kernel of the descended SL₃ action consists of scalar matrices and lies
in both marked parabolics. Thus normalization of an image parabolic lifts
to conjugation preserving its cover parabolic. Two root involutions then
recover the natural fixed point, or dually the natural fixed plane: their
conjugates have distinguished diagonal entry one in characteristic two.

This proves the natural-space recovery input of the odd parabolic exponent
used in Aschbacher–Smith, combined manuscript of 1 March 2004, H.4.2
(printed p.380) and Proposition 8.2.3 (printed pp.715–716).
-/

public noncomputable section
open Subgroup Matrix
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped MatrixGroups
namespace Representation.HermitianTensorThree.ParabolicTorus.OddExponent
variable (n : ℕ) [NeZero n]

private theorem kernel_le_point : (binaryActionHom n).ker ≤ coverPointParabolic n := by
  intro x hx
  rw [binaryActionHom_ker_eq, mem_actionHom_ker_iff] at hx
  obtain ⟨c,hc,_,_⟩ := hx
  rw [coverPointParabolic, Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff, hc]
  simp [Matrix.scalar]

private theorem kernel_le_plane : (binaryActionHom n).ker ≤ coverPlaneParabolic n := by
  intro x hx
  rw [binaryActionHom_ker_eq, mem_actionHom_ker_iff] at hx
  obtain ⟨c,hc,_,_⟩ := hx
  rw [coverPlaneParabolic, Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff, hc]
  simp [Matrix.scalar]

private theorem point_preimage (a : Cover n) :
    binaryActionHom n a ∈ pointParabolicImage n ↔ a ∈ coverPointParabolic n := by
  change a ∈ ((coverPointParabolic n).map (binaryActionHom n)).comap (binaryActionHom n) ↔ _
  rw [comap_map_eq_self (kernel_le_point n)]

private theorem plane_preimage (a : Cover n) :
    binaryActionHom n a ∈ planeParabolicImage n ↔ a ∈ coverPlaneParabolic n := by
  change a ∈ ((coverPlaneParabolic n).map (binaryActionHom n)).comap (binaryActionHom n) ↔ _
  rw [comap_map_eq_self (kernel_le_plane n)]

private theorem cover_congruence_conj (g : GeneralLinearGroup (Fin 3) (E n)) (a : Cover n) :
    binaryActionHom n (coverConj n g a) =
      binaryCongruence n g * binaryActionHom n a * (binaryCongruence n g)⁻¹ := by
  rw [← binaryCongruence_toGL, coverConj_toGL, map_mul, map_mul, map_inv,
    binaryCongruence_toGL]

private theorem conj_point (g : GeneralLinearGroup (Fin 3) (E n))
    (hg : binaryCongruence n g ∈ normalizer (pointParabolicImage n : Set (BinaryAut n)))
    (a : Cover n) (ha : a ∈ coverPointParabolic n) :
    coverConj n g a ∈ coverPointParabolic n := by
  apply (point_preimage n _).mp
  rw [cover_congruence_conj]
  exact (mem_normalizer_iff.mp hg _).mp ((point_preimage n a).mpr ha)

private theorem conj_plane (g : GeneralLinearGroup (Fin 3) (E n))
    (hg : binaryCongruence n g ∈ normalizer (planeParabolicImage n : Set (BinaryAut n)))
    (a : Cover n) (ha : a ∈ coverPlaneParabolic n) :
    coverConj n g a ∈ coverPlaneParabolic n := by
  apply (plane_preimage n _).mp
  rw [cover_congruence_conj]
  exact (mem_normalizer_iff.mp hg _).mp ((plane_preimage n a).mpr ha)

omit [NeZero n] in
private theorem conj_square (g : GeneralLinearGroup (Fin 3) (E n))
    (a : Cover n) (ha : a*a = 1) : coverConj n g a * coverConj n g a = 1 := by
  apply SpecialLinearGroup.toGL_injective
  rw [map_mul, map_one, coverConj_toGL]
  calc
    _ = g * (SpecialLinearGroup.toGL a * SpecialLinearGroup.toGL a) * g⁻¹ := by group
    _ = 1 := by rw [←map_mul,ha,map_one,mul_one,mul_inv_cancel]

omit [NeZero n] in
private theorem point_involution_diagonal (a : Cover n)
    (ha : a ∈ coverPointParabolic n) (hs : a*a = 1) : a.val 0 0 = 1 := by
  obtain ⟨h10,h20⟩ := (Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff _ a).mp ha
  have h := congrArg (fun b : Cover n => b.val 0 0) hs
  change (a.val * a.val) 0 0 = (1 : Mat n) 0 0 at h
  simp only [Matrix.mul_apply,Fin.sum_univ_three,h10,h20,mul_zero,add_zero,
    Matrix.one_apply_eq] at h
  exact (sq_eq_one_iff.mp (by simpa only [pow_two] using h)).elim id (fun h => by simpa only [CharTwo.neg_eq] using h)

omit [NeZero n] in
private theorem plane_involution_diagonal (a : Cover n)
    (ha : a ∈ coverPlaneParabolic n) (hs : a*a = 1) : a.val 2 2 = 1 := by
  obtain ⟨h20,h21⟩ := (Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff _ a).mp ha
  have h := congrArg (fun b : Cover n => b.val 2 2) hs
  change (a.val * a.val) 2 2 = (1 : Mat n) 2 2 at h
  simp only [Matrix.mul_apply,Fin.sum_univ_three,h20,h21,zero_mul,zero_add,
    Matrix.one_apply_eq] at h
  exact (sq_eq_one_iff.mp (by simpa only [pow_two] using h)).elim id (fun h => by simpa only [CharTwo.neg_eq] using h)

omit [NeZero n] in
private theorem transvection_square (i j : Fin 3) (hij : i ≠ j) :
    let a := SpecialLinearGroup.transvection hij (1 : E n)
    a * a = 1 := by
  dsimp
  rw [← SpecialLinearGroup.transvection_add, CharTwo.add_self_eq_zero]
  apply Subtype.ext
  simp

private theorem point_column (g : GeneralLinearGroup (Fin 3) (E n))
    (hg : binaryCongruence n g ∈ normalizer (pointParabolicImage n : Set (BinaryAut n)))
    (j : Fin 3) (hj : (0 : Fin 3) ≠ j) : g.val j 0 = 0 := by
  let a : Cover n := SpecialLinearGroup.transvection hj 1
  have ha : a ∈ coverPointParabolic n := by
    rw [coverPointParabolic, Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff]
    simp [a, SpecialLinearGroup.transvection_coe]
  have hgi : binaryCongruence n g⁻¹ ∈
      normalizer (pointParabolicImage n : Set (BinaryAut n)) := by
    rw [map_inv]
    exact (normalizer _).inv_mem hg
  let b := coverConj n g⁻¹ a
  have hb : b ∈ coverPointParabolic n := conj_point n g⁻¹ hgi a ha
  have h00 : b.val 0 0 = 1 :=
    point_involution_diagonal n b hb (conj_square n g⁻¹ a (transvection_square n 0 j hj))
  obtain ⟨h10,h20⟩ := (Matrix.PSL3.LinearThree.mem_pointParabolicSL_iff _ b).mp hb
  have he : g * SpecialLinearGroup.toGL b = SpecialLinearGroup.toGL a * g := by
    dsimp [b]
    rw [coverConj_toGL]
    group
  have h := congrArg (fun c : GeneralLinearGroup (Fin 3) (E n) => c.val 0 0) he
  change (g.val * b.val) 0 0 = (a.val * g.val) 0 0 at h
  rw [show a.val = Matrix.transvection 0 j 1 from rfl,
    Matrix.transvection_mul_apply_same] at h
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h00,h10,h20,mul_one,mul_zero,
    add_zero,one_mul] at h
  exact add_left_cancel (show g.val 0 0 + g.val j 0 = g.val 0 0 + 0 by simpa using h.symm)

private theorem plane_row (g : GeneralLinearGroup (Fin 3) (E n))
    (hg : binaryCongruence n g ∈ normalizer (planeParabolicImage n : Set (BinaryAut n)))
    (i : Fin 3) (hi : i ≠ (2 : Fin 3)) : g.val 2 i = 0 := by
  let a : Cover n := SpecialLinearGroup.transvection hi 1
  have ha : a ∈ coverPlaneParabolic n := by
    rw [coverPlaneParabolic, Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff]
    simp [a, SpecialLinearGroup.transvection_coe]
  let b := coverConj n g a
  have hb : b ∈ coverPlaneParabolic n := conj_plane n g hg a ha
  have h22 : b.val 2 2 = 1 :=
    plane_involution_diagonal n b hb (conj_square n g a (transvection_square n i 2 hi))
  obtain ⟨h20,h21⟩ := (Matrix.PSL3.LinearThree.mem_lineParabolicSL_iff _ b).mp hb
  have he : g * SpecialLinearGroup.toGL a = SpecialLinearGroup.toGL b * g := by
    dsimp [b]
    rw [coverConj_toGL]
    group
  have h := congrArg (fun c : GeneralLinearGroup (Fin 3) (E n) => c.val 2 2) he
  change (g.val * a.val) 2 2 = (b.val * g.val) 2 2 at h
  rw [show a.val = Matrix.transvection i 2 1 from rfl,
    Matrix.mul_transvection_apply_same] at h
  simp only [Matrix.mul_apply, Fin.sum_univ_three, h22,h20,h21,one_mul,zero_mul,
    zero_add] at h
  exact add_left_cancel (show g.val 2 2 + g.val 2 i = g.val 2 2 + 0 by simpa using h)

/-- Normalization of either marked Hermitian image parabolic recovers its
natural point or plane. The original scalar kernel is retained. -/
theorem congruenceParabolicRecovery : CongruenceParabolicRecovery n := by
  intro g hg
  rcases hg with hp | hl
  · exact Or.inl ⟨point_column n g hp 1 (by decide), point_column n g hp 2 (by decide)⟩
  · exact Or.inr ⟨plane_row n g hl 0 (by decide), plane_row n g hl 1 (by decide)⟩

end Representation.HermitianTensorThree.ParabolicTorus.OddExponent
