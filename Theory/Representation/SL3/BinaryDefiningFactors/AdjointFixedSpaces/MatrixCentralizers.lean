module

public import Theory.Representation.SL3.BinaryDefiningFactors
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Trace-zero matrix centralizers of the two SL₃ root planes

For a nonidentity element of a coordinate root plane, four entries determine
a commuting trace-zero matrix. In characteristic two, two entries suffice
for a matrix commuting with the whole plane. Reversing the coordinates after
transposing exchanges the point and line calculations. The results are stated
for an arbitrary injectively parametrized matrix space, so that the actual
adjoint fixed spaces can be substituted without changing their carriers.

Source: Guralnick–Malle, Classification of 2F-modules II, author manuscript
Lemma 4.5, pp.23–24, paragraph 2. These uniform calculations implement its
centralizer comparison in dimension three.
-/

public section
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

private theorem point_kernel (M : Matrix (Fin 3) (Fin 3) K) (a c : K)
    (hc : M * matrix K ⟨a,0,c⟩ = matrix K ⟨a,0,c⟩ * M)
    (ht : Matrix.trace M = 0) (h00 : M 0 0 = 0) (h01 : M 0 1 = 0)
    (h02 : M 0 2 = 0)
    (ha : a ≠ 0 ∧ M 2 1 = 0 ∨ c ≠ 0 ∧ M 1 2 = 0) : M = 0 := by
  have he (i j : Fin 3) := congrFun (congrFun hc i) j
  have htr : M 0 0 + M 1 1 + M 2 2 = 0 := by
    simpa [Matrix.trace, Fin.sum_univ_three] using ht
  rcases ha with ⟨ha,h21⟩ | ⟨hc,h12⟩
  · have h10 : M 1 0 = 0 := by
      have hh := he 1 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, ha] using hh
    have h20 : M 2 0 = 0 := by
      have hh := he 2 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, ha] using hh
    have h11 : M 1 1 = 0 := by
      have hh := he 0 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, h00,h01,h21,ha] using hh.symm
    have h22 : M 2 2 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, h00,h11] using htr
    have h12 : M 1 2 = 0 := by
      have hh := he 0 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, h00,h02,h22,ha] using hh.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h01,h02,h10,h11,h12,h20,h21,h22]
  · have h10 : M 1 0 = 0 := by
      have hh := he 1 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, hc] using hh
    have h20 : M 2 0 = 0 := by
      have hh := he 2 2
      simp [Matrix.mul_apply, Fin.sum_univ_three, matrix] at hh
      exact hh.resolve_right hc
    have h22 : M 2 2 = 0 := by
      have hh := he 0 2
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, h00,h02,h12,hc] using hh.symm
    have h11 : M 1 1 = 0 := by simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, h00,h22] using htr
    have h21 : M 2 1 = 0 := by
      have hh := he 0 1
      simpa [Matrix.mul_apply, Fin.sum_univ_three, matrix, h00,h01,h11,hc] using hh.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00,h01,h02,h10,h11,h12,h20,h21,h22]

private def flip (M : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  M.transpose.submatrix Fin.rev Fin.rev

omit [Field K] in
private theorem flip_flip (M : Matrix (Fin 3) (Fin 3) K) : flip (flip M) = M := by
  ext i j
  simp [flip]

private theorem flip_mul (M N : Matrix (Fin 3) (Fin 3) K) :
    flip (M * N) = flip N * flip M := by
  simp only [flip, Matrix.transpose_mul]
  exact (Matrix.submatrix_mul_equiv _ _ Fin.rev Fin.revPerm Fin.rev).symm

private theorem flip_line (b c : K) : flip (matrix K ⟨0,b,c⟩) = matrix K ⟨b,0,c⟩ := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem flip_trace (M : Matrix (Fin 3) (Fin 3) K) :
    Matrix.trace (flip M) = Matrix.trace M := by
  simp [Matrix.trace, Fin.sum_univ_three, flip, Matrix.submatrix, Matrix.transpose_apply]
  ring

private theorem point_plane_kernel [CharP K 2] (M : Matrix (Fin 3) (Fin 3) K)
    (h1 : M * matrix K ⟨1,0,0⟩ = matrix K ⟨1,0,0⟩ * M)
    (h2 : M * matrix K ⟨0,0,1⟩ = matrix K ⟨0,0,1⟩ * M)
    (ht : Matrix.trace M = 0) (h01 : M 0 1 = 0) (h02 : M 0 2 = 0) : M = 0 := by
  have h11 := congrFun (congrFun h1 0) 1
  have h22 := congrFun (congrFun h2 0) 2
  have h21 := congrFun (congrFun h2 0) 1
  simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h11 h22 h21
  have h00 : M 0 0 = 0 := by
    have htr : M 0 0 + M 1 1 + M 2 2 = 0 := by
      simpa [Matrix.trace, Fin.sum_univ_three] using ht
    have he11 : M 0 0 = M 1 1 := by linear_combination h11
    have he22 : M 0 0 = M 2 2 := by linear_combination h22
    rw [← he11, ← he22, CharTwo.add_self_eq_zero, zero_add] at htr
    exact htr
  exact point_kernel M 1 0 h1 ht h00 h01 h02 (Or.inl ⟨one_ne_zero,h21⟩)

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem finrank_le_four_of_point_commutes (f : W →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hf : Function.Injective f) (a c : K) (ha : a ≠ 0 ∨ c ≠ 0)
    (ht : ∀ v, Matrix.trace (f v) = 0)
    (hc : ∀ v, f v * matrix K ⟨a,0,c⟩ = matrix K ⟨a,0,c⟩ * f v) :
    Module.finrank K W ≤ 4 := by
  classical
  let coordinates : W →ₗ[K] (Fin 4 → K) :=
    { toFun := fun v => ![f v 0 0, f v 0 1, f v 0 2,
        if a = 0 then f v 1 2 else f v 2 1]
      map_add' := by intro v w; ext i; fin_cases i <;> (by_cases h : a = 0 <;> simp [h])
      map_smul' := by intro t v; ext i; fin_cases i <;> (by_cases h : a = 0 <;> simp [h]) }
  have hi : Function.Injective coordinates := by
    apply (LinearMap.ker_eq_bot).mp
    apply _root_.eq_bot_iff.mpr
    intro v hv
    change coordinates v = 0 at hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    have h3 := congrFun hv 3
    dsimp [coordinates] at h0 h1 h2 h3
    apply hf
    rw [map_zero]
    apply point_kernel _ a c (hc v) (ht v) h0 h1 h2
    by_cases hz : a = 0
    · exact Or.inr ⟨ha.resolve_left (not_not.mpr hz), by simpa [hz] using h3⟩
    · exact Or.inl ⟨hz, by simpa [hz] using h3⟩
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  simpa using hh

private def flipLinear : Matrix (Fin 3) (Fin 3) K →ₗ[K] Matrix (Fin 3) (Fin 3) K where
  toFun := flip
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_le_four_of_line_commutes (f : W →ₗ[K] Matrix (Fin 3) (Fin 3) K)
    (hf : Function.Injective f) (b c : K) (hb : b ≠ 0 ∨ c ≠ 0)
    (ht : ∀ v, Matrix.trace (f v) = 0)
    (hc : ∀ v, f v * matrix K ⟨0,b,c⟩ = matrix K ⟨0,b,c⟩ * f v) :
    Module.finrank K W ≤ 4 := by
  apply finrank_le_four_of_point_commutes (flipLinear.comp f)
    ((Function.LeftInverse.injective flip_flip).comp hf) b c hb
  · intro v
    exact (flip_trace (f v)).trans (ht v)
  · intro v
    change flip (f v) * _ = _ * flip (f v)
    have h := congrArg flip (hc v)
    simpa only [flip_mul, flip_line] using h.symm

theorem finrank_le_two_of_point_plane_commutes [CharP K 2]
    (f : W →ₗ[K] Matrix (Fin 3) (Fin 3) K) (hf : Function.Injective f)
    (ht : ∀ v, Matrix.trace (f v) = 0)
    (h1 : ∀ v, f v * matrix K ⟨1,0,0⟩ = matrix K ⟨1,0,0⟩ * f v)
    (h2 : ∀ v, f v * matrix K ⟨0,0,1⟩ = matrix K ⟨0,0,1⟩ * f v) :
    Module.finrank K W ≤ 2 := by
  let coordinates : W →ₗ[K] (K × K) :=
    { toFun := fun v => (f v 0 1, f v 0 2)
      map_add' := by intro v w; simp
      map_smul' := by intro t v; simp }
  have hi : Function.Injective coordinates := by
    apply (LinearMap.ker_eq_bot).mp
    apply _root_.eq_bot_iff.mpr
    intro v hv
    change coordinates v = 0 at hv
    apply hf
    rw [map_zero]
    exact point_plane_kernel _ (h1 v) (h2 v) (ht v)
      (congrArg Prod.fst hv) (congrArg Prod.snd hv)
  have hh := LinearMap.finrank_le_finrank_of_injective hi
  simpa using hh

theorem finrank_le_two_of_line_plane_commutes [CharP K 2]
    (f : W →ₗ[K] Matrix (Fin 3) (Fin 3) K) (hf : Function.Injective f)
    (ht : ∀ v, Matrix.trace (f v) = 0)
    (h1 : ∀ v, f v * matrix K ⟨0,1,0⟩ = matrix K ⟨0,1,0⟩ * f v)
    (h2 : ∀ v, f v * matrix K ⟨0,0,1⟩ = matrix K ⟨0,0,1⟩ * f v) :
    Module.finrank K W ≤ 2 := by
  apply finrank_le_two_of_point_plane_commutes (flipLinear.comp f)
    ((Function.LeftInverse.injective flip_flip).comp hf)
  · intro v
    exact (flip_trace (f v)).trans (ht v)
  · intro v
    change flip (f v) * _ = _ * flip (f v)
    have h := congrArg flip (h1 v)
    simpa only [flip_mul, flip_line] using h.symm
  · intro v
    change flip (f v) * _ = _ * flip (f v)
    have h := congrArg flip (h2 v)
    simpa only [flip_mul, flip_line] using h.symm

end Representation.SL3.BinaryDefiningFactors.AdjointFixedSpaces
