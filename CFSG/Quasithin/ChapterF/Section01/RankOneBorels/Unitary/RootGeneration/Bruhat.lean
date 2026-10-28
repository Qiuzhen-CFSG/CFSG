module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.RootGeneration.RootIdentities

/-!
# Bruhat coverage for the standard SU₃ matrix group

Every determinant-one isometry of the antidiagonal Hermitian form is either
`U u * T k` or `U u * W * T k * U v`, with equality in SU itself. The proof
works over any field carrying the given involution, so in particular includes
the finite-field case q = 2 without a simplicity or perfectness assumption.

An isotropic column with nonzero bottom entry c is reduced to `(0,0,c)` by
the inverse root with coordinates `(-conj(y/c), x/c)`. If the bottom-left entry
is zero, isotropy forces the middle-left entry to vanish; reducing the last
column then gives a diagonal torus element. Otherwise reduce the first column
and apply the Weyl matrix to reach the small cell. Torus conjugation gives the
stated order of factors.

The diagonal calculation follows the two-point stabilizer calculation in
`BenderSuzuki.External.Huppert.II.theorem_10_12`, retaining its equality in SU.
Sources: Huppert II.10.12; Aschbacher–Smith, F.1.3(1), printed pp.259–260.
This module supplies the coverage premise for the separate generation assembly.
-/

open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Matrix
namespace CFSG.Quasithin.ChapterF.Source.Unitary
variable {K : Type*} [Field K] (J : HermitianForm 3 K)
variable (hs : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
private abbrev mat (g : J.specialSubgroup) : Matrix (Fin 3) (Fin 3) K := g.val.val
private theorem conj_conj (x : K) : J.conj (J.conj x) = x := J.conj_involutive x
include hs in
private theorem pairing (g : J.specialSubgroup) (i j : Fin 3) :
    J.conj (mat J g 2 i) * mat J g 0 j +
    J.conj (mat J g 1 i) * mat J g 1 j +
    J.conj (mat J g 0 i) * mat J g 2 j = J.form i j := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M i j)
    ((J.mem_specialSubgroup_iff g.val).mp g.property).1
  simpa [hs, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three] using h

-- Fixing both coordinate lines forces an exact torus matrix, by determinant one.
private theorem diagonal (g : J.specialSubgroup)
    (h10 : mat J g 1 0 = 0) (h20 : mat J g 2 0 = 0)
    (h02 : mat J g 0 2 = 0) (h12 : mat J g 1 2 = 0) :
    ∃ k : Kˣ, g = hermitianTorusSU J hs k := by
  let M := mat J g
  have hac : J.conj (M 0 0) * M 2 2 = 1 := by
    simpa [M, hs, h10, h20] using pairing J hs g 0 2
  have hc : M 2 2 ≠ 0 := (mul_ne_zero_iff.mp (hac ▸ one_ne_zero)).2
  have ha : J.conj (M 0 0) ≠ 0 := (mul_ne_zero_iff.mp (hac ▸ one_ne_zero)).1
  have hcc : J.conj (M 2 2) ≠ 0 := (map_ne_zero J.conj).2 hc
  have h21 : M 2 1 = 0 := by
    have h : J.conj (M 0 0) * M 2 1 = 0 := by
      simpa [M, hs, h10, h20] using pairing J hs g 0 1
    exact (mul_eq_zero.mp h).resolve_left ha
  have h01 : M 0 1 = 0 := by
    have h : J.conj (M 2 2) * M 0 1 = 0 := by
      simpa [M, hs, h02, h12] using pairing J hs g 2 1
    exact (mul_eq_zero.mp h).resolve_left hcc
  have haDiag : M 0 0 = (J.conj (M 2 2))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [map_mul, conj_conj] using congrArg J.conj hac
  have hdet := congrArg Units.val ((J.mem_specialSubgroup_iff g.val).mp g.property).2
  have hd : M 0 0 * M 1 1 * M 2 2 = 1 := by
    simpa [M, mat, Matrix.det_fin_three, h10, h20, h02, h12, h01, h21] using hdet
  have hm : M 1 1 = J.conj (M 2 2) * (M 2 2)⁻¹ := by
    rw [haDiag] at hd
    field_simp at hd ⊢
    linear_combination hd
  refine ⟨Units.mk0 (M 2 2) hc, ?_⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change M i j = (hermitianTorusMatrix J (Units.mk0 (M 2 2) hc)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, h01, h21, hm, haDiag, M, h10, h20, h02, h12]

-- Isotropy supplies the root-coordinate relation needed for column elimination.
private theorem normalize_column (g : J.specialSubgroup) (j : Fin 3)
    (hiso : J.form j j = 0) (hc : mat J g 2 j ≠ 0) :
    ∃ u : hermitianUnipotentCoord J,
      mat J ((hermitianUnipotentSU J hs u)⁻¹ * g) 0 j = 0 ∧
      mat J ((hermitianUnipotentSU J hs u)⁻¹ * g) 1 j = 0 := by
  let x := mat J g 0 j
  let y := mat J g 1 j
  let c := mat J g 2 j
  have hc' : c ≠ 0 := hc
  have hcc : J.conj c ≠ 0 := (map_ne_zero J.conj).2 hc
  have hi : J.conj c * x + J.conj y * y + J.conj x * c = 0 := by
    simpa [x, y, c, hiso] using pairing J hs g j j
  have hu : x / c + J.conj (x / c) + (-J.conj (y / c)) * J.conj (-J.conj (y / c)) = 0 := by
    simp only [map_div₀, map_neg, conj_conj, neg_mul_neg]
    field_simp [hc, hc', hcc]
    linear_combination hi
  let u : hermitianUnipotentCoord J := ⟨(-J.conj (y / c), x / c), hu⟩
  refine ⟨u, ?_, ?_⟩
  all_goals rw [← map_inv]
  all_goals change (hermitianUnipotentMatrix J (hermitianUnipotentInv J u) * mat J g) _ j = 0
  all_goals simp [hermitianUnipotentMatrix, hermitianUnipotentInv, u,
    Matrix.mul_apply, Fin.sum_univ_three, map_div₀, conj_conj]
  all_goals dsimp [x, y, c] at hi hc hcc ⊢
  · field_simp [hc, hc', hcc]
    linear_combination hi
  · field_simp [hc, hcc]
    ring

private theorem small_cell (g : J.specialSubgroup) (h20 : mat J g 2 0 = 0) :
    ∃ u : hermitianUnipotentCoord J, ∃ k : Kˣ,
      g = hermitianUnipotentSU J hs u * hermitianTorusSU J hs k := by
  have hp : J.conj (mat J g 1 0) * mat J g 1 0 = 0 := by
    simpa [hs, h20] using pairing J hs g 0 0
  have h10 : mat J g 1 0 = 0 := by
    rcases mul_eq_zero.mp hp with h | h
    · exact (map_eq_zero J.conj).mp h
    · exact h
  have hac : J.conj (mat J g 0 0) * mat J g 2 2 = 1 := by
    simpa [hs, h10, h20] using pairing J hs g 0 2
  have hc : mat J g 2 2 ≠ 0 := (mul_ne_zero_iff.mp (hac ▸ one_ne_zero)).2
  obtain ⟨u, hu0, hu1⟩ := normalize_column J hs g 2 (by simp [hs]) hc
  have hlow (i : Fin 3) (hi : i = 1 ∨ i = 2) :
      mat J ((hermitianUnipotentSU J hs u)⁻¹ * g) i 0 = 0 := by
    rw [← map_inv]
    change (hermitianUnipotentMatrix J (hermitianUnipotentInv J u) * mat J g) i 0 = 0
    rcases hi with rfl | rfl <;>
      simp [hermitianUnipotentMatrix, Matrix.mul_apply, Fin.sum_univ_three, h10, h20]
  obtain ⟨k, hk⟩ := diagonal J hs ((hermitianUnipotentSU J hs u)⁻¹ * g)
    (hlow 1 (Or.inl rfl)) (hlow 2 (Or.inr rfl)) hu0 hu1
  exact ⟨u, k, by rw [← hk]; simp⟩

/-- Exact Bruhat coverage in the standard special unitary matrix group. -/
public theorem su_bruhat_coverage (g : J.specialSubgroup) :
    (∃ u : hermitianUnipotentCoord J, ∃ k : Kˣ,
      g = hermitianUnipotentSU J hs u * hermitianTorusSU J hs k) ∨
    (∃ u : hermitianUnipotentCoord J, ∃ k : Kˣ, ∃ v : hermitianUnipotentCoord J,
      g = hermitianUnipotentSU J hs u * hermitianWeylSU J hs *
        hermitianTorusSU J hs k * hermitianUnipotentSU J hs v) := by
  by_cases hc : mat J g 2 0 = 0
  · exact Or.inl (small_cell J hs g hc)
  obtain ⟨u, hu0, _⟩ := normalize_column J hs g 0 (by simp [hs]) hc
  let h := (hermitianUnipotentSU J hs u)⁻¹ * g
  have hh : mat J (hermitianWeylSU J hs * h) 2 0 = 0 := by
    change (hermitianWeylMatrix * mat J h : Matrix (Fin 3) (Fin 3) K) 2 0 = 0
    simpa [hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three] using hu0
  obtain ⟨r, k, hk⟩ := small_cell J hs (hermitianWeylSU J hs * h) hh
  let v := hermitianTorusAction J k⁻¹ r
  have ht : (hermitianTorusSU J hs k)⁻¹ * hermitianUnipotentSU J hs r =
      hermitianUnipotentSU J hs v * (hermitianTorusSU J hs k)⁻¹ := by
    simpa only [map_inv] using
      (show hermitianTorusSU J hs k⁻¹ * hermitianUnipotentSU J hs r =
          hermitianUnipotentSU J hs v * hermitianTorusSU J hs k⁻¹ from
        Subtype.ext (hermitianTorusGL_mul_unipotent J k⁻¹ r))
  have hmove : hermitianUnipotentSU J hs r * hermitianTorusSU J hs k =
      hermitianTorusSU J hs k * hermitianUnipotentSU J hs v := by
    calc
      _ = hermitianTorusSU J hs k *
          ((hermitianTorusSU J hs k)⁻¹ * hermitianUnipotentSU J hs r) *
          hermitianTorusSU J hs k := by group
      _ = _ := by rw [ht]; group
  refine Or.inr ⟨u, k, v, ?_⟩
  calc
    g = hermitianUnipotentSU J hs u * h := by simp [h]
    _ = hermitianUnipotentSU J hs u * hermitianWeylSU J hs *
        (hermitianWeylSU J hs * h) := by
      symm
      calc
        _ = hermitianUnipotentSU J hs u *
            (hermitianWeylSU J hs * hermitianWeylSU J hs) * h := by group
        _ = _ := by rw [su_weyl_sq, mul_one]
    _ = hermitianUnipotentSU J hs u * hermitianWeylSU J hs *
        (hermitianUnipotentSU J hs r * hermitianTorusSU J hs k) := by rw [hk]
    _ = _ := by rw [hmove]; simp only [mul_assoc]
end CFSG.Quasithin.ChapterF.Source.Unitary
