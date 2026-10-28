module

public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Explicit SU₃ words in opposite root groups

For the standard antidiagonal Hermitian form in characteristic two, the Weyl
matrix is a product of three elements from the two opposite root groups.
The root–Weyl identity then produces every torus element: norm surjectivity
allows any nonzero field element as the second root coordinate. These
calculations include the field of order four and do not use perfectness.

The matrix calculation for `su_weyl_mul_root_mul_weyl` is adapted from the
GL identity inside `External.hermitianWeylPSU_mul_unipotent_mul_weyl`, retaining
its equality in SU rather than passing to PGL.

Sources: Huppert II.10.12; Aschbacher–Smith, F.1.3(1), printed pp.259–260.
The passage from these words to generation of all SU requires the Bruhat
coverage proved separately; no coverage assertion is made in this module.
-/

open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Matrix
namespace CFSG.Quasithin.ChapterF.Source.Unitary
variable {K : Type*} [Field K] (J : HermitianForm 3 K)
variable (hs : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The root–Weyl identity holds in SU itself, retaining all scalar factors. -/
public theorem su_weyl_mul_root_mul_weyl (z : hermitianUnipotentCoord J) (hz : z.1.2 ≠ 0) :
    hermitianWeylSU J hs * hermitianUnipotentSU J hs z * hermitianWeylSU J hs =
      hermitianUnipotentSU J hs (hermitianBruhatLeft J z hz) *
        hermitianTorusSU J hs (Units.mk0 z.1.2 hz) * hermitianWeylSU J hs *
        hermitianUnipotentSU J hs (hermitianBruhatRight J z hz) := by
  have hconjz : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hz
  have hGL :
      hermitianWeylGL (K := K) * hermitianUnipotentGL J z *
            hermitianWeylGL (K := K) =
        hermitianUnipotentGL J (hermitianBruhatLeft J z hz) *
            hermitianTorusGL J (Units.mk0 z.1.2 hz) *
          hermitianWeylGL (K := K) *
        hermitianUnipotentGL J (hermitianBruhatRight J z hz) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change
      ((hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
          hermitianUnipotentMatrix J z *
          (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K)) i j =
        (hermitianUnipotentMatrix J (hermitianBruhatLeft J z hz) *
          hermitianTorusMatrix J (Units.mk0 z.1.2 hz) *
          (hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) *
          hermitianUnipotentMatrix J (hermitianBruhatRight J z hz)) i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianWeylMatrix, hermitianUnipotentMatrix,
        hermitianTorusMatrix, hermitianBruhatLeft, hermitianBruhatRight,
        Matrix.mul_apply, Fin.sum_univ_three]
    all_goals field_simp [hz, hconjz]
    all_goals try rw [J.conj_involutive]
    all_goals try linear_combination z.1.2 * z.2
    all_goals try (ring_nf; done)
    simpa [add_comm, add_left_comm, add_assoc] using z.2.symm
  exact Subtype.ext hGL


/-- The standard Weyl representative is an involution. -/
public theorem su_weyl_sq : hermitianWeylSU J hs * hermitianWeylSU J hs = 1 := by
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (hermitianWeylMatrix * hermitianWeylMatrix : Matrix (Fin 3) (Fin 3) K) i j =
    (1 : Matrix (Fin 3) (Fin 3) K) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianWeylMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- The inverse of the standard Weyl representative. -/
public theorem su_weyl_inv : (hermitianWeylSU J hs)⁻¹ = hermitianWeylSU J hs :=
  inv_eq_of_mul_eq_one_right (su_weyl_sq J hs)

/-- Every standard torus element normalizes the explicit SU root range. -/
public theorem su_torus_mem_root_normalizer (k : Kˣ) :
    hermitianTorusSU J hs k ∈ Subgroup.normalizer (hermitianUnipotentSU J hs).range := by
  have hconj (l : Kˣ) (z : hermitianUnipotentCoord J) :
      hermitianTorusSU J hs l * hermitianUnipotentSU J hs z *
        (hermitianTorusSU J hs l)⁻¹ =
      hermitianUnipotentSU J hs (hermitianTorusAction J l z) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    exact Subtype.ext (hermitianTorusGL_mul_unipotent J l z)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨hermitianTorusAction J k z, (hconj k z).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨hermitianTorusAction J k⁻¹ z, ?_⟩
    rw [← hconj, map_inv, hz]
    simp [mul_assoc]

/-- Every field element occurs as the second coordinate of a Hermitian root. -/
public theorem exists_root_coord_snd [Finite K] (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (b : K) :
    ∃ z : hermitianUnipotentCoord J, z.1.2 = b := by
  have hc : J.conj (-(b + J.conj b)) = -(b + J.conj b) := by
    rw [map_neg, map_add, J.conj_involutive]; ring
  by_cases hb : -(b + J.conj b) = 0
  · refine ⟨⟨(0, b), ?_⟩, rfl⟩
    simpa using neg_eq_zero.mp hb
  · obtain ⟨a, _, ha⟩ := huppert_II_10_4_norm_surjective J q hcard hfixed _ hc hb
    exact ⟨⟨(a, b), by dsimp; rw [ha]; ring⟩, rfl⟩

/-- In characteristic two, the two opposite root groups contain the Weyl element. -/
public theorem su_weyl_mem_opposite_join [CharP K 2] :
    hermitianWeylSU J hs ∈
      (hermitianUnipotentSU J hs).range ⊔
        (hermitianUnipotentSU J hs).range.map (MulAut.conj (hermitianWeylSU J hs)) := by
  let z : hermitianUnipotentCoord J := ⟨(0, 1), by simp [CharTwo.add_self_eq_zero]⟩
  let u := hermitianUnipotentSU J hs z
  let w := hermitianWeylSU J hs
  let H := (hermitianUnipotentSU J hs).range ⊔
    (hermitianUnipotentSU J hs).range.map (MulAut.conj w)
  have hu : u ∈ H := Subgroup.mem_sup_left (show u ∈ (hermitianUnipotentSU J hs).range from ⟨z, rfl⟩)
  have hop : w * u * w⁻¹ ∈ H :=
    Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨u, ⟨z, rfl⟩, rfl⟩)
  have heq : u * (w * u * w⁻¹) * u = w := by
    dsimp [w]
    rw [su_weyl_inv]
    apply Subtype.ext
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    change (hermitianUnipotentMatrix J z *
      (hermitianWeylMatrix * hermitianUnipotentMatrix J z * hermitianWeylMatrix) *
      hermitianUnipotentMatrix J z : Matrix (Fin 3) (Fin 3) K) i j = hermitianWeylMatrix i j
    fin_cases i <;> fin_cases j <;>
      simp [z, hermitianUnipotentMatrix, hermitianWeylMatrix, Matrix.mul_apply,
        Fin.sum_univ_three, CharTwo.add_self_eq_zero]
    exact (CharTwo.neg_eq _).symm
  change w ∈ H
  rw [← heq]
  exact H.mul_mem (H.mul_mem hu hop) hu

/-- Over a quadratic finite field in characteristic two, opposite roots contain the full torus. -/
public theorem su_torus_mem_opposite_join [Finite K] [CharP K 2] (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q) (k : Kˣ) :
    hermitianTorusSU J hs k ∈
      (hermitianUnipotentSU J hs).range ⊔
        (hermitianUnipotentSU J hs).range.map (MulAut.conj (hermitianWeylSU J hs)) := by
  let H := (hermitianUnipotentSU J hs).range ⊔
    (hermitianUnipotentSU J hs).range.map (MulAut.conj (hermitianWeylSU J hs))
  have hu (z : hermitianUnipotentCoord J) : hermitianUnipotentSU J hs z ∈ H :=
    Subgroup.mem_sup_left (show hermitianUnipotentSU J hs z ∈ (hermitianUnipotentSU J hs).range from ⟨z, rfl⟩)
  have hw : hermitianWeylSU J hs ∈ H := su_weyl_mem_opposite_join J hs
  obtain ⟨z, hz⟩ := exists_root_coord_snd J q hcard hfixed (k : K)
  have hz0 : z.1.2 ≠ 0 := hz ▸ Units.ne_zero k
  have heq := su_weyl_mul_root_mul_weyl J hs z hz0
  have hk : Units.mk0 z.1.2 hz0 = k := Units.ext hz
  rw [hk] at heq
  have hm : hermitianUnipotentSU J hs (hermitianBruhatLeft J z hz0) *
      hermitianTorusSU J hs k * hermitianWeylSU J hs *
      hermitianUnipotentSU J hs (hermitianBruhatRight J z hz0) ∈ H :=
    heq ▸ H.mul_mem (H.mul_mem hw (hu z)) hw
  have h1 := H.mul_mem hm (H.inv_mem (hu (hermitianBruhatRight J z hz0)))
  have h2 := H.mul_mem h1 (H.inv_mem hw)
  have h3 := H.mul_mem (H.inv_mem (hu (hermitianBruhatLeft J z hz0))) h2
  simpa only [mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel_left] using h3

end CFSG.Quasithin.ChapterF.Source.Unitary
