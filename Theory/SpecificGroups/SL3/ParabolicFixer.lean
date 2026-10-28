module
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ResidualRigidity
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Pointwise rigidity of the full special-linear parabolic residuals

An automorphism fixing either standard affine residual of a degree-three
parabolic is the identity. Projective root rigidity first proves this for
PSL₃; injectivity of automorphism descent through a perfect central cover
then retains the entire SL₃ group, including its cubic center.

This is the model obstruction used in Aschbacher--Smith, original 4.3.7,
printed pp.615--616, for the SL₃ row of C.4.1(3), pp.151--153. The residuals
are the actual point-vector and line-covector stabilizers, not the full
parabolics. No source configuration or placement assumption enters this
model calculation.
-/

public section
open Subgroup
open Matrix.PSL3Even.UnipotentGeometry
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem projective_fixer_eq_one {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (P : Subgroup PSL(3,F)) (hU : unipotent F ≤ P) (hB : ¬ P ≤ borel F)
    (a : MulAut PSL(3,F)) (ha : ∀ x ∈ P, a x = x) : a = 1 := by
  obtain ⟨r,rfl⟩ := ResidualRigidity.fixer_unipotent_is_root_inner hn hF a
    (fun x => ha x (hU x.property))
  by_cases hr : r = 0
  · subst r
    have he : (⟨0,0,0⟩ : U F) = 1 := rfl
    rw [he,map_one,map_one]
  · exfalso
    apply hB
    apply le_trans _ (ResidualRigidity.root_centralizer_le_borel r hr)
    intro x hx
    rw [mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.mp (ha x hx)).symm

theorem specialLinear_fixer_eq_one {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (P : Subgroup SL(3,F)) (hU : unipotentSL F ≤ P) (hB : ¬ P ≤ borelSL F)
    (a : MulAut SL(3,F)) (ha : ∀ x ∈ P, a x = x) : a = 1 := by
  let f : PerfectCentralCovering.Cover SL(3,F) PSL(3,F) :=
    { toMonoidHom := projection F
      surjective := QuotientGroup.mk'_surjective _
      isPerfect := Atlas.sl_perfect 3 (by decide)
      ker_le_center := (projection_ker F).le }
  have hk : f.toMonoidHom.ker = center SL(3,F) := projection_ker F
  have hprojective : f.autMap hk a = 1 := by
    apply projective_fixer_eq_one hn hF (P.map (projection F)) (map_mono hU)
    · intro hle
      apply hB
      rw [← borel_comap F]
      exact (map_le_iff_le_comap).mp hle
    · rintro x ⟨y,hy,rfl⟩
      change f.autMap hk a (f.toMonoidHom y) = f.toMonoidHom y
      rw [f.autMap_apply hk a y,ha y hy]
  exact f.autMap_injective hk (hprojective.trans (map_one _).symm)

theorem pointLocalSL_fixer_eq_one {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut SL(3,F)) (ha : ∀ x ∈ pointLocalSL F, a x = x) : a = 1 := by
  apply specialLinear_fixer_eq_one hn hF _ inf_le_left ?_ a ha
  intro hle
  let g := Matrix.SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (1 : F)
  have hg : g ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [g,Matrix.SpecialLinearGroup.transvection_coe]
  have he := (mem_borelSL_iff F g).mp (hle hg)
  simpa [g,Matrix.SpecialLinearGroup.transvection_coe] using he.2.2

theorem lineLocalSL_fixer_eq_one {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut SL(3,F)) (ha : ∀ x ∈ lineLocalSL F, a x = x) : a = 1 := by
  apply specialLinear_fixer_eq_one hn hF _ inf_le_right ?_ a ha
  intro hle
  let g := Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F)
  have hg : g ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    simp [g,Matrix.SpecialLinearGroup.transvection_coe]
  have he := (mem_borelSL_iff F g).mp (hle hg)
  simpa [g,Matrix.SpecialLinearGroup.transvection_coe] using he.1

end Matrix.PSL3.LinearThree
