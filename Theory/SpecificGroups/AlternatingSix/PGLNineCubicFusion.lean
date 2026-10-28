module
public import Theory.SpecificGroups.AlternatingSix.PGLNineFiveNormalizer
public import GorensteinWalter.PSL2ProjectiveLine
public import GorensteinWalter.PGammaL2FullSplitTorus
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Cubic fusion in the actual PGL₂(9)

The standard unipotent subgroup has order nine and is a Sylow three-subgroup.
Every cubic conjugates into it. Projective diagonal matrices scale any
nonzero root parameter to one, so all cubics are conjugate in the full PGL₂(9).
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open Atlas.Comparisons.Exceptional GorensteinWalter
namespace AlternatingSix.PGLNineCubicFusion

private def root : Multiplicative Nine.F →* PGL2 Nine.F :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL.comp (psl2UpperUnipotentHom Nine.F)

private def up (a : Nine.F) : PGL2 Nine.F := root (Multiplicative.ofAdd a)

private theorem root_injective : Function.Injective root :=
  Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp psl2UpperUnipotentHom_injective

private theorem root_card : Nat.card root.range = 9 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective root_injective).toEquiv]
  exact Nine.card

private theorem diagonal_scales (c : Nine.Fˣ) (a : Nine.F) :
    pGammaL2FullSplitTorus Nine.F c * up a * (pGammaL2FullSplitTorus Nine.F c)⁻¹ =
      up ((c : Nine.F)*a) := by
  have hm : pGammaL2FullSplitTorusGL Nine.F c * SpecialLinearGroup.toGL (sl2UpperUnipotent a) =
      SpecialLinearGroup.toGL (sl2UpperUnipotent ((c : Nine.F)*a)) *
        pGammaL2FullSplitTorusGL Nine.F c := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [pGammaL2FullSplitTorusGL,sl2UpperUnipotent,SpecialLinearGroup.toGL,
        Matrix.mul_apply,Fin.sum_univ_two]
  apply mul_inv_eq_iff_eq_mul.mpr
  change ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL Nine.F c) *
      Matrix.ProjectiveSpecialLinearGroup.toPGL (QuotientGroup.mk (sl2UpperUnipotent a)) =
    Matrix.ProjectiveSpecialLinearGroup.toPGL
      (QuotientGroup.mk (sl2UpperUnipotent ((c : Nine.F)*a))) *
      ProjGenLinGroup.mk (pGammaL2FullSplitTorusGL Nine.F c)
  rw [Matrix.ProjectiveSpecialLinearGroup.toPGL_mk,Matrix.ProjectiveSpecialLinearGroup.toPGL_mk]
  rw [←map_mul,←map_mul,hm]

private theorem cubic_isConj_root (x : PGL2 Nine.F) (hx : orderOf x = 3) :
    IsConj x (up 1) := by
  let : Finite (PGL2 Nine.F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hcard : Nat.card (PGL2 Nine.F) = 720 := by
    rw [pgl2_card_formula,Nine.card]
    norm_num
  let S : Sylow 3 (PGL2 Nine.F) := Sylow.ofCard root.range (by
    rw [root_card,hcard]
    decide +kernel)
  obtain ⟨y,hxy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow (n := 1) (by simpa using hx)
  obtain ⟨a,ha⟩ := y.property
  have hya : (y : PGL2 Nine.F) = up a.toAdd := ha.symm
  have ha0 : a.toAdd ≠ 0 := by
    intro hh
    have ha1 : a = 1 := Multiplicative.toAdd.injective hh
    have hy1 : (y : PGL2 Nine.F) = 1 := by
      rw [hya]
      change root a = 1
      rw [ha1,map_one]
    have hx1 : x = 1 := isConj_one_left.mp (hy1 ▸ hxy)
    rw [hx1,orderOf_one] at hx
    contradiction
  have hconj : IsConj (up a.toAdd) (up 1) := by
    refine isConj_iff.mpr ⟨pGammaL2FullSplitTorus Nine.F (Units.mk0 a.toAdd ha0)⁻¹,?_⟩
    simpa only [Units.val_inv_eq_inv_val,Units.val_mk0,inv_mul_cancel₀ ha0] using
      diagonal_scales (Units.mk0 a.toAdd ha0)⁻¹ a.toAdd
  exact (hya ▸ hxy).trans hconj

/-- All elements of order three in the actual projective group are conjugate. -/
theorem cubic_isConj (x y : PGL2 Nine.F) (hx : orderOf x = 3) (hy : orderOf y = 3) :
    IsConj x y :=
  (cubic_isConj_root x hx).trans (cubic_isConj_root y hy).symm

end AlternatingSix.PGLNineCubicFusion
