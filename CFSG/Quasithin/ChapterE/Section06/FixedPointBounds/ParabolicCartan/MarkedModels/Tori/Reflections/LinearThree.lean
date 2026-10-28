module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.LinearThree
public import Mathlib.Algebra.CharP.Two
/-!
# Reflection of the marked linear-three cyclic torus

The first-two-coordinate permutation matrix is special linear in
characteristic two. It interchanges a and its inverse in the specified
point torus diag(a,a⁻¹,1). Its lower-left entry excludes it from the original
flag Borel, including after the actual central projective quotient.

Source: Aschbacher--Smith E.6.27, printed p.257, with the marked Borel
models from E.2.2. These witnesses feed the same chosen cyclic subgroup
and Hall-subgroup lifting in the original parabolic consumer.
-/
public section
open Matrix Matrix.PSL3 Matrix.PSL3.LinearThree
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
variable (F : Type*) [Field F] [Finite F] [CharP F 2]

private def linearReflection : SL(3,F) :=
  ⟨!![0,1,0;1,0,0;0,0,1],by simp [Matrix.det_fin_three,CharTwo.neg_eq]⟩

omit [Finite F] in
private theorem linearReflection_intertwine (a : Fˣ) :
    linearReflection F * pointTorus F a = pointTorus F a⁻¹ * linearReflection F := by
  apply Subtype.ext
  change (!![0,1,0;1,0,0;0,0,1] : Matrix (Fin 3) (Fin 3) F) *
    diagonal ![(a:F),((a⁻¹:Fˣ):F),1] =
    diagonal ![((a⁻¹:Fˣ):F),(((a⁻¹)⁻¹:Fˣ):F),1] * !![0,1,0;1,0,0;0,0,1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_diagonal,Matrix.diagonal_mul]

theorem exists_psl3Torus_reflection :
    ∃ w : PSL(3,F), w ∉ borel F ∧ ∀ a : Fˣ,
      w * (psl3Torus F a : PSL(3,F)) * w⁻¹ = (psl3Torus F a : PSL(3,F))⁻¹ := by
  refine ⟨projection F (linearReflection F),?_,?_⟩
  · intro hw
    have hh : linearReflection F ∈ borelSL F := (borel_comap F) ▸ hw
    have he := ((mem_borelSL_iff F _).mp hh).1
    simp [linearReflection] at he
  · intro a
    change projection F (linearReflection F) * projection F (pointTorus F a) *
      (projection F (linearReflection F))⁻¹ = (projection F (pointTorus F a))⁻¹
    rw [← map_inv,← map_mul,← map_mul,← map_inv]
    apply congrArg (projection F)
    have hi : pointTorus F a⁻¹ = (pointTorus F a)⁻¹ :=
      congrArg Subtype.val (map_inv (sl3Torus F) a)
    rw [linearReflection_intertwine,mul_inv_cancel_right,hi]
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori
