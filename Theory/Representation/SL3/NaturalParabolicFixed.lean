module
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeLargeField
public import Theory.Representation.SL3.ParabolicSubgroups
public import Theory.Representation.FirstCohomologyConjugationSplitting

/-!
# Fixed vectors for the natural SL₃ line parabolic

Three elementary transvections force all coordinates of a fixed vector
to vanish. The same holds for two natural summands. Together with the
proved vanishing of natural SL₃ first cohomology over nonbinary fields,
these are the two representation inputs to original 4.3.9.

The subgroup is the covector stabilizer `lineLocalSL`, whose preserved
projective line is a vector plane. The point stabilizer has nonzero
fixed vectors and cannot replace it in this calculation.
Source: Aschbacher--Smith, original 4.3.9, printed p.616.
-/

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
namespace Representation.SL3ParabolicNatural
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F]

theorem line_fixed_zero (v : Fin 3 → F)
    (hv : ∀ g ∈ lineLocalSL F, specialLinearNatural 3 g v = v) : v = 0 := by
  have ht {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 2) :
      transvection hij (1 : F) ∈ lineLocalSL F := by
    rw [mem_lineLocalSL_iff]
    simp [transvection_coe, hi]
  have hc {i j : Fin 3} (hij : i ≠ j) (hi : i ≠ 2) : v j = 0 := by
    have h := congrFun (hv (transvection hij 1) (ht hij hi)) i
    rw [OneCohomology.SLHigherNatural.action_transvection] at h
    simpa using h
  ext i
  fin_cases i
  · exact hc (by decide : (1 : Fin 3) ≠ 0) (by decide)
  · exact hc (by decide : (0 : Fin 3) ≠ 1) (by decide)
  · exact hc (by decide : (0 : Fin 3) ≠ 2) (by decide)

theorem line_prod_fixed_zero (v : (Fin 3 → F) × (Fin 3 → F))
    (hv : ∀ g ∈ lineLocalSL F,
      (specialLinearNatural 3).prod (specialLinearNatural 3) g v = v) : v = 0 := by
  exact Prod.ext (line_fixed_zero v.1 (fun g hg => congrArg Prod.fst (hv g hg)))
    (line_fixed_zero v.2 (fun g hg => congrArg Prod.snd (hv g hg)))
end Representation.SL3ParabolicNatural
