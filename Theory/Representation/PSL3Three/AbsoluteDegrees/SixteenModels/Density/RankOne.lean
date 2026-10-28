module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density.RankOneProducts

/-!
# A rank-one element of the generated algebra

Write `C=AB`. The checked addition chain forms `S₃=1+C+C²`,
`S₆=S₃+C³S₃`, `S₁₂=S₆+C⁶S₆`, and `E=1+CS₁₂`.
Thus E belongs to every subalgebra containing A and B. The last check
identifies E with the outer product of the published witness vectors v and λ.
All computations use the literal generator codes, with arbitrary-field
transport through the proved arithmetic checker.

Source: ATLAS L33G1-f16r16aB0, attributed in `SixteenModels.Data`;
the degree-sixteen models underlying GM02 Proposition 4.2, pp.9–10.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density

theorem product_p3 : codeProduct c3 s3 = p3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem product_p6 : codeProduct c6 s6 = p6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem product_p12 : codeProduct c s12 = p12 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem sum_s3 : codeAdd (codeAdd codeOne c) c2 = s3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem sum_s6 : codeAdd s3 p3 = s6 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem sum_s12 : codeAdd s6 p6 = s12 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem sum_e : codeAdd codeOne p12 = e :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem factor_e : codeOuter v lam = e :=
  checkMatrix_sound _ _ (by decide +kernel)

variable {F : Type*} [Field F] [CharP F 2]

theorem rankOne_mem (t : F) (ht : t ^ 4 = t + 1)
    (S : Subalgebra F (Matrix (Fin 16) (Fin 16) F))
    (ha : matrixA t ∈ S) (hb : matrixB t ∈ S) :
    Matrix.vecMulVec (evalVector t v) (evalVector t lam) ∈ S := by
  have hI : evalMatrix t codeOne ∈ S := by rw [eval_one]; exact S.one_mem
  have hc := product_mem t ht S product_c ha hb
  have hc2 := product_mem t ht S product_c2 hc hc
  have hc3 := product_mem t ht S product_c3 hc2 hc
  have hc6 := product_mem t ht S product_c6 hc3 hc3
  have hs3 : evalMatrix t s3 ∈ S := by
    rw [← sum_s3, eval_add, eval_add]
    exact S.add_mem (S.add_mem hI hc) hc2
  have hp3 := product_mem t ht S product_p3 hc3 hs3
  have hs6 : evalMatrix t s6 ∈ S := by
    rw [← sum_s6, eval_add]
    exact S.add_mem hs3 hp3
  have hp6 := product_mem t ht S product_p6 hc6 hs6
  have hs12 : evalMatrix t s12 ∈ S := by
    rw [← sum_s12, eval_add]
    exact S.add_mem hs6 hp6
  have hp12 := product_mem t ht S product_p12 hc hs12
  rw [← eval_outer t ht, factor_e, ← sum_e, eval_add]
  exact S.add_mem hI hp12

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density
