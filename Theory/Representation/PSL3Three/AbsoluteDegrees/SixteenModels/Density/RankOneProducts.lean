module

public import Theory.Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density.Data

/-!
# Initial products for the rank-one certificate

Kernel checks for `C=AB`, `C²`, `C³` and `C⁶`. The numeric tables are
`Density.Data`; the finite arithmetic and its field interpretation are proved
in `Density.Arithmetic`. Splitting at this point bounds simultaneous kernel
work for the dense products. Source: ATLAS L33G1-f16r16aB0, as in `Data`.
-/

public section
namespace Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density

theorem product_c : codeProduct codesA codesB = c :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem product_c2 : codeProduct c c = c2 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem product_c3 : codeProduct c2 c = c3 :=
  checkMatrix_sound _ _ (by decide +kernel)

theorem product_c6 : codeProduct c3 c3 = c6 :=
  checkMatrix_sound _ _ (by decide +kernel)

variable {F : Type*} [Field F] [CharP F 2]

theorem product_mem (t : F) (ht : t ^ 4 = t + 1)
    (S : Subalgebra F (Matrix (Fin 16) (Fin 16) F))
    {M N R : Matrix (Fin 16) (Fin 16) (Fin 16)} (h : codeProduct M N = R)
    (hM : evalMatrix t M ∈ S) (hN : evalMatrix t N ∈ S) : evalMatrix t R ∈ S := by
  rw [← h, eval_product t ht]
  exact S.mul_mem hM hN

end Representation.PSL3Three.AbsoluteDegrees.SixteenModels.Density
