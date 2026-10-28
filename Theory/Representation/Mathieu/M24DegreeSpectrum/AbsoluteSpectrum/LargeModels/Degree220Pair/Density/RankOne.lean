module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density.Recurrences

public import Mathlib.Algebra.Field.ZMod

/-!
# Rank-one membership from a cyclic matrix

If C kills a column v and a row λ, then vλ commutes with C. A checked
cyclic basis for C therefore places vλ in every subalgebra containing C.
This avoids dense evaluation of the exploratory degree-219 polynomial for
the two ATLAS degree-220 pairs. The final applications use the literal
column and row vectors from Density/source/density-witnesses.json.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density
open Matrix

/-- A cyclic matrix's two null vectors give a rank-one element of its algebra. -/
theorem rankOne_mem_of_cyclic_rows {F : Type*} [Field F] {n : ℕ}
    (S : Subalgebra F (Matrix (Fin n) (Fin n) F))
    (C X Xi : Matrix (Fin n) (Fin n) F) (v lam seed : Fin n → F)
    (hC : C ∈ S) (hCv : C.mulVec v = 0) (hlC : vecMul lam C = 0)
    (hX : ∀ i : Fin n, X i = vecMul seed (C ^ i.val))
    (hXi : Xi * X = 1) : vecMulVec v lam ∈ S := by
  apply commuting_mem_of_cyclic_rows S C (vecMulVec v lam) X Xi seed hC ?_ hX hXi
  change C * vecMulVec v lam = vecMulVec v lam * C
  rw [mul_vecMulVec, vecMulVec_mul, hCv, hlC]
  ext i j
  simp

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree220Pair.Density
