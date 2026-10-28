module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import Theory.Representation.Triality.OuterDisplacement.TensorCoordinates
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Displacement of a twisted swap on the natural G₂ pair

The ordinary flip on a six-by-six tensor moves at least fifteen dimensions:
strict upper-triangular entries inject into its displacement. Conjugating the
flip by `f tensor 1` proves the same bound for the actual map
`x tensor y ↦ f(y) tensor f⁻¹(x)`. Thus a twisted swap needs no group cocycle
trivialization. The last theorem applies this calculation to the literal
scalar-extended natural G₂ carrier used by `pairRep`.

Identifying arbitrary outer normalizers with these operators remains a separate
model obligation. This module does not assert that identification.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
open Representation.BinaryOffender.NaturalTensor

namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
section LinearAlgebra
variable {K U : Type*} [Field K] [AddCommGroup U] [Module K U]
  [FiniteDimensional K U]

theorem flip_displacement (hd : Module.finrank K U = 6) :
    15 ≤ operatorFixedCodim (TensorProduct.comm K U U).toLinearMap := by
  let e : U ≃ₗ[K] (Fin 6 → K) := LinearEquiv.ofFinrankEq _ _ (by simp [hd])
  let C := (TensorProduct.congr e e).trans
    (TensorProduct.piScalarRight K K (Fin 6 → K) (Fin 6))
  let S := (TensorProduct.comm K U U).toLinearMap
  have hC (v : U ⊗[K] U) : ∀ i j, C (S v) i j = C v j i := by
    induction v using TensorProduct.induction_on with
    | zero => intro i j; simp
    | tmul x y => intro i j; simp [C, S, mul_comm]
    | add x y hx hy => intro i j; simp only [map_add, Pi.add_apply, hx, hy]
  let T := C.conj S
  have hT (x : Fin 6 → Fin 6 → K) (i j : Fin 6) : T x i j = x j i := by
    simpa only [T, LinearEquiv.conj_apply_apply, C.apply_symm_apply] using hC (C.symm x) i j
  have hb := Triality.OuterDisplacement.transpose_displacement_ge 6 T (LinearMap.id)
    (fun x i j => hT x i j)
  have he := operatorFixedCodim_eq_of_equiv S T C (by intro v; simp [T])
  rw [he]
  change Nat.choose 6 2 * Module.finrank K K ≤ operatorFixedCodim T at hb
  simpa only [show Nat.choose 6 2 = 15 from rfl, Module.finrank_self, mul_one] using hb

theorem twisted_swap_displacement (hd : Module.finrank K U = 6)
    (f : U ≃ₗ[K] U) (T : Module.End K (U ⊗[K] U))
    (hT : ∀ x y, T (x ⊗ₜ[K] y) = f y ⊗ₜ[K] f.symm x) :
    15 ≤ operatorFixedCodim T := by
  let C := TensorProduct.congr f (LinearEquiv.refl K U)
  let S := (TensorProduct.comm K U U).toLinearMap
  have hc (v : U ⊗[K] U) : C (S v) = T (C v) := by
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [C, S, hT]
    | add x y hx hy => simp only [map_add, hx, hy]
  have he := operatorFixedCodim_eq_of_equiv S T C hc
  rw [← he]
  exact flip_displacement hd
end LinearAlgebra

section Pair
variable (F K : Type*) [Field F] [CharP F 2] [Field K] [Algebra F K]

/-- The twisted-swap estimate on the actual pair of scalar-extended natural factors. -/
theorem pair_twisted_swap_displacement
    (f : NaturalScalarSpace F K ≃ₗ[K] NaturalScalarSpace F K)
    (T : Module.End K (PairSpace F K))
    (hT : ∀ x y, T (x ⊗ₜ[K] y) = f y ⊗ₜ[K] f.symm x) :
    15 ≤ operatorFixedCodim (k := K) (V := PairSpace F K) T := by
  apply twisted_swap_displacement (U := NaturalScalarSpace F K) _ f T hT
  rw [Module.finrank_baseChange, Atlas.G2.Natural.finrank_space]

end Pair
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
