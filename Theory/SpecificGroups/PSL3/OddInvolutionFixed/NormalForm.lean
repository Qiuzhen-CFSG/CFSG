module

public import Theory.SpecificGroups.PSL3.OuterSolvable.OddPrimeCoverage
public import Theory.SpecificGroups.PSL3.CartanActions.NormalizerForm
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Odd-prime PSL₃ automorphisms and linear involutions

The checked standard-automorphism coverage gives a linear-times-graph normal
form over a prime field. A scalar determinant correction makes the cube of
every linear actor inner, so every involution in the linear image is inner.
The formulas retain the canonical quotient by the scalar center.

This extends the matrix calculations in `PSL3.SevenAction.NormalForm` and
`PSL3.SevenAction.Inner` from the seven-element field to arbitrary fields.
Source: GLS3, Theorem 2.5.12(a) and §2.7, and the inspection in
Aschbacher–Smith E.6.18, printed p.252 (PDF p.263).
-/

public section
open scoped MatrixGroups
open Subgroup Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.OddInvolutionFixed
variable {F : Type*} [Field F]

@[expose] def inverseTransposeGL : GL (Fin 3) F →* GL (Fin 3) F where
  toFun g := {
    val := g.inv.transpose
    inv := g.val.transpose
    val_inv := by rw [← Matrix.transpose_mul, g.val_inv, Matrix.transpose_one]
    inv_val := by rw [← Matrix.transpose_mul, g.inv_val, Matrix.transpose_one] }
  map_one' := Units.ext Matrix.transpose_one
  map_mul' g h := Units.ext (Matrix.transpose_mul h.inv g.inv)

/-- Inverse transpose agrees with its formula on the invertible matrix group. -/
theorem graphSL_toGL (x : SL(3,F)) :
    SpecialLinearGroup.toGL (graphSL F x) = inverseTransposeGL (SpecialLinearGroup.toGL x) := by
  apply Units.ext
  exact (Matrix.adjugate_transpose x.val).symm

theorem graph_linearConj (g : GL (Fin 3) F) :
    graph F * linearConj F g = linearConj F (inverseTransposeGL g) * graph F := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) y
  change QuotientGroup.mk (graphSL F (linearConjSL F g x)) =
    QuotientGroup.mk (linearConjSL F (inverseTransposeGL g) (graphSL F x))
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [graphSL_toGL, linearConjSL_toGL, map_mul, map_mul, map_inv,
    linearConjSL_toGL, graphSL_toGL]

theorem automorphism_normal_form [Finite F] [IsSimpleGroup PSL(3,F)]
    (hns : ¬ Group.IsSolvable PSL(3,F)) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p) (a : MulAut PSL(3,F)) :
    ∃ g : GL (Fin 3) F, a = linearConj F g ∨ a = linearConj F g * graph F := by
  have hfield (σ : F ≃+* F) : σ = 1 := FiniteField.ringAut_eq_one_of_card_prime hp hF σ
  have hc := standard_eq_top_of_odd_prime_card F hns hp ho hF
  obtain ⟨g, σ, ha⟩ := CartanActions.NormalizerForm.standard_factorization F
    (by intro σ m; rw [hfield σ, map_one, one_mul, mul_one]; rfl)
    (fun g => ⟨inverseTransposeGL g, graph_linearConj g⟩)
    (by intro σ; rw [hfield σ, map_one]; exact Commute.one_left _)
    a (hc ▸ mem_top a)
  exact ⟨g, by simpa only [hfield σ, map_one, mul_one] using ha⟩

theorem linearConj_scalar (u : Fˣ) :
    linearConj F (GeneralLinearGroup.scalar (Fin 3) u) = 1 := by
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center SL(3,F)) y
  change QuotientGroup.mk (linearConjSL F (GeneralLinearGroup.scalar (Fin 3) u) x) =
    QuotientGroup.mk x
  congr 1
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL, GeneralLinearGroup.scalar_commute, mul_inv_cancel_right]

theorem linearConj_cube_inner (g : GL (Fin 3) F) :
    linearConj F g ^ 3 ∈ MulAut.innerSubgroup PSL(3,F) := by
  let m := GeneralLinearGroup.scalar (Fin 3) (GeneralLinearGroup.det g)⁻¹ * g ^ 3
  have hm : GeneralLinearGroup.det m = 1 := by
    simp only [m, map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow,
      inv_pow, inv_mul_cancel]
  let x := (slEquivDetKernel F).symm ⟨m, hm⟩
  refine ⟨QuotientGroup.mk' (center SL(3,F)) x, ?_⟩
  calc
    MulAut.conj (QuotientGroup.mk' (center SL(3,F)) x) =
        linearConj F (SpecialLinearGroup.toGL x) := (linearConj_toGL F x).symm
    _ = linearConj F m := by rw [slEquivDetKernel_symm_toGL]
    _ = _ := by
      dsimp only [m]
      rw [map_mul, linearConj_scalar, one_mul, map_pow]

theorem linearConj_involution_inner (g : GL (Fin 3) F)
    (hg : linearConj F g ^ 2 = 1) :
    linearConj F g ∈ MulAut.innerSubgroup PSL(3,F) := by
  simpa only [pow_succ, hg, one_mul] using linearConj_cube_inner g

end Matrix.PSL3.OddInvolutionFixed
