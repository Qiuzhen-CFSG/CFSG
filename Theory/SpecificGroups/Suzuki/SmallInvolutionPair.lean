module

public import Theory.SpecificGroups.Suzuki.SplitNormalizerGeometry

/-!
# Two involutions in the actual degenerate Suzuki group

The root element with coordinates (0,1) and the Weyl matrix are involutions,
and their product has order five. This is the concrete calculation already
used privately in BenderSuzuki/MatrixGroups/SuzukiZero.lean, made available
in an extension without changing that shared module. It uses the actual
GF(2) matrices, with no replacement by an abstract group of order twenty.

Injective maps preserve the pair and its product order. In a direct product
both witnesses have first coordinate one, so a source application needs
fusion only on the Suzuki factor.

Source: the matrix convention of Huppert–Blackburn III, XI.3.1–3;
Aschbacher–Smith, J.2.9, printed p.438 (PDF p.449), refs/quasithin.pdf.
-/

@[expose] public section
namespace BenderSuzuki.MatrixGroups
open PFAppendixIII

/-- The central root involution with coordinates (0,1). -/
noncomputable def suzukiZeroInvolution : SuzukiMatrixGroup 0 :=
  ⟨SuzukiRootGL 0 0 1, Subgroup.subset_closure (Or.inl ⟨0, 1, rfl⟩)⟩

/-- The specified matrix is an involution. -/
theorem suzukiZeroInvolution_order : orderOf suzukiZeroInvolution = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [suzukiZeroInvolution, SuzukiRootGL, SuzukiRootMatrix,
        Matrix.mul_apply, Fin.sum_univ_four, pow_two, CharTwo.add_self_eq_zero]
  · intro h
    have he := congrArg (fun x : SuzukiMatrixGroup 0 => x.val (0 : Fin 4) (2 : Fin 4)) h
    simp [suzukiZeroInvolution, SuzukiRootGL, SuzukiRootMatrix] at he

set_option maxHeartbeats 1200000 in
/-- The product of the two specified involutions has order five. -/
theorem suzukiZeroInvolution_mul_weyl_order :
    orderOf (suzukiZeroInvolution * suzukiWeyl 0) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (SuzukiRootGL 0 0 1 * SuzukiWeylGL 0) ^ 5 =
      (1 : GL (Fin 4) (BinaryGaloisField 1))
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SuzukiRootGL, SuzukiRootMatrix, SuzukiWeylGL,
        SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four, pow_succ,
        CharTwo.add_self_eq_zero]
  · intro h
    have he := congrArg (fun x : SuzukiMatrixGroup 0 => x.val (0 : Fin 4) (3 : Fin 4)) h
    simp [suzukiZeroInvolution, suzukiWeyl, SuzukiRootGL, SuzukiRootMatrix,
      SuzukiWeylGL, SuzukiWeylMatrix, Matrix.mul_apply, Fin.sum_univ_four] at he

/-- Embed the matrix pair in the second factor of an actual direct product. -/
theorem suzukiZero_pair_in_product {A : Type*} [Group A] :
    ∃ u v : A × SuzukiMatrixGroup 0,
      u.1 = 1 ∧ v.1 = 1 ∧ orderOf u = 2 ∧ orderOf v = 2 ∧ orderOf (u * v) = 5 := by
  let f : SuzukiMatrixGroup 0 →* A × SuzukiMatrixGroup 0 := MonoidHom.inr _ _
  have hf : Function.Injective f := fun x y h => congrArg Prod.snd h
  refine ⟨f suzukiZeroInvolution, f (suzukiWeyl 0), rfl, rfl, ?_, ?_, ?_⟩
  · rw [orderOf_injective f hf, suzukiZeroInvolution_order]
  · rw [orderOf_injective f hf, suzukiWeyl_orderOf]
  · rw [← map_mul, orderOf_injective f hf, suzukiZeroInvolution_mul_weyl_order]

/-- An injective group map retains both involution orders and the product order. -/
theorem suzukiZero_pair_of_product_embedding {A H : Type*} [Group A] [Group H]
    (f : A × SuzukiMatrixGroup 0 →* H) (hf : Function.Injective f) :
    ∃ u v : H, orderOf u = 2 ∧ orderOf v = 2 ∧ orderOf (u * v) = 5 := by
  obtain ⟨u, v, _, _, hu, hv, huv⟩ := suzukiZero_pair_in_product (A := A)
  exact ⟨f u, f v, (orderOf_injective f hf u).trans hu,
    (orderOf_injective f hf v).trans hv,
    by rw [← map_mul, orderOf_injective f hf, huv]⟩

end BenderSuzuki.MatrixGroups
