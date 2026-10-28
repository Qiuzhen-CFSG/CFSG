module
public import Theory.Representation.TensorInvolutionIntertwiners
public import Theory.Representation.Triality.OuterDisplacement.TensorCoordinates
/-!
# Schur rigidity for an actual paired tensor component

An irreducible component represented in coordinates `U tensor U` acts as a
half representation tensor its twist by an involutive group automorphism.
The transported tensor interchange induces that same automorphism. The
existing Schur comparison makes the actual square-one actor a scalar multiple
of interchange; characteristic two forces this scalar to be one.

Finite dimensionality is assumed on the actual half module and transported
to the component through the supplied equivalence. Tensor-product basis
coordinates then identify the very same actor with transpose, with a
one-dimensional remaining coordinate. The final applications retain the
original operator under algebraic-closure base change and construct
`HasPairedTensorCoordinates`, hence its seven-sixteenths displacement bound.
No swap formula or paired-coordinate certificate is an input.

Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Lemma 8.6, internal pp.20,56--57; the scalar comparison is Schur's lemma.
-/

public section
open Representation
open scoped TensorProduct
noncomputable section
namespace Triality.OuterDisplacement.ConcretePairedTensorSource

section Schur
variable {k N W U : Type*} [Field k] [IsAlgClosed k] [CharP k 2]
  [Group N] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
  [FiniteDimensional k U]

/-- Component intertwining identifies the actual square-one operator with tensor interchange. -/
theorem paired_operator_eq_comm
    (σ : Representation k N W) [IsIrreducible σ]
    (a : N ≃* N) (ha : Function.Involutive a) (π : Representation k N U)
    (e : W ≃ₗ[k] (U ⊗[k] U))
    (he : ∀ g v, e (σ g v) = TensorProduct.map (π g) (π (a g)) (e v))
    (T : Module.End k W) (hT2 : T * T = 1)
    (hTi : ∀ g v, T (σ g v) = σ (a g) (T v)) (v : W) :
    e (T v) = TensorProduct.comm k U U (e v) := by
  let : FiniteDimensional k W := e.symm.finiteDimensional
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let S : W ≃ₗ[k] W := (e.trans (TensorProduct.comm k U U)).trans e.symm
  have hS (w : W) : e (S w) = TensorProduct.comm k U U (e w) := by
    simp only [S, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hS2 : S.toLinearMap * S.toLinearMap = 1 := by
    apply LinearMap.ext
    intro w
    apply e.injective
    change e (S (S w)) = e w
    rw [hS, hS]
    simp
  have hSi (g : N) : S.toLinearMap * σ g = σ (a g) * S.toLinearMap := by
    apply LinearMap.ext
    intro w
    apply e.injective
    change e (S (σ g w)) = e (σ (a g) (S w))
    rw [hS, he, he, ha, hS]
    exact (TensorProduct.map_comm _ _ _).symm
  have hTS := TensorInvolutionIntertwiners.same_automorphism_involutions_eq σ a T S
    (fun g => LinearMap.ext (hTi g)) hSi hT2 hS2
  rw [hTS]
  exact hS v

/-- The same rigidity statement for a literal involutive linear equivalence. -/
theorem paired_equiv_eq_comm
    (σ : Representation k N W) [IsIrreducible σ]
    (a : N ≃* N) (ha : Function.Involutive a) (π : Representation k N U)
    (e : W ≃ₗ[k] (U ⊗[k] U))
    (he : ∀ g v, e (σ g v) = TensorProduct.map (π g) (π (a g)) (e v))
    (T : W ≃ₗ[k] W) (hT2 : Function.Involutive T)
    (hTi : ∀ g v, T (σ g v) = σ (a g) (T v)) (v : W) :
    e (T v) = TensorProduct.comm k U U (e v) :=
  paired_operator_eq_comm σ a ha π e he T.toLinearMap
    (LinearMap.ext hT2) hTi v

end Schur

section Coordinates
variable {k U : Type*} [Field k] [AddCommGroup U] [Module k U]

/-- Tensor-product basis coordinates, curried with a singleton remaining index. -/
@[expose] def tensorBasisCoordinates {d : ℕ} (b : Module.Basis (Fin d) k U) :
    (U ⊗[k] U) ≃ₗ[k] (Fin d → Fin d → Fin 1 → k) where
  toFun z i j _ := (b.tensorProduct b).equivFun z (i, j)
  invFun f := (b.tensorProduct b).equivFun.symm (fun p => f p.1 p.2 0)
  left_inv z := (b.tensorProduct b).equivFun.symm_apply_apply z
  right_inv f := by
    funext i j l
    change (b.tensorProduct b).equivFun ((b.tensorProduct b).equivFun.symm _) (i, j) = f i j l
    rw [LinearEquiv.apply_symm_apply]
    exact congrArg (f i j) (Subsingleton.elim _ _)
  map_add' z w := by
    funext i j l
    change (b.tensorProduct b).equivFun (z + w) (i, j) = _
    rw [map_add]
    rfl
  map_smul' a z := by
    funext i j l
    change (b.tensorProduct b).equivFun (a • z) (i, j) = _
    rw [map_smul]
    rfl

/-- Pure tensor coordinates are the products of the two basis coordinates. -/
theorem tensorBasisCoordinates_tmul {d : ℕ} (b : Module.Basis (Fin d) k U)
    (v w : U) (i j : Fin d) (l : Fin 1) :
    tensorBasisCoordinates b (v ⊗ₜ[k] w) i j l = b.repr v i * b.repr w j := by
  change (b.tensorProduct b).equivFun (v ⊗ₜ[k] w) (i, j) = _
  simp only [Module.Basis.equivFun_apply, Module.Basis.tensorProduct_repr_tmul_apply,
    smul_eq_mul, mul_comm]

/-- Tensor interchange is transpose in these coordinates. -/
theorem tensorBasisCoordinates_comm {d : ℕ} (b : Module.Basis (Fin d) k U)
    (z : U ⊗[k] U) (i j : Fin d) :
    tensorBasisCoordinates b (TensorProduct.comm k U U z) i j =
      tensorBasisCoordinates b z j i := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v w =>
    funext l
    simp only [TensorProduct.comm_tmul, tensorBasisCoordinates_tmul, mul_comm]
  | add z w hz hw =>
    simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hz hw

/-- Coordinates obtained from the given tensor equivalence and the half-module basis. -/
@[expose] def pairedCoordinates {W : Type*} [AddCommGroup W] [Module k W]
    [FiniteDimensional k U] (e : W ≃ₗ[k] (U ⊗[k] U)) :
    W ≃ₗ[k] (Fin (Module.finrank k U) → Fin (Module.finrank k U) → Fin 1 → k) :=
  e.trans (tensorBasisCoordinates (Module.finBasis k U))

end Coordinates

section Assembled
variable {k N W U : Type*} [Field k] [IsAlgClosed k] [CharP k 2]
  [Group N] [AddCommGroup W] [Module k W] [AddCommGroup U] [Module k U]
  [FiniteDimensional k U]

/-- The coordinates built from the supplied equivalence transpose the actual operator. -/
theorem pairedCoordinates_action
    (σ : Representation k N W) [IsIrreducible σ]
    (a : N ≃* N) (ha : Function.Involutive a) (π : Representation k N U)
    (e : W ≃ₗ[k] (U ⊗[k] U))
    (he : ∀ g v, e (σ g v) = TensorProduct.map (π g) (π (a g)) (e v))
    (T : Module.End k W) (hT2 : T * T = 1)
    (hTi : ∀ g v, T (σ g v) = σ (a g) (T v)) (v : W) (i j : Fin (Module.finrank k U)) :
    pairedCoordinates e (T v) i j = pairedCoordinates e v j i := by
  change tensorBasisCoordinates (Module.finBasis k U) (e (T v)) i j =
    tensorBasisCoordinates (Module.finBasis k U) (e v) j i
  rw [paired_operator_eq_comm σ a ha π e he T hT2 hTi]
  exact tensorBasisCoordinates_comm (Module.finBasis k U) (e v) i j

/-- A paired irreducible component admits transpose coordinates with remaining rank one. -/
theorem exists_transpose_coordinates
    (σ : Representation k N W) [IsIrreducible σ]
    (a : N ≃* N) (ha : Function.Involutive a) (π : Representation k N U)
    (e : W ≃ₗ[k] (U ⊗[k] U))
    (he : ∀ g v, e (σ g v) = TensorProduct.map (π g) (π (a g)) (e v))
    (T : Module.End k W) (hT2 : T * T = 1)
    (hTi : ∀ g v, T (σ g v) = σ (a g) (T v)) :
    ∃ c : W ≃ₗ[k] (Fin (Module.finrank k U) → Fin (Module.finrank k U) → Fin 1 → k),
      ∀ v i j, c (T v) i j = c v j i :=
  ⟨pairedCoordinates e, pairedCoordinates_action σ a ha π e he T hT2 hTi⟩

end Assembled

section BaseChange
variable {E N W U : Type*} [Field E] [CharP E 2] [Group N]
  [AddCommGroup W] [Module E W] [FiniteDimensional E W]
  [AddCommGroup U] [Module (AlgebraicClosure E) U] [FiniteDimensional (AlgebraicClosure E) U]

omit [FiniteDimensional E W] in
/-- Actual component data construct the literal algebraic-closure displacement coordinates. -/
theorem hasPairedTensorCoordinates_of_component_intertwiner
    (T : Module.End E W) (hT2 : T * T = 1)
    (σ : Representation (AlgebraicClosure E) N (AlgebraicClosure E ⊗[E] W))
    [IsIrreducible σ] (a : N ≃* N) (ha : Function.Involutive a)
    (π : Representation (AlgebraicClosure E) N U)
    (e : (AlgebraicClosure E ⊗[E] W) ≃ₗ[AlgebraicClosure E]
      (U ⊗[AlgebraicClosure E] U))
    (he : ∀ g v, e (σ g v) = TensorProduct.map (π g) (π (a g)) (e v))
    (hTi : ∀ g v, T.baseChange (AlgebraicClosure E) (σ g v) =
      σ (a g) (T.baseChange (AlgebraicClosure E) v))
    (hd : 8 ≤ Module.finrank (AlgebraicClosure E) U) : HasPairedTensorCoordinates T := by
  have h2 : T.baseChange (AlgebraicClosure E) * T.baseChange (AlgebraicClosure E) = 1 := by
    rw [← LinearMap.baseChange_mul, hT2, LinearMap.baseChange_one]
  obtain ⟨c, hc⟩ := exists_transpose_coordinates σ a ha π e he
    (T.baseChange (AlgebraicClosure E)) h2 hTi
  exact ⟨Module.finrank (AlgebraicClosure E) U, 1, hd, c, 1, hc⟩

/-- The resulting paired-tensor bound applies to the original operator over its original field. -/
theorem displacement_ratio_of_component_intertwiner
    (T : Module.End E W) (hT2 : T * T = 1)
    (σ : Representation (AlgebraicClosure E) N (AlgebraicClosure E ⊗[E] W))
    [IsIrreducible σ] (a : N ≃* N) (ha : Function.Involutive a)
    (π : Representation (AlgebraicClosure E) N U)
    (e : (AlgebraicClosure E ⊗[E] W) ≃ₗ[AlgebraicClosure E]
      (U ⊗[AlgebraicClosure E] U))
    (he : ∀ g v, e (σ g v) = TensorProduct.map (π g) (π (a g)) (e v))
    (hTi : ∀ g v, T.baseChange (AlgebraicClosure E) (σ g v) =
      σ (a g) (T.baseChange (AlgebraicClosure E) v))
    (hd : 8 ≤ Module.finrank (AlgebraicClosure E) U) :
    7 * Module.finrank E W ≤ 16 * Module.finrank E (LinearMap.range (T - LinearMap.id)) :=
  displacement_ratio_of_pairedTensorCoordinates T
    (hasPairedTensorCoordinates_of_component_intertwiner T hT2 σ a ha π e he hTi hd)

end BaseChange
end Triality.OuterDisplacement.ConcretePairedTensorSource
