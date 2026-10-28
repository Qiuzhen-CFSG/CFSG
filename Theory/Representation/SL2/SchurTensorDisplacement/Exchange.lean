module

public import Theory.Representation.TensorInterchange
public import Theory.Representation.TensorInvolutionIntertwiners
public import Theory.Representation.CommonFixedSpaceTransport

/-!
# Involutions exchanging a pair of representation factors

For the literal pair `τ ⊗ (τ ∘ δ)`, where `δ² = 1`, an operator inducing
inner times `δ` differs by a scalar from an inner action followed by exchange.
Schur's lemma supplies the scalar; the square-one equation in characteristic
two absorbs it and identifies the second exchange map with the first inverse.
Conjugating on one factor reduces to interchange, whose displacement has
rank `d.choose 2`. In particular it moves at least a quarter when `d ≥ 2`.

The scalar-descent and Chapter K outer SL₂ consumers use the actual actor
and its intertwining equation, without assuming an involution conjugacy.
Source: Guralnick--Malle, Classification of 2F-modules II, §3.5 and
Proposition 4.1(2), manuscript pp.20,22.
-/

public section

open scoped TensorProduct
open Module
namespace Representation.SL2.SchurTensorDisplacement
noncomputable section
variable {F H : Type*} [Field F] [CharP F 2] [Group H]

private def actionEquiv {U : Type*} [AddCommGroup U] [Module F U]
    (τ : Representation F H U) (c : H) : U ≃ₗ[F] U where
  toFun := τ c
  invFun := τ c⁻¹
  left_inv v := by
    change (τ c⁻¹ * τ c) v = v
    rw [← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change (τ c * τ c⁻¹) v = v
    rw [← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  map_add' := (τ c).map_add
  map_smul' := (τ c).map_smul

omit [CharP F 2] in
private theorem normalized_exchange_rank {d : ℕ}
    (f : (Fin d → F) ≃ₗ[F] (Fin d → F))
    (T : Module.End F (TensorInterchange.Space F d))
    (hT : ∀ u v, T (u ⊗ₜ[F] v) = f v ⊗ₜ[F] f.symm u) :
    finrank F (T - 1).range = d.choose 2 := by
  let e := TensorProduct.congr f.symm (LinearEquiv.refl F (Fin d → F))
  have he : ∀ z, e (T z) = TensorInterchange.flip F d (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => simp [e, hT, TensorInterchange.flip]
    | add z w hz hw => simp [hz, hw]
  exact (LinearMap.FixedSpaceTransport.finrank_range_sub_one_equiv e T
    (TensorInterchange.flip F d) he).trans (TensorInterchange.finrank_range_flip F d)

/-- An involution inducing inner times the automorphism that exchanges two
Frobenius-paired factors has the exact displacement of tensor interchange. -/
theorem paired_involution_rank [IsAlgClosed F] {d : ℕ}
    (τ : Representation F H (Fin d → F)) (δ : MulAut H) (hδ : δ ^ 2 = 1)
    [IsIrreducible (τ.tprod (τ.comp δ.toMonoidHom))]
    (c : H) (T : Module.End F (TensorInterchange.Space F d))
    (h2 : T * T = 1)
    (hT : ∀ a, T * (τ.tprod (τ.comp δ.toMonoidHom)) a =
      (τ.tprod (τ.comp δ.toMonoidHom)) (c * δ a * c⁻¹) * T) :
    finrank F (T - 1).range = d.choose 2 := by
  let π := τ.tprod (τ.comp δ.toMonoidHom)
  let f := actionEquiv τ c
  let g := actionEquiv τ (δ c)
  let S : TensorInterchange.Space F d ≃ₗ[F] TensorInterchange.Space F d :=
    (_root_.TensorProduct.comm F _ _).trans (TensorProduct.congr f g)
  have hδδ (a : H) : δ (δ a) = a := by
    have hh := DFunLike.congr_fun hδ a
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using hh
  have hmove (a b : H) (v : Fin d → F) :
      τ a (τ b v) = τ (a * b * a⁻¹) (τ a v) := by
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hS : ∀ a, S.toLinearMap * π a = π ((MulAut.conj c * δ) a) * S.toLinearMap := by
    intro a
    apply TensorProduct.ext'
    intro u v
    change τ c (τ (δ a) v) ⊗ₜ[F] τ (δ c) (τ a u) =
      τ (c * δ a * c⁻¹) (τ c v) ⊗ₜ[F] τ (δ (c * δ a * c⁻¹)) (τ (δ c) u)
    simp only [map_mul δ, map_inv δ, hδδ]
    exact congrArg₂ (fun u v => u ⊗ₜ[F] v) (hmove c (δ a) v) (hmove (δ c) a u)
  obtain ⟨b, hb⟩ := TensorInvolutionIntertwiners.same_automorphism_scalar π
    (MulAut.conj c * δ) T S hT hS
  have hform : ∀ u v, T (u ⊗ₜ[F] v) = b • (f v ⊗ₜ[F] g u) := by
    intro u v
    rw [hb]
    rfl
  exact normalized_exchange_rank f T
    (TensorInvolutionIntertwiners.normalize_exchange f g b T h2 hform)

/-- For nontrivial factors, paired outer involutions move at least a quarter
of the tensor square, with equality for factors of dimension two. -/
theorem paired_involution_bound [IsAlgClosed F] {d : ℕ} (hd : 2 ≤ d)
    (τ : Representation F H (Fin d → F)) (δ : MulAut H) (hδ : δ ^ 2 = 1)
    [IsIrreducible (τ.tprod (τ.comp δ.toMonoidHom))]
    (c : H) (T : Module.End F (TensorInterchange.Space F d))
    (h2 : T * T = 1)
    (hT : ∀ a, T * (τ.tprod (τ.comp δ.toMonoidHom)) a =
      (τ.tprod (τ.comp δ.toMonoidHom)) (c * δ a * c⁻¹) * T) :
    finrank F (TensorInterchange.Space F d) ≤ 4 * finrank F (T - 1).range := by
  rw [paired_involution_rank τ δ hδ c T h2 hT, TensorInterchange.finrank_space]
  have hchoose : ∀ n : ℕ, 2 * n.choose 2 + n = n * n := by
    intro n
    induction n with
    | zero => simp
    | succ d ih => rw [Nat.choose_succ_succ, Nat.choose_one_right]; nlinarith
  have hc := hchoose d
  nlinarith
end
end Representation.SL2.SchurTensorDisplacement
