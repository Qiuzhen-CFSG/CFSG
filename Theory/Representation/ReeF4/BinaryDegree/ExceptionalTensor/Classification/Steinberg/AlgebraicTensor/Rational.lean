module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Parameters


/-!
# Rationality of exceptional tensor products

An algebraic endomorphism of the literal closed F₄ carrier gives a rational
action on the exact `pointTensor` space. Iterate the algebraic morphism, pull
back each rational factor, and apply the rational tensor construction at every
stage of `tensorPrefix`. Equality of the point actions identifies the result
with the existing tensor, including its initial one-dimensional unit factor.

No root formula, surjectivity, characteristic, or highest-weight condition is
needed for rationality. Irreducibility and the highest weight of this action
remain separate obligations in the exceptional tensor-product theorem.

Sources: GLS3, Definition 2.8.3 and Theorem 2.8.5; Steinberg,
*Representations of Algebraic Groups*, Nagoya Math. J. 22 (1963), §5.
-/

public section

open Theory.AlgebraicGroup
open scoped TensorProduct
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
universe u v
variable {F : Type u} [Field F] [IsAlgClosed F]

private def actionOf {G : Variety F} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module F V]
    (ρ : Representation F (Variety.Point G) V) : RationalRepresentation G V :=
  ⟨ρ.asGroupHom⟩

omit [IsAlgClosed F] in
private theorem actionOf_apply {G : Variety F} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module F V]
    (ρ : Representation F (Variety.Point G) V) (g : Variety.Point G) :
    ((actionOf ρ).action g).val = ρ g := Representation.asGroupHom_apply ρ g

omit [IsAlgClosed F] in
private theorem action_ext {G : Variety F} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module F V]
    (ρ σ : RationalRepresentation G V)
    (h : ∀ g, (ρ.action g).val = (σ.action g).val) : ρ = σ := by
  cases ρ with
  | mk ρ =>
    cases σ with
    | mk σ =>
      congr 1
      ext g v
      exact LinearMap.congr_fun (h g) v

set_option backward.isDefEq.respectTransparency false in
private theorem trivial_rational {G : Variety F} [AlgebraicGroup G] :
    IsRationalRepresentation (actionOf (Representation.trivial F (Variety.Point G) F)) := by
  let b := Module.finBasis F F
  let f : Theory.AlgebraicGroup.Morphism G (glVarietyOf F F) :=
    { toVariety := Variety.Morphism.const _ _ 1
      map_one := rfl
      map_mul := by intro x y; exact (one_mul 1).symm }
  refine ⟨b, f, ?_⟩
  intro g
  change glPointEquivOf F F b 1 = _
  have h1 := glPointEquivOf_generalLinearRepresentationPoint b
    (1 : LinearMap.GeneralLinearGroup F F)
  rw [generalLinearRepresentationPoint_one] at h1
  rw [h1]
  apply Units.ext
  rw [actionOf_apply]
  rfl

private theorem tensor_rational {G : Variety F} [AlgebraicGroup G]
    {V W : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (ρ : Representation F (Variety.Point G) V)
    (σ : Representation F (Variety.Point G) W)
    (hρ : IsRationalRepresentation (actionOf ρ))
    (hσ : IsRationalRepresentation (actionOf σ)) :
    IsRationalRepresentation (actionOf (ρ.tprod σ)) := by
  obtain ⟨τ, hτ, hr⟩ := rationalRepresentation_tensorProduct_exists
    (actionOf ρ) (actionOf σ) hρ hσ
  have he : τ = actionOf (ρ.tprod σ) := by
    apply action_ext
    intro g
    apply TensorProduct.ext
    ext v w
    exact hτ g v w
  exact he ▸ hr

private def morphismPow {G : Variety F} [AlgebraicGroup G]
    (Ψ : Theory.AlgebraicGroup.Morphism G G) : ℕ → Theory.AlgebraicGroup.Morphism G G
  | 0 => .id G
  | n + 1 => Ψ.comp (morphismPow Ψ n)

omit [IsAlgClosed F] in
private theorem morphismPow_onPoints {G : Variety F} [AlgebraicGroup G]
    (Ψ : Theory.AlgebraicGroup.Morphism G G) (ψ : Monoid.End (Variety.Point G))
    (hψ : Ψ.onPoints = ψ) (n : ℕ) :
    (morphismPow Ψ n).onPoints = ψ ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change Ψ.onPoints.comp (morphismPow Ψ n).onPoints = _
    rw [ih, hψ]
    rfl

private theorem restrict_rational (B : AlgebraicFactor F)
    (Ψ : Theory.AlgebraicGroup.Morphism (F4Chevalley.Carrier (k := F))
      (F4Chevalley.Carrier (k := F))) (ψ : Monoid.End (PointGroup F))
    (hψ : Ψ.onPoints = ψ) (n : ℕ) :
    IsRationalRepresentation (actionOf (B.restrict (ψ ^ n)).ρ) := by
  obtain ⟨τ, hτ, hr⟩ := rationalRepresentation_pullback_exists
    (morphismPow Ψ n) B.action B.irreducible.1
  have he : τ = actionOf (B.restrict (ψ ^ n)).ρ := by
    apply action_ext
    intro g
    rw [hτ, morphismPow_onPoints Ψ ψ hψ]
    rfl
  exact he ▸ hr

/-- The canonical algebraic action on the exact finite tensor space. -/
noncomputable def pointTensorAction {k : ℕ} (ψ : Monoid.End (PointGroup F))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) :
    RationalRepresentation (F4Chevalley.Carrier (k := F)) (pointTensor ψ B) :=
  actionOf (pointTensor ψ B).ρ

theorem pointTensorAction_apply {k : ℕ} (ψ : Monoid.End (PointGroup F))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) (g : PointGroup F) :
    ((pointTensorAction ψ B).action g).val = (pointTensor ψ B).ρ g :=
  actionOf_apply _ _

/-- Rationality of the actual tensor, without any irreducibility premise. -/
theorem pointTensorAction_rational {k : ℕ}
    (Ψ : Theory.AlgebraicGroup.Morphism (F4Chevalley.Carrier (k := F))
      (F4Chevalley.Carrier (k := F)))
    (B : ZMod (2 * k + 1) → AlgebraicFactor F) :
    IsRationalRepresentation (pointTensorAction Ψ.onPoints B) := by
  let ψ : Monoid.End (PointGroup F) := Ψ.onPoints
  let V : ℕ → FDRep F (PointGroup F) := fun i =>
    (B (i : ZMod (2 * k + 1))).restrict (ψ ^ (i : ZMod (2 * k + 1)).val)
  have hV (i : ℕ) : IsRationalRepresentation (actionOf (V i).ρ) :=
    restrict_rational _ Ψ ψ rfl _
  have hprefix : ∀ n, IsRationalRepresentation (actionOf (tensorPrefix V n).ρ) := by
    intro n
    induction n with
    | zero => exact trivial_rational
    | succ n ih => exact tensor_rational _ _ ih (hV n)
  exact hprefix (2 * k + 1)

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
