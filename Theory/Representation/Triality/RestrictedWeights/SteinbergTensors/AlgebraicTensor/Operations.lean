module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.Construction

/-!
# Regularity of the specified D4 tensor actions

This compatibility layer connects the exact point actions in `Construction`
to the generic rational-representation operations. Polynomial morphisms compose
under pullback, and regular matrix coefficients multiply under tensor product.
This proves rationality of every `rationalTensor`, including the empty tensor.
The one-factor intertwiner also proves irreducibility at length one.

Source: GLS3, Definition 2.8.3 and the proof of Corollary 2.8.6(a),
`refs/KGroup/GLS3/chapter2.tex`. Longer tensor irreducibility is a separate
representation-theoretic obligation.
-/

@[expose] public noncomputable section

open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v w
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

/-- The algebraic-action package for a representation of the point group. -/
def algebraicAction {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : Representation k (Variety.Point K) V) : RationalRepresentation K V :=
  ⟨Representation.asGroupHom ρ⟩

omit [IsAlgClosed k] in
@[simp] theorem algebraicAction_apply {V : Type v} [AddCommGroup V] [Module k V]
    (ρ : Representation k (Variety.Point K) V) (g : Variety.Point K) :
    ((algebraicAction ρ).action g : Module.End k V) = ρ g :=
  Representation.asGroupHom_apply ρ g

omit [IsAlgClosed k] in
/-- Equality of point operators determines the algebraic-action package. -/
theorem action_ext {V : Type v} [AddCommGroup V] [Module k V]
    (ρ σ : RationalRepresentation K V)
    (h : ∀ g, (ρ.action g : Module.End k V) = (σ.action g : Module.End k V)) : ρ = σ := by
  cases ρ with | mk ρ =>
    cases σ with | mk σ =>
      congr 1
      apply MonoidHom.ext
      intro g
      exact Units.ext (h g)

/-- A specified point action inherits rationality from any equal rational action. -/
theorem rational_of_action_eq {V : Type v} [AddCommGroup V] [Module k V]
    (ρ σ : RationalRepresentation K V)
    (h : ∀ g, (ρ.action g : Module.End k V) = (σ.action g : Module.End k V))
    (hσ : IsRationalRepresentation σ) : IsRationalRepresentation ρ := by
  rwa [action_ext ρ σ h]

/-- Pull back the actual action, without choosing an existential witness. -/
def pullback {H : Variety k} [AlgebraicGroup H]
    (φ : Theory.AlgebraicGroup.Morphism H K) {V : Type v}
    [AddCommGroup V] [Module k V] (ρ : RationalRepresentation K V) :
    RationalRepresentation H V := ⟨ρ.action.comp φ.onPoints⟩

/-- Regular pullback preserves rationality of the specified action. -/
theorem pullback_rational {H : Variety k} [AlgebraicGroup H]
    (φ : Theory.AlgebraicGroup.Morphism H K) {V : Type v}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) :
    IsRationalRepresentation (pullback φ ρ) := by
  obtain ⟨σ, hσ, hr⟩ := rationalRepresentation_pullback_exists φ ρ hρ
  apply rational_of_action_eq _ σ _ hr
  intro g
  exact congrArg Units.val (hσ g).symm

/-- Point-surjective regular pullback preserves irreducibility. -/
theorem pullback_irreducible {H : Variety k} [AlgebraicGroup H]
    (φ : Theory.AlgebraicGroup.Morphism H K) (hφ : Function.Surjective φ.onPoints)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ) :
    IsIrreducibleRepresentation (pullback φ ρ) := by
  refine ⟨pullback_rational φ ρ hρ.1, fun W hW => hρ.2 W ?_⟩
  intro g v hv
  obtain ⟨h, rfl⟩ := hφ g
  exact hW h v hv

/-- The point endomorphism, retaining the type whose multiplication is composition. -/
def pointEnd (φ : Theory.AlgebraicGroup.Morphism K K) : Monoid.End (Variety.Point K) :=
  φ.onPoints

/-- Iterate the regular morphism. -/
def iterate (φ : Theory.AlgebraicGroup.Morphism K K) : ℕ → Theory.AlgebraicGroup.Morphism K K
  | 0 => .id K
  | n + 1 => φ.comp (iterate φ n)

omit [IsAlgClosed k] in
@[simp] theorem iterate_onPoints (φ : Theory.AlgebraicGroup.Morphism K K) (n : ℕ) :
    pointEnd (iterate φ n) = pointEnd φ ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (pointEnd φ).comp (pointEnd (iterate φ n)) = _
    rw [ih, pow_succ']
    rfl

/-- Regularity of the exact tensor action used in `Construction`. -/
theorem tprod_rational {V : Type v} {W : Type w}
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (ρ : Representation k (Variety.Point K) V)
    (σ : Representation k (Variety.Point K) W)
    (hρ : IsRationalRepresentation (algebraicAction ρ))
    (hσ : IsRationalRepresentation (algebraicAction σ)) :
    IsRationalRepresentation (algebraicAction (Representation.tprod ρ σ)) := by
  obtain ⟨τ, hτ, hr⟩ := rationalRepresentation_tensorProduct_exists
    (algebraicAction ρ) (algebraicAction σ) hρ hσ
  apply rational_of_action_eq _ τ _ hr
  intro g
  apply TensorProduct.ext'
  intro v w
  simpa only [algebraicAction_apply, Representation.tprod_apply, TensorProduct.map_tmul] using (hτ g v w).symm

set_option backward.isDefEq.respectTransparency false in
/-- The empty tensor is the rational trivial line. -/
theorem trivial_rational :
    IsRationalRepresentation (algebraicAction (Representation.trivial k (Variety.Point K) k)) := by
  let f : Theory.AlgebraicGroup.Morphism K (glVarietyOf k k) :=
    { toVariety := Variety.Morphism.const _ _ 1
      map_one := rfl
      map_mul := fun _ _ => (one_mul _).symm }
  refine ⟨Module.finBasis k k, f, ?_⟩
  intro g
  change glPointEquivOf k k (Module.finBasis k k) 1 = _
  rw [← generalLinearRepresentationPoint_one (Module.finBasis k k),
    glPointEquivOf_generalLinearRepresentationPoint]
  apply Units.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The exact point action agrees with pullback along the regular iterate. -/
theorem twistedFactor_eq_pullback (A : BasicWeight → RationalFactor K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (a : BasicWeight) (i : ℕ) :
    algebraicAction (twistedFactor A (pointEnd φ) (MonoidHom.id _) a i).ρ =
      pullback (iterate φ i) (A a).action := by
  apply action_ext
  intro g
  rw [algebraicAction_apply]
  change ((A a).action.action (((pointEnd φ) ^ i) g)).val =
    ((A a).action.action (pointEnd (iterate φ i) g)).val
  rw [iterate_onPoints]

/-- Every twisted basic factor in the construction is rational. -/
theorem twistedFactor_rational (A : BasicWeight → RationalFactor K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (a : BasicWeight) (i : ℕ) :
    IsRationalRepresentation
      (algebraicAction (twistedFactor A (pointEnd φ) (MonoidHom.id _) a i).ρ) := by
  rw [twistedFactor_eq_pullback]
  exact pullback_rational _ _ (A a).irreducible.1

set_option backward.isDefEq.respectTransparency false in
/-- Rationality of the actual tensor, for every length including zero and one. -/
theorem rationalTensor_rational (A : BasicWeight → RationalFactor K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (a : ℕ → BasicWeight) (n : ℕ) :
    IsRationalRepresentation (rationalTensor A (pointEnd φ) a n) := by
  induction n with
  | zero => exact trivial_rational
  | succ n ih => exact tprod_rational _ _ ih (twistedFactor_rational A φ (a n) n)


omit [IsAlgClosed k] in
/-- An actual intertwining linear equivalence transports algebraic irreducibility. -/
theorem algebraicallyIrreducible_of_equiv
    {V : Type v} {W : Type w} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W]
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (e : V ≃ₗ[k] W) (he : Intertwines ρ σ e.toLinearMap)
    (hσ : IsAlgebraicallyIrreducibleRepresentation σ) :
    IsAlgebraicallyIrreducibleRepresentation ρ := by
  intro U hU
  have hmap : IsInvariantSubmodule σ (U.map e.toLinearMap) := by
    intro g w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨(ρ.action g).val v, hU g v hv, he g v⟩
  rcases hσ (U.map e.toLinearMap) hmap with hbot | htop
  · left
    apply eq_bot_iff.mpr
    intro v hv
    have hmem : e v ∈ U.map e.toLinearMap := ⟨v, hv, rfl⟩
    rw [hbot, Submodule.mem_bot] at hmem
    exact e.injective (hmem.trans e.map_zero.symm)
  · right
    apply top_unique
    intro v _
    have hmem : e v ∈ U.map e.toLinearMap := by rw [htop]; trivial
    obtain ⟨w, hw, heq⟩ := hmem
    have hwv : w = v := e.injective heq
    change w ∈ U at hw
    exact hwv ▸ hw

set_option backward.isDefEq.respectTransparency false in
/-- The length-one tensor is irreducible, with no hypothesis on finite restriction. -/
theorem rationalTensor_one_irreducible (A : BasicWeight → RationalFactor K)
    (φ : Theory.AlgebraicGroup.Morphism K K) (a : ℕ → BasicWeight) :
    IsIrreducibleRepresentation (rationalTensor A (pointEnd φ) a 1) := by
  refine ⟨rationalTensor_rational A φ a 1, ?_⟩
  let f := tensorOneEquiv A (pointEnd φ) (MonoidHom.id _) a
  apply algebraicallyIrreducible_of_equiv _ (A (a 0)).action f.toLinearEquiv
    _ (A (a 0)).irreducible.2
  intro g v
  change f.toLinearMap ((tensor A (pointEnd φ) (MonoidHom.id _) a 1).ρ g v) = _
  exact LinearMap.congr_fun (f.isIntertwining' g) v

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
