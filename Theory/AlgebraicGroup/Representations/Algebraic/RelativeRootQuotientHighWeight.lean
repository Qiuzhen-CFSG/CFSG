module

public import Theory.AlgebraicGroup.Representations.Algebraic.RelativeRoot

/-!
# High weights on relative-root quotient models

This module supplies the quotient-first high-weight interface needed for a
relative-root fiber represented directly as a Levi module.  Unlike
`relativeRootFiberGenerator_hasHighWeight_of_rootAction`, it does not require
an ambient representation followed by quotient, pullback, and restriction.
Instead, the generator action is stated directly in the target module, while
its label action remains inside the exact relative-root fiber by construction.

For a nonzero parameter, Borel label fixation turns the acted generator into a
scalar multiple by dividing its new parameter by the original one and using
parameter homogeneity.  Torus label fixation and compatibility of the parameter
scalar with the prescribed character give the weight-vector equation in the
same way.  This is the elementary representation-theoretic step used before
GLS3, Theorem 1.14.7; the geometric conjugation laws that instantiate it remain
separate source-level inputs.
-/

universe u v

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k]

/-- A canonical relative-root fiber generator is a high-weight vector when a
Levi representation acts on its exact quotient model by the given label and
parameter actions, the Borel and torus fix its label, and the torus parameter
is scaled by the prescribed character. -/
public theorem relativeRootFiberGenerator_hasHighWeight_of_quotientRootAction
    {K L : Variety k} [AlgebraicGroup K] [AlgebraicGroup L]
    {T : ClosedSubgroup K}
    (D : RootGroupData K T) [Finite D.Root]
    (J : Set D.Root) (coeff : D.Root → D.Root → ℤ)
    (i : ℤ) (β : D.Root)
    {V : Type v} [AddCommGroup V] [Module k V]
    (ρfiber : RationalRepresentation L V)
    (rootVector :
      {γ : D.Root // γ ∈ relativeRootFiberAtHeight D coeff J i β} → k → V)
    (rootAction : Variety.Point L →
      {γ : D.Root // γ ∈ relativeRootFiberAtHeight D coeff J i β} →
      {γ : D.Root // γ ∈ relativeRootFiberAtHeight D coeff J i β})
    (rootScalar : Variety.Point L →
      {γ : D.Root // γ ∈ relativeRootFiberAtHeight D coeff J i β} → k → k)
    (hRootVector : ∀ l γ z,
      (ρfiber.action l).1 (rootVector γ z) =
        rootVector (rootAction l γ) (rootScalar l γ z))
    (B₀ T₀ : ClosedSubgroup L)
    (γ : {δ : D.Root // δ ∈ relativeRootFiberAtHeight D coeff J i β})
    (z : k) (hz : z ≠ 0) (χ : TorusWeight T₀)
    (hgenerator : rootVector γ z ≠ 0)
    (hsmul : ∀ c : k, rootVector γ (c * z) = c • rootVector γ z)
    (hBfixed : ∀ l, l ∈ B₀ → rootAction l γ = γ)
    (hTfixed : ∀ t : Variety.Point T₀.carrierVariety,
      rootAction (T₀.includePoint t) γ = γ)
    (hTscalar : ∀ t : Variety.Point T₀.carrierVariety,
      rootScalar (T₀.includePoint t) γ z = χ.pointCharacter t * z) :
    HasHighWeight ρfiber B₀ T₀ (rootVector γ z) χ := by
  constructor
  · refine ⟨hgenerator, ?_⟩
    intro l hl
    let c := rootScalar l γ z / z
    refine ⟨c, ?_⟩
    rw [hRootVector, hBfixed l hl]
    rw [show rootScalar l γ z = c * z by simp [c, hz], hsmul]
  · refine ⟨hgenerator, ?_⟩
    intro t
    rw [hRootVector, hTfixed t, hTscalar t, hsmul]

end Theory.AlgebraicGroup
