module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ScalarCoordinates
public import Mathlib.Algebra.CharP.Two

/-!+# Comparing the two actions on the same unitary core section

This is the coefficient comparison in Fong--Seitz II, (8.7)--(8.8),
printed pp.201--202. The displacement is computed in one additive section,
and its root line is injectively labelled. The natural module and the
four-dimensional tensor form initially use unrelated scalar twists and
two unnormalized basis vectors. Evaluation at 1 and theta forces the
basis labels and both twist identities. Extending the resulting finite-field
automorphism then normalizes the same displacement, with no compatibility
assumption between the two initial labels.

These are consequences of the two module calculations, not constructions
of those source modules; the source reconstruction retains that obligation.
-/

public noncomputable section
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource

variable {F E V : Type*} [Field F] [Field E] [CharP E 2] [AddCommGroup V]

/-- Compare (8.7) and (8.8) in their common section. The minus sign records
the reversed commutator order; it disappears because the root labels have
characteristic two. In particular neither basis normalization is assumed. -/
theorem same_section_twists (ι κ : F →+* E) (τ₁ τ₂ ρ : F ≃+* F)
    (θ x y : E) (u : E →+ V) (hu : Function.Injective u) (δ : E → F → V)
    (hnatural : ∀ a b, δ a b = u (a*κ b))
    (htensor : ∀ a₁ a₂ b,
      -δ (ι a₁+ι a₂*θ) b =
        u (ι (τ₂ (τ₁.symm b)) *
          (ι (τ₂ (ρ a₁))*x+ι (τ₂ (ρ a₂))*y))) :
    x = 1 ∧ y = θ ∧ (∀ b, κ b = ι (τ₂ (τ₁.symm b))) ∧
      ρ.trans τ₂ = RingEquiv.refl F := by
  have he (a₁ a₂ b : F) :
      (ι a₁+ι a₂*θ)*κ b = ι (τ₂ (τ₁.symm b)) *
        (ι (τ₂ (ρ a₁))*x+ι (τ₂ (ρ a₂))*y) := by
    apply hu
    have h := htensor a₁ a₂ b
    rw [hnatural, ← map_neg, CharTwo.neg_eq] at h
    exact h
  have hx : x = 1 := by simpa only [map_zero, map_one, zero_mul, one_mul,
    mul_one, add_zero] using (he 1 0 1).symm
  have hy : y = θ := by simpa only [map_zero, map_one, zero_mul, one_mul,
    mul_one, zero_add] using (he 0 1 1).symm
  have hk (b : F) : κ b = ι (τ₂ (τ₁.symm b)) := by
    simpa only [map_zero, map_one, zero_mul, one_mul, mul_one, add_zero, hx] using he 1 0 b
  refine ⟨hx, hy, hk, ?_⟩
  ext a
  apply ι.injective
  simpa only [map_zero, map_one, zero_mul, one_mul, mul_one, add_zero, hx,
    RingEquiv.trans_apply, RingEquiv.refl_apply] using (he a 0 1).symm

variable [Finite F] [Finite E] [CharP F 2]

/-- The comparison constructs the relabeling of the same E-parametrized
root. Its restriction is the natural-module coefficient, and its
reparametrized displacement is the ordinary product a*b. -/
theorem exists_common_field_labels (ι κ : F →+* E) (τ₁ τ₂ ρ : F ≃+* F)
    (θ x y : E) (u : E →+ V) (hu : Function.Injective u) (δ : E → F → V)
    (hnatural : ∀ a b, δ a b = u (a*κ b))
    (htensor : ∀ a₁ a₂ b,
      -δ (ι a₁+ι a₂*θ) b =
        u (ι (τ₂ (τ₁.symm b)) *
          (ι (τ₂ (ρ a₁))*x+ι (τ₂ (ρ a₂))*y))) :
    x = 1 ∧ y = θ ∧ ρ.trans τ₂ = RingEquiv.refl F ∧
      ∃ η : E ≃+* E,
        (∀ b, η (ι b) = κ b) ∧
        (∀ a b, δ (η a) b = (u.comp η.toAddMonoidHom) (a*ι b)) ∧
        ∀ (σ : E ≃+* E) a, η (σ a) = σ (η a) := by
  obtain ⟨hx, hy, hk, hρ⟩ := same_section_twists ι κ τ₁ τ₂ ρ θ x y u hu δ hnatural htensor
  obtain ⟨η, hη, hc⟩ := exists_extending_automorphism ι (τ₁.symm.trans τ₂)
  have hκ (b : F) : η (ι b) = κ b := (hη b).trans (hk b).symm
  refine ⟨hx, hy, hρ, η, hκ, ?_, hc⟩
  intro a b
  change δ (η a) b = u (η (a*ι b))
  rw [hnatural, η.map_mul, hκ]

omit [Finite F] [Finite E] [CharP F 2] [CharP E 2] in
/-- The very same extending automorphism also matches the scalar actions
on the relabelled second root line. -/
theorem relabel_scalar_action [Module F V] (ι : F →+* E)
    (τ₁ τ₂ : F ≃+* F) (η : E ≃+* E)
    (hη : ∀ a, η (ι a) = ι (τ₂ (τ₁.symm a)))
    (u : E →+ V) (hscalar : ∀ a b, a • u b = u (ι (τ₂ a)*b)) (a : F) (b : E) :
    a • (u.comp η.toAddMonoidHom) b =
      (u.comp η.toAddMonoidHom) (ι (τ₁ a)*b) := by
  change a • u (η b) = u (η (ι (τ₁ a)*b))
  rw [hscalar, η.map_mul, hη, RingEquiv.symm_apply_apply]

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
