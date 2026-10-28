module

public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSpaces
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# A torus invariant hyperplane avoiding a vector

The dual of a rational representation is spanned by its torus weight spaces.
Since the full dual separates vectors, some dual weight does not vanish at a
prescribed nonzero vector. Its kernel is invariant under the original torus
action. This supplies the hyperplane in Borel, §§13.5–13.6.
-/

public noncomputable section

namespace Theory.AlgebraicGroup
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- An invariant hyperplane for a torus can avoid any specified nonzero vector. -/
theorem exists_invariant_dual_nonzero
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (T : ClosedSubgroup G) (hT : IsTorus T.carrierVariety) (v : V) (hv : v ≠ 0) :
    ∃ f : Module.Dual k V, f v ≠ 0 ∧
      ∀ (t : Variety.Point T.carrierVariety) w,
        f w = 0 → f ((ρ.action (T.includePoint t)).1 w) = 0 := by
  obtain ⟨τ, hdual, hτ⟩ := rationalRepresentation_dual_exists ρ hρ
  have hspan := closedSubtorusRepresentation_weightSpace_iSup_eq_top τ hτ T hT
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero k hv
  have hex : ∃ (χ : TorusWeight T) (l : Module.Dual k V),
      l ∈ weightSpace τ T χ ∧ l v ≠ 0 := by
    by_contra! h
    have hle : (⨆ χ : TorusWeight T, weightSpace τ T χ) ≤
        LinearMap.ker ((Module.Dual.eval k V) v) := by
      apply iSup_le
      intro χ l hl
      exact h χ l hl
    rw [hspan] at hle
    exact hf (hle (Submodule.mem_top : f ∈ (⊤ : Submodule k (Module.Dual k V))))
  obtain ⟨χ, l, hl, hlv⟩ := hex
  refine ⟨l, hlv, ?_⟩
  intro t w hw
  have hh := congrArg (fun z : Module.Dual k V => z w) (hl t⁻¹)
  rw [hdual] at hh
  have ht : T.includePoint t⁻¹ = (T.includePoint t)⁻¹ :=
    T.inclusion.onPoints.map_inv t
  simpa only [ht, inv_inv, LinearMap.smul_apply, smul_eq_mul, hw, mul_zero] using hh

end Theory.AlgebraicGroup
