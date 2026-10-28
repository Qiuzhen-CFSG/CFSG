module

public import Theory.AlgebraicGroup.RightTranslation.ExteriorRational
public import Theory.AlgebraicGroup.Variety.ProjectiveLinearAction
public import Theory.AlgebraicGroup.Bor1.BorelHomogeneousSpace

/-!
# The literal Chevalley projective action

The rational exterior representation of a closed subgroup's defining ideal
induces a regular projective action with that exact subgroup as stabilizer.
The abstract rational-to-projective comparison is kept separate from the
concrete exterior space to avoid expensive elaboration by unfolding its
coordinate construction. This supplies Borel, §§5.1 and 13.6–13.7.
-/

public noncomputable section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization
open Theory.AlgebraicGroup.Variety.Geometric
namespace Theory.AlgebraicGroup.Bor1.TorusBorelGeneration
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private theorem exists_regular_projectivization
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (ρ : RationalRepresentation G E) (hρ : IsRationalRepresentation ρ) :
    ∃ (b : Module.Basis (Fin (Module.finrank k E)) k E)
      (A : MorphicAction G (projectiveSpace k E)),
      ∀ (g : Variety.Point G) (p : Point (projectiveSpace k E)),
        projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
        Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
          (projectiveSpacePointEquivOf b p) := by
  obtain ⟨b, φ, hφ⟩ := hρ
  refine ⟨b, projectiveLinearMorphicActionPullback E φ, ?_⟩
  intro g p
  rw [projectiveLinearMorphicActionPullback_projectiveSpacePointEquivOf b φ g p, hφ g]

/-- The actual Chevalley projective action is regular, rational and has the
prescribed closed subgroup as its exact point stabilizer. -/
theorem exists_projective_action_stabilizer (H : ClosedSubgroup G) :
    ∃ (E : Type u) (_ : AddCommGroup E) (_ : Module k E) (_ : FiniteDimensional k E)
      (ρ : RationalRepresentation G E)
      (b : Module.Basis (Fin (Module.finrank k E)) k E)
      (A : MorphicAction G (projectiveSpace k E)) (x : Point (projectiveSpace k E)),
      IsRationalRepresentation ρ ∧
      (∀ (g : Variety.Point G) (p : Point (projectiveSpace k E)),
        projectiveSpacePointEquivOf b (A.toMulAction.smul g p) =
        Projectivization.map (ρ.action g).1 (ρ.action g).toLinearEquiv.injective
          (projectiveSpacePointEquivOf b p)) ∧
      (∀ g : Variety.Point G, A.toMulAction.smul g x = x ↔ g ∈ H.toSubgroup) := by
  let E := ⋀[k]^H.rightTranslateVanishingTopWedgeData.degree H.rightTranslateVanishingSpan
  let ρ := H.rightTranslateVanishingExteriorRationalRepresentation
  have hρ : IsRationalRepresentation ρ :=
    H.rightTranslateVanishingExteriorRationalRepresentation_isRational
  obtain ⟨b, A, he⟩ := exists_regular_projectivization ρ hρ
  let x := (projectiveSpacePointEquivOf b).symm H.rightTranslateVanishingPluckerPoint
  refine ⟨E, inferInstance, inferInstance, inferInstance, ρ, b, A, x, hρ, he, ?_⟩
  intro g
  rw [← (projectiveSpacePointEquivOf b).injective.eq_iff, he]
  simp only [x, Equiv.apply_symm_apply]
  exact closedSubgroup_chevalleyPluckerPoint_fixed_iff H g

end Theory.AlgebraicGroup.Bor1.TorusBorelGeneration
