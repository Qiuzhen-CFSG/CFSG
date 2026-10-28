module

public import Theory.AlgebraicGroup.Variety.GeometricOpenGluing
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.PointAction

/-!
# Gluing the local regular representatives of a projective-line action

The point homomorphism of the original morphic action is already proved.
If genuine local geometric maps on a covering family of opens realize that
same homomorphism through the literal affine point equivalences, ordinary
geometric open gluing gives its unique global geometric representative.

The remaining local maps and chart-cover premises are exactly the regular
triple-family calculations in Borel 10.8/13.13; the family-assembly module
supplies them. No global algebraic regularity is part of this input.
-/

@[expose] public section

open AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Exact family-assembly consumer: local genuine representatives of the proved
point homomorphism give a unique global geometric map. -/
theorem pointActionHom_existsUnique_of_local_representatives
    {H : Theory.AlgebraicGroup.Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) {ι : Type v}
    (U : ι → (ofAffine H).toScheme.Opens) (hU : ⨆ i, U i = ⊤)
    (F : ∀ i, Morphism (openSubvariety (ofAffine H) (U i)).toGeometric
      (ofAffine (pgl2Variety (k := k))))
    (hF : ∀ i p, (affinePointEquiv (pgl2Variety (k := k))) (F i p) =
      pointActionHom A (affinePointEquiv H ((openSubvariety (ofAffine H) (U i)).inclusion p))) :
    ∃! f : Morphism (ofAffine H) (ofAffine (pgl2Variety (k := k))),
      ∀ p, affinePointEquiv (pgl2Variety (k := k)) (f p) =
        pointActionHom A (affinePointEquiv H p) := by
  let ψ : Point (ofAffine H) → Point (ofAffine (pgl2Variety (k := k))) := fun p =>
    (affinePointEquiv (pgl2Variety (k := k))).symm (pointActionHom A (affinePointEquiv H p))
  have hh : ∀ i p, F i p = ψ ((openSubvariety (ofAffine H) (U i)).inclusion p) := by
    intro i p
    apply (affinePointEquiv (pgl2Variety (k := k))).injective
    simpa only [ψ,Equiv.apply_symm_apply] using hF i p
  obtain ⟨f,hf,huniq⟩ := existsUnique_morphism_of_open_local_representatives U hU F ψ hh
  refine ⟨f,?_,?_⟩
  · intro p
    rw [hf]
    exact (affinePointEquiv (pgl2Variety (k := k))).apply_symm_apply _
  · intro g hg
    apply huniq
    intro p
    apply (affinePointEquiv (pgl2Variety (k := k))).injective
    simpa only [ψ,Equiv.apply_symm_apply] using hg p

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
