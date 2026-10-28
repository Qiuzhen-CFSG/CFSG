module

public import Theory.AlgebraicGroup.Representations.Matrix

universe u v

/-! Realizing rational representations by regular matrix morphisms in an
arbitrary finite basis. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A rational representation is represented by an algebraic-group morphism
to a general linear group in every finite basis. -/
public theorem IsRationalRepresentation.exists_morphism_in_basis
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
    {ρ : RationalRepresentation G V} (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    ∃ f : AlgebraicGroup.Morphism G (glVarietyOf k V),
      ∀ g, glPointEquivOf k V b (f.onPoints g) = ρ.action g := by
  rcases hρ with ⟨e, f, hf⟩
  let c (i j : Fin (Module.finrank k V)) : G.PolynomialFunction :=
    rationalRepresentationLinearMatrixCoefficient ρ e f (b.coord i) (b j)
  let cInv (i j : Fin (Module.finrank k V)) : G.PolynomialFunction :=
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
      (c i j)
  have hc (i j : Fin (Module.finrank k V)) (g : Variety.Point G) :
      c i j g = b.repr ((ρ.action g : Module.End k V) (b j)) i := by
    exact rationalRepresentationLinearMatrixCoefficient_apply
      ρ e f hf (b.coord i) (b j) g
  have hcInv (i j : Fin (Module.finrank k V)) (g : Variety.Point G) :
      cInv i j g =
        b.repr (((((ρ.action g)⁻¹ : LinearMap.GeneralLinearGroup k V) :
          Module.End k V)) (b j)) i := by
    change c i j g⁻¹ = _
    rw [hc]
    simp
  let F := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b ρ.action c cInv hc hcInv
  refine ⟨F, fun g ↦ ?_⟩
  change glPointEquivOf k V b
    (generalLinearRepresentationPoint b (ρ.action g)) = ρ.action g
  exact glPointEquivOf_generalLinearRepresentationPoint b (ρ.action g)

end Theory.AlgebraicGroup
