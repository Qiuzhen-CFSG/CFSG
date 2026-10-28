module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Theory.AlgebraicGroup.Representations.Operations

/-!
# Rationality of exterior-power representations

For any rational representation of an algebraic group, its prescribed action
on every exterior power is rational. In the exterior basis, matrix coordinates
are minors of the original polynomial matrix. Pulling these coordinates back
along group inversion gives the inverse matrix coordinates, hence an actual
algebraic-group morphism to the general linear group.

The construction includes degree zero and degrees above the dimension, and
requires neither faithfulness nor connectedness. It supplies the exterior
rationality premise in `FlagGeometry.nonempty_flagModel_of_plucker_prerequisites`.

Source: Borel, *Linear Algebraic Groups*, §11.1, the regular action on the flag
variety via projective exterior coordinates. The minor calculation follows
the pattern in `RightTranslation.Exterior`, without its specialized action.
-/

open scoped ExteriorAlgebra

namespace Theory.AlgebraicGroup

universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Every exterior power of a rational representation is rational, including
its zeroth exterior power. The morphism induces the action defined in
`exteriorPowerRepresentation`. -/
public theorem exteriorPowerRepresentation_isRational
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ) (n : ℕ) :
    IsRationalRepresentation (exteriorPowerRepresentation ρ n) := by
  classical
  obtain ⟨e, fρ, hfρ⟩ := hρ
  let E := ⋀[k]^n V
  let I := Set.powersetCard (Fin (Module.finrank k V)) n
  let idx : I ≃ Fin (Module.finrank k E) :=
    (Fintype.equivFin I).trans (finCongr (Module.finrank_eq_card_basis
      (e.exteriorPower n)).symm)
  let b : Module.Basis (Fin (Module.finrank k E)) k E :=
    (e.exteriorPower n).reindex idx
  let minor (s t : I) : G.PolynomialFunction :=
    Matrix.det fun i j => rationalRepresentationMatrixCoefficient ρ e fρ
      (Set.powersetCard.ofFinEmbEquiv.symm s j)
      (Set.powersetCard.ofFinEmbEquiv.symm t i)
  have hminor (s t : I) (g : Variety.Point G) :
      minor s t g = (e.exteriorPower n).repr
        (exteriorPower.map n (ρ.action g).1 ((e.exteriorPower n) t)) s := by
    let ev : G.PolynomialFunction →+* k :=
      { toFun := fun f => f g
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let M : Matrix (Fin n) (Fin n) G.PolynomialFunction := fun i j =>
      rationalRepresentationMatrixCoefficient ρ e fρ
        (Set.powersetCard.ofFinEmbEquiv.symm s j)
        (Set.powersetCard.ofFinEmbEquiv.symm t i)
    change ev (Matrix.det M) = _
    rw [RingHom.map_det]
    change (Matrix.det fun i j => rationalRepresentationMatrixCoefficient ρ e fρ
      (Set.powersetCard.ofFinEmbEquiv.symm s j)
      (Set.powersetCard.ofFinEmbEquiv.symm t i) g) = _
    rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
      exteriorPower.map_apply_ιMulti_family, exteriorPower.ιMulti_family,
      exteriorPower.ιMultiDual_apply_ιMulti]
    congr 1
    ext i j
    rw [rationalRepresentationMatrixCoefficient_apply ρ e fρ hfρ]
    rfl
  let τ := exteriorPowerRepresentation ρ n
  let c (i j : Fin (Module.finrank k E)) : G.PolynomialFunction :=
    minor (idx.symm i) (idx.symm j)
  have hc : ∀ i j g, c i j g = b.repr ((τ.action g).1 (b j)) i := by
    intro i j g
    change minor (idx.symm i) (idx.symm j) g = _
    rw [show b j = (e.exteriorPower n) (idx.symm j) from
      Module.Basis.reindex_apply _ _ _]
    exact hminor (idx.symm i) (idx.symm j) g
  let cInv (i j : Fin (Module.finrank k E)) : G.PolynomialFunction :=
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G) (c i j)
  have hcInv : ∀ i j g, cInv i j g =
      b.repr ((((τ.action g)⁻¹ : LinearMap.GeneralLinearGroup k E) :
        Module.End k E) (b j)) i := by
    intro i j g
    change c i j g⁻¹ = _
    rw [hc]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    b τ.action c cInv hc hcInv
  refine ⟨b, f, ?_⟩
  intro g
  change glPointEquivOf k E b (generalLinearRepresentationPoint b (τ.action g)) = _
  exact glPointEquivOf_generalLinearRepresentationPoint b (τ.action g)

end Theory.AlgebraicGroup
