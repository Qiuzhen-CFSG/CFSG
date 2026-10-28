module

public import Theory.AlgebraicGroup.Bor1.WeightBlocks
public import Theory.AlgebraicGroup.PluckerOrbit.Conjugation
public import Theory.AlgebraicGroup.Representations.Operations

universe u v w

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- The conjugation action induced on the full endomorphism space by a
rational representation. -/
@[expose]
public noncomputable def conjEndRationalRepresentation
    (ρ : RationalRepresentation G V) :
    RationalRepresentation G (Module.End k V) :=
  ⟨conjEndRepresentation.comp ρ.action⟩

/-- Conjugation on the full endomorphism space is rational whenever the
original representation is rational. -/
public theorem conjEndRationalRepresentation_isRational
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ) :
    IsRationalRepresentation (conjEndRationalRepresentation ρ) := by
  rcases hρ with ⟨b, f, hf⟩
  let e := generalLinearConjugationEndBasis b
  let idx := generalLinearConjugationEndIndexEquiv (k := k) (V := V)
  let matrixCoefficient :
      Fin (Module.finrank k (Module.End k V)) →
        Fin (Module.finrank k (Module.End k V)) →
          G.PolynomialFunction := fun i j =>
    rationalRepresentationMatrixCoefficient ρ b f
        (idx.symm i).1 (idx.symm j).1 *
      rationalRepresentationInverseMatrixCoefficient ρ b f
        (idx.symm j).2 (idx.symm i).2
  have matrixCoefficient_apply : ∀ i j g,
      matrixCoefficient i j g =
        e.repr ((((conjEndRationalRepresentation ρ).action g :
          Module.End k (Module.End k V))) (e j)) i := by
    intro i j g
    change
      rationalRepresentationMatrixCoefficient ρ b f
          (idx.symm i).1 (idx.symm j).1 g *
        rationalRepresentationInverseMatrixCoefficient ρ b f
          (idx.symm j).2 (idx.symm i).2 g = _
    rw [rationalRepresentationMatrixCoefficient_apply ρ b f hf]
    rw [rationalRepresentationInverseMatrixCoefficient_apply ρ b f hf]
    have hconj :
        conjEndGeneralLinear (ρ.action g) =
          generalLinearConjugationRepresentation (ρ.action g) := by
      apply Units.ext
      rfl
    change _ = e.repr
      (((conjEndGeneralLinear (ρ.action g) :
        LinearMap.GeneralLinearGroup k (Module.End k V)) :
        Module.End k (Module.End k V)) (e j)) i
    rw [hconj]
    exact (generalLinearConjugationRepresentation_finMatrixCoefficient
      b (ρ.action g) i j).symm
  let inverseMatrixCoefficient :
      Fin (Module.finrank k (Module.End k V)) →
        Fin (Module.finrank k (Module.End k V)) →
          G.PolynomialFunction := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
      (matrixCoefficient i j)
  have inverseMatrixCoefficient_apply : ∀ i j g,
      inverseMatrixCoefficient i j g =
        e.repr (((((conjEndRationalRepresentation ρ).action g)⁻¹ :
          LinearMap.GeneralLinearGroup k (Module.End k V)) :
          Module.End k (Module.End k V)) (e j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [matrixCoefficient_apply]
    simp
  let F := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    e (conjEndRationalRepresentation ρ).action matrixCoefficient
      inverseMatrixCoefficient matrixCoefficient_apply
      inverseMatrixCoefficient_apply
  refine ⟨e, F, ?_⟩
  intro g
  change glPointEquivOf k (Module.End k V) e
    (generalLinearRepresentationPoint e
      ((conjEndRationalRepresentation ρ).action g)) =
        (conjEndRationalRepresentation ρ).action g
  exact glPointEquivOf_generalLinearRepresentationPoint e
    ((conjEndRationalRepresentation ρ).action g)

/-- The rational representation whose action is conjugation on a
block-diagonal endomorphism subspace. -/
@[expose]
public noncomputable def blockDiagonalEndConjRationalRepresentation
    {ι : Type w} (E : ι → Submodule k V)
    (ρ : RationalRepresentation G V) (σ : Variety.Point G →* Equiv.Perm ι)
    (hE : ∀ g i, Submodule.map
      ((ρ.action g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i)) :
    RationalRepresentation G (blockDiagonalEnd E) :=
  ⟨blockDiagonalEnd_conjRepresentation E ρ.action σ hE⟩

/-- Restricting rational conjugation to a permuted block-diagonal
endomorphism subspace remains rational. -/
public theorem blockDiagonalEndConjRationalRepresentation_isRational
    {ι : Type w} (E : ι → Submodule k V)
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (σ : Variety.Point G →* Equiv.Perm ι)
    (hE : ∀ g i, Submodule.map
      ((ρ.action g : LinearMap.GeneralLinearGroup k V) : Module.End k V) (E i) =
        E ((σ g : Equiv ι ι) i)) :
    IsRationalRepresentation
      (blockDiagonalEndConjRationalRepresentation E ρ σ hE) := by
  have hBlock : IsInvariantSubmodule (conjEndRationalRepresentation ρ)
      (blockDiagonalEnd E) := by
    intro g u hu
    exact blockDiagonalEnd_conj_mem E (σ g) (ρ.action g) (hE g) u hu
  obtain ⟨τ, hτ, hτrat⟩ := rationalRepresentation_restriction_exists
    (conjEndRationalRepresentation ρ)
      (conjEndRationalRepresentation_isRational ρ hρ)
      (blockDiagonalEnd E) hBlock
  have haction : τ.action =
      (blockDiagonalEndConjRationalRepresentation E ρ σ hE).action := by
    apply MonoidHom.ext
    intro g
    apply Units.ext
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    rw [show
      (blockDiagonalEndConjRationalRepresentation E ρ σ hE).action =
        blockDiagonalEnd_conjRepresentation E ρ.action σ hE by rfl]
    unfold blockDiagonalEnd_conjRepresentation
    change ((τ.action g : Module.End k (blockDiagonalEnd E)) u).1 =
      (blockDiagonalEnd_conjLinearMap E (σ g) (ρ.action g) (hE g) u).1
    rw [blockDiagonalEnd_conjLinearMap_apply]
    exact hτ g u
  rcases hτrat with ⟨b, f, hf⟩
  refine ⟨b, f, ?_⟩
  intro g
  rw [← haction]
  exact hf g

end Theory.AlgebraicGroup.Bor1
