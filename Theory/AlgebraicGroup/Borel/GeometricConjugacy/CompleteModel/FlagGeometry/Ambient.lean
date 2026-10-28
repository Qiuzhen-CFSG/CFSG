module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.Products
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.Plucker
public import Theory.AlgebraicGroup.Variety.ProjectiveLinearAction
public import Theory.AlgebraicGroup.Representations.Operations

/-!
# The complete ambient space of full flags

Full flags embed on rational points into the finite product of projective
exterior powers. This module constructs that reduced separated finite-type
ambient variety, proves it complete, and transports the injective Plücker map
to its rational points. The degree-zero factor is harmless and lets us use
`Fin (finrank k V)` uniformly, including the empty product in dimension zero.

Algebraic-group morphisms to the exterior general linear groups induce a
regular product action. When their point maps are the exterior powers of the
original representation, the Plücker embedding is equivariant for the exact
`flagAction`. This separates regularity of the exterior operators from
closedness of the incidence image. Source: Borel, *Linear Algebraic Groups*,
§11.1 and its projective flag-variety construction.
-/

@[expose] public noncomputable section

open scoped ExteriorAlgebra LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry

open Variety.Geometric

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Ambient product of projective exterior powers in degrees `0, ..., dim V - 1`.
The degree-zero factor is a point; in dimension zero the whole product is `Spec k`. -/
def flagAmbient : Variety.Geometric k :=
  finProduct (Module.finrank k V) (fun i => projectiveSpace k (⋀[k]^(i : ℕ) V))

theorem flagAmbient_isComplete : IsComplete (flagAmbient (k := k) V) :=
  finProduct_isComplete _ _ (fun _ => projectiveSpace_isComplete _ _)

/-- Choices of coordinates for the finitely many exterior powers. -/
abbrev CoordinateBases := (i : Fin (Module.finrank k V)) →
  Module.Basis (Fin (Module.finrank k (⋀[k]^(i : ℕ) V))) k (⋀[k]^(i : ℕ) V)

variable {V}

/-- Compare rational points of the ambient product with projective exterior tuples. -/
def ambientPointEquiv (b : CoordinateBases (k := k) V) :
    Point (flagAmbient (k := k) V) ≃
      ((i : Fin (Module.finrank k V)) → ℙ k (⋀[k]^(i : ℕ) V)) :=
  (finProductPointEquiv _ _).trans
    (Equiv.piCongrRight fun i => projectiveSpacePointEquivOf (b i))

/-- The genuine Plücker embedding on rational points. -/
def flagEmbedding (b : CoordinateBases (k := k) V) (F : FullFlag k V) :
    Point (flagAmbient (k := k) V) :=
  (ambientPointEquiv b).symm (flagPlucker F)

@[simp] theorem ambientPointEquiv_flagEmbedding (b : CoordinateBases (k := k) V)
    (F : FullFlag k V) : ambientPointEquiv b (flagEmbedding b F) = flagPlucker F :=
  (ambientPointEquiv b).apply_symm_apply _

theorem flagEmbedding_injective (b : CoordinateBases (k := k) V) :
    Function.Injective (flagEmbedding b) :=
  (ambientPointEquiv b).symm.injective.comp flagPlucker_injective

variable {G : Variety k} [AlgebraicGroup G]

/-- Product of projective actions pulled back along actual algebraic-group morphisms. -/
def ambientAction
    (φ : (i : Fin (Module.finrank k V)) →
      Theory.AlgebraicGroup.Morphism G (glVarietyOf k (⋀[k]^(i : ℕ) V))) :
    MorphicAction G (flagAmbient (k := k) V) :=
  finProductAction _ _ (fun i => projectiveLinearMorphicActionPullback _ (φ i))

theorem ambientPointEquiv_action
    (b : CoordinateBases (k := k) V)
    (φ : (i : Fin (Module.finrank k V)) →
      Theory.AlgebraicGroup.Morphism G (glVarietyOf k (⋀[k]^(i : ℕ) V)))
    (g : Variety.Point G) (x : Point (flagAmbient (k := k) V))
    (i : Fin (Module.finrank k V)) :
    ambientPointEquiv b ((ambientAction φ).toMulAction.smul g x) i =
      Projectivization.map (glPointEquivOf k _ (b i) ((φ i).onPoints g)).1
        (glPointEquivOf k _ (b i) ((φ i).onPoints g)).toLinearEquiv.injective
        (ambientPointEquiv b x i) := by
  exact (congrArg (projectiveSpacePointEquivOf (b i))
    (finProductAction_equivariant (Module.finrank k V)
      (fun i => projectiveSpace k (⋀[k]^(i : ℕ) V))
      (fun i => projectiveLinearMorphicActionPullback _ (φ i)) g x i)).trans
        (projectiveLinearMorphicActionPullback_projectiveSpacePointEquivOf _ _ _ _)

/-- A product of rational exterior actions induces exactly the action on full flags. -/
theorem flagEmbedding_equivariant
    (ρ : RationalRepresentation G V) (b : CoordinateBases (k := k) V)
    (φ : (i : Fin (Module.finrank k V)) →
      Theory.AlgebraicGroup.Morphism G (glVarietyOf k (⋀[k]^(i : ℕ) V)))
    (hφ : ∀ i g, glPointEquivOf k _ (b i) ((φ i).onPoints g) =
      (exteriorPowerRepresentation ρ i).action g)
    (g : Variety.Point G) (F : FullFlag k V) :
    flagEmbedding b ((flagAction ρ).smul g F) =
      (ambientAction φ).toMulAction.smul g (flagEmbedding b F) := by
  apply (ambientPointEquiv b).injective
  funext i
  rw [ambientPointEquiv_action]
  rw [ambientPointEquiv_flagEmbedding, ambientPointEquiv_flagEmbedding]
  rw [hφ i g]
  exact flagPlucker_map F (ρ.action g).toLinearEquiv i

end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry
