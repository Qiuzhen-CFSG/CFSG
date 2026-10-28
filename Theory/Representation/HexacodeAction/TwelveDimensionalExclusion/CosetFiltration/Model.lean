module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Data
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.Generators
public import Theory.Representation.G2DerivedPermutationFiltration.VertexFiltrations.Transport
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# Word action and the exact central coset coordinate contract

The checked monomial tables define invertible linear operators, hence an
action of the free group on two letters. Its homomorphism to the actual even
hexacode cover is surjective by the existing generating-pair theorem.
An equivariant basis of the literal coset eigenspace needs only the two
generator equations: those imply intertwining on every word. Consequently a
filtration of the word action transports to the requested coset representation.

Source application: Aschbacher–Smith K.1.3, printed p.453 (PDF p.464).
This module does not assert existence of the coset coordinates or filtration.
-/

@[expose] public section
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate

abbrev WordGroup := FreeGroup (Fin 2)

/-- The checked monomial generator, applied to column vectors. -/
def generator (j : Fin 2) : Space ≃ₗ[F] Space where
  toFun v i := coefficient j i * v (rowSource j i)
  invFun v i := (coefficient j (inverseSource j i))⁻¹ * v (inverseSource j i)
  left_inv v := by
    funext i
    simp only [inverseSource_right, ← mul_assoc, inv_mul_cancel₀ (coefficient_ne_zero _ _),
      one_mul]
  right_inv v := by
    funext i
    simp only [inverseSource_left, ← mul_assoc, mul_inv_cancel₀ (coefficient_ne_zero _ _),
      one_mul]
  map_add' v w := by
    funext i
    exact mul_add _ _ _
  map_smul' a v := by
    funext i
    exact mul_left_comm _ _ _

def wordAction : WordGroup →* (Space ≃ₗ[F] Space) := FreeGroup.lift generator

/-- The concrete word representation; no cover identification is assumed. -/
def representation : Representation F WordGroup Space :=
  LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp wordAction

@[simp] theorem representation_of_apply (j : Fin 2) (v : Space) (i : Fin 45) :
    representation (FreeGroup.of j) v i = coefficient j i * v (rowSource j i) := by
  change wordAction (FreeGroup.of j) v i = _
  rw [wordAction, FreeGroup.lift_apply_of]
  rfl

theorem representation_of_matrix (j : Fin 2) (v : Space) :
    representation (FreeGroup.of j) v = (generatorMatrix j).mulVec v := by
  funext i
  simp [Matrix.mulVec, dotProduct, generatorMatrix, representation_of_apply]

/-- The actual marked generating pair, in the witness alphabet's order. -/
def coverGenerator : Fin 2 → Cover :=
  ![SixDimensional.EvenImage.generatorA, SixDimensional.EvenImage.generatorB]

def coverHom : WordGroup →* Cover := FreeGroup.lift coverGenerator

@[simp] theorem coverHom_of (j : Fin 2) :
    coverHom (FreeGroup.of j) = coverGenerator j := FreeGroup.lift_apply_of

theorem coverHom_surjective : Function.Surjective coverHom := by
  apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr
  have hr : Set.range coverGenerator =
      {SixDimensional.EvenImage.generatorA, SixDimensional.EvenImage.generatorB} := by
    ext x
    simp [coverGenerator, or_comm]
  rw [hr, SixDimensional.EvenImage.generators_closure]

/-- Evaluate the integer-exponent witness words in the literal cover. -/
def evalWord (w : List (Fin 2 × ℤ)) : Cover :=
  (w.map fun a => coverGenerator a.1 ^ a.2).prod

/-- The required model identification: a Sylow subgroup and a basis of its
literal omega-eigenspace, intertwining the two marked generators. -/
structure CosetCoordinates where
  sylow : Sylow 2 Cover
  coordinates : Space ≃ₗ[F] (centralEigenspace (cosetRepresentation (sylow : Subgroup Cover))).toSubmodule
  generator_coordinates : ∀ j v,
    coordinates (generator j v) =
      cosetCentralRepresentation (sylow : Subgroup Cover) (coverGenerator j) (coordinates v)

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- Agreement on the two generators implies equivariance on every word. -/
theorem intertwines_words (σ : Representation F Cover V) (e : Space ≃ₗ[F] V)
    (he : ∀ j v, e (generator j v) = σ (coverGenerator j) (e v)) :
    ∀ g v, e (representation g v) = σ (coverHom g) (e v) := by
  have h : (e.conjAlgEquiv F).toMonoidHom.comp representation = σ.comp coverHom := by
    apply FreeGroup.ext_hom
    intro j
    apply LinearMap.ext
    intro v
    change e (representation (FreeGroup.of j) (e.symm v)) =
      σ (coverHom (FreeGroup.of j)) v
    rw [coverHom_of]
    change e (generator j (e.symm v)) = _
    rw [he, e.apply_symm_apply]
  intro g v
  have hv := LinearMap.congr_fun (DFunLike.congr_fun h g) (e v)
  change e (representation g (e.symm (e v))) = σ (coverHom g) (e v) at hv
  simpa only [e.symm_apply_apply] using hv

/-- The concrete word filtration gives the literal coset filtration once its
coordinate certificate is supplied. -/
theorem cosetFiltration_of_wordFiltration (C : CosetCoordinates)
    (h : FactorDegreeFiltration ({3, 9} : Set ℕ) representation) : CosetFiltration := by
  refine ⟨C.sylow, ?_⟩
  exact h.transport coverHom coverHom_surjective _ C.coordinates
    (intertwines_words _ C.coordinates C.generator_coordinates)

end Representation.Hexacode.TwelveDimensional.CosetCertificate
