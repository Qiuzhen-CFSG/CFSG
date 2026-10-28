module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Cubic.Actor
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Cubic.Certificates
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.ActorCoverage
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.ModelFlag.FactorSimplicity.Coordinates

/-!
# Spectra on both literal degree-21 cubic quotients

The existing first and last quotient maps identify the literal quotients
with the same nilpotent image. Composing with its checked image coordinates
transfers the finite certificates. The actor coverage theorem then handles
every element of order seven. The coefficient scalar is the original inverse
Borel-character value, including both nontrivial cubic characters.
Source application: Guralnick–Malle, Proposition 4.3, pp.10–11;
Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public noncomputable section
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic
open Degrees.CubicCalculation ModelFlag FactorCoordinates
open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations
universe v
attribute [local irreducible] generatorMatrix nilpotentMatrix imageMatrices imageCoordinates

private theorem spectrum_of_coordinates
    {K U : Type*} [Field K] [CharP K 2] [AddCommGroup U] [Module K U]
    [FiniteDimensional K U] (ρ : Representation K (standardGroup modelForm) U)
    (z : K) (hz : z ^ 2 + z + 1 = 0)
    (a : Fin 2 → standardGroup modelForm) (ha : word a = actor)
    (e : U ≃ₗ[K] (Fin 21 → K))
    (he : ∀ i u, e (ρ (a i) u) =
      ((imageMatrices i).map (evaluate z hz)).mulVec (e u))
    (x : standardGroup modelForm) (hx : orderOf x = 7) :
    (ρ x).charpoly = sevenSpectrum K 21 := by
  let f : Matrix (Fin 21) (Fin 21) CoefficientField →+*
      Matrix (Fin 21) (Fin 21) K := (evaluate z hz).mapMatrix
  have hg (i : Fin 2) : e.conjAlgEquiv K (ρ (a i)) = (f (imageMatrices i)).toLin' := by
    apply LinearMap.ext
    intro v
    change e (ρ (a i) (e.symm v)) = (f (imageMatrices i)).mulVec v
    rw [he, e.apply_symm_apply]
    rfl
  have hp (k : ℕ) : e.conjAlgEquiv K (ρ (word a ^ k)) = (f (word imageMatrices ^ k)).toLin' := by
    simp only [map_pow, word, map_mul]
    simp only [hg, Matrix.toLin'_pow, Matrix.toLin'_mul, Module.End.mul_eq_comp]
  apply charpoly_of_order_seven_generator_powers modelForm
    (by
      let : Fact (Nat.Prime 5) := ⟨by decide⟩
      exact GaloisField.card 5 2 (by decide)) ρ actor actor_order _ ?_ x hx
  intro k hk0 hk7
  rw [← ha, ← e.charpoly_conj]
  change (e.conjAlgEquiv K (ρ (word a ^ k))).charpoly = _
  rw [hp, Matrix.charpoly_toLin']
  exact evaluated_spectrum z hz k hk0 hk7

variable {K : Type v} [Field K] [CharP K 2]
  {χ : standardBorel modelForm →* Kˣ} (c : Coordinates χ)

def firstCoordinates :
    (((c.flag matrix_relations).stage 1).toSubmodule ⧸
      (within ((c.flag matrix_relations).stage 0)
        ((c.flag matrix_relations).stage 1)).toSubmodule) ≃ₗ[K] (Fin 21 → K) :=
  (c.firstQuotientCoordinates matrix_relations).trans (imageCoordinates c.z c.quadratic)

def lastCoordinates :
    (((c.flag matrix_relations).stage 3).toSubmodule ⧸
      (within ((c.flag matrix_relations).stage 2)
        ((c.flag matrix_relations).stage 3)).toSubmodule) ≃ₗ[K] (Fin 21 → K) :=
  (c.lastQuotientCoordinates matrix_relations).trans (imageCoordinates c.z c.quadratic)

theorem firstCoordinates_action (i : Fin 2)
    (u : ((c.flag matrix_relations).stage 1).toSubmodule ⧸
      (within ((c.flag matrix_relations).stage 0)
        ((c.flag matrix_relations).stage 1)).toSubmodule) :
    firstCoordinates c
      ((within ((c.flag matrix_relations).stage 0)
        ((c.flag matrix_relations).stage 1)).quotientRepresentation (c.actor i) u) =
      ((imageMatrices i).map (evaluate c.z c.quadratic)).mulVec (firstCoordinates c u) := by
  have h : c.firstQuotientCoordinates matrix_relations
      ((within ((c.flag matrix_relations).stage 0)
        ((c.flag matrix_relations).stage 1)).quotientRepresentation (c.actor i) u) =
      FactorSimplicity.imageActor c.z c.quadratic matrix_relations i
        (c.firstQuotientCoordinates matrix_relations u) := by
    apply Subtype.ext
    exact c.firstQuotientCoordinates_action matrix_relations i u
  exact (congrArg (imageCoordinates c.z c.quadratic) h).trans
    (image_action c.z c.quadratic matrix_relations i _)

theorem lastCoordinates_action (i : Fin 2)
    (u : ((c.flag matrix_relations).stage 3).toSubmodule ⧸
      (within ((c.flag matrix_relations).stage 2)
        ((c.flag matrix_relations).stage 3)).toSubmodule) :
    lastCoordinates c
      ((within ((c.flag matrix_relations).stage 2)
        ((c.flag matrix_relations).stage 3)).quotientRepresentation (c.actor i) u) =
      ((imageMatrices i).map (evaluate c.z c.quadratic)).mulVec (lastCoordinates c u) := by
  have h : c.lastQuotientCoordinates matrix_relations
      ((within ((c.flag matrix_relations).stage 2)
        ((c.flag matrix_relations).stage 3)).quotientRepresentation (c.actor i) u) =
      FactorSimplicity.imageActor c.z c.quadratic matrix_relations i
        (c.lastQuotientCoordinates matrix_relations u) := by
    apply Subtype.ext
    exact c.lastQuotientCoordinates_action matrix_relations i u
  exact (congrArg (imageCoordinates c.z c.quadratic) h).trans
    (image_action c.z c.quadratic matrix_relations i _)

/-- The coordinate comparison for the first quotient, before specialization. -/
theorem first_spectrum_of_coordinates (ha : word c.actor = actor)
    (x : standardGroup modelForm) (hx : orderOf x = 7) :
    ((within ((c.flag matrix_relations).stage 0)
      ((c.flag matrix_relations).stage 1)).quotientRepresentation x).charpoly =
        sevenSpectrum K 21 :=
  spectrum_of_coordinates _ c.z c.quadratic c.actor ha
    (firstCoordinates c) (firstCoordinates_action c) x hx

/-- The coordinate comparison for the last quotient, before specialization. -/
theorem last_spectrum_of_coordinates (ha : word c.actor = actor)
    (x : standardGroup modelForm) (hx : orderOf x = 7) :
    ((within ((c.flag matrix_relations).stage 2)
      ((c.flag matrix_relations).stage 3)).quotientRepresentation x).charpoly =
        sevenSpectrum K 21 :=
  spectrum_of_coordinates _ c.z c.quadratic c.actor ha
    (lastCoordinates c) (lastCoordinates_action c) x hx

variable [Finite K] (χ : standardBorel modelForm →* Kˣ)
  (hne : χ ≠ 1) (hcube : ∀ b, χ b ^ 3 = 1)
  (x : standardGroup modelForm) (hx : orderOf x = 7)

include hx

/-- First literal quotient of the completed cubic flag. -/
theorem first_quotient_spectrum :
    ((within ((model_flags K χ hne hcube).stage 0)
      ((model_flags K χ hne hcube).stage 1)).quotientRepresentation x).charpoly =
        sevenSpectrum K 21 := by
  exact first_spectrum_of_coordinates (modelCoordinates χ hne hcube)
    (modelCoordinates_word χ hne hcube) x hx

/-- Last literal quotient of the same completed cubic flag. -/
theorem last_quotient_spectrum :
    ((within ((model_flags K χ hne hcube).stage 2)
      ((model_flags K χ hne hcube).stage 3)).quotientRepresentation x).charpoly =
        sevenSpectrum K 21 := by
  exact last_spectrum_of_coordinates (modelCoordinates χ hne hcube)
    (modelCoordinates_word χ hne hcube) x hx

end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors.Cubic
