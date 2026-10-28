module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Cubic.Quotients
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Inputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FactorSimplicity

/-!
# Spectral filtrations for both cubic SU₃(5) principal series

The actual image/kernel flag has simple literal quotients of dimensions
21, 84, 21. Both degree-21 quotients have characteristic polynomial
(X⁷ − 1)³ at every order-seven actor, by their checked common coordinates.
The degree-84 quotient needs no spectral computation. Assembling this flag
keeps every original finite characteristic-two field and both nontrivial
cubic Borel characters, with no additional embedding or splitting premise.
Source application: Guralnick–Malle, Proposition 4.3, pp.10–11;
Aschbacher–Smith K.2, printed p.453.
-/

public section
namespace Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors
open Degrees.CubicCalculation
universe v

open G2DerivedPermutationFiltration.VertexCoordinates.CoordinateFiltrations

/-- Assemble the spectra without unfolding the concrete flag during elaboration. -/
private theorem of_simple_flag {K G V : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {ρ : Representation K G V} (s : ThreeStepFlag ρ) (hs : s.Simple) (x : G)
    (hfirst : ((within (s.stage 0) (s.stage 1)).quotientRepresentation x).charpoly =
      sevenSpectrum K 21)
    (hlast : ((within (s.stage 2) (s.stage 3)).quotientRepresentation x).charpoly =
      sevenSpectrum K 21) : FactorPolynomialFiltration (SmallSpectrum K) x ρ := by
  apply FactorPolynomialFiltration.of_flag 3 s.stage s.zero s.top s.nested hs
  intro m hm
  unfold SmallSpectrum
  rw [s.degree m hm]
  by_cases hm1 : m = 1
  · simp only [hm1, ↓reduceIte]
    omega
  · rw [if_neg hm1]
    intro _
    refine Or.inr ⟨Or.inr rfl, ?_⟩
    have hcases : m = 0 ∨ m = 2 := by omega
    rcases hcases with rfl | rfl
    · exact hfirst
    · exact hlast

attribute [local irreducible] model_flags ModelFlag.modelCoordinates
  ModelFlag.generatorMatrix ModelFlag.nilpotentMatrix

/-- The spectral filtration of the literal canonical cubic principal series. -/
theorem cubic_model_spectral_filtrations : CubicModelSpectralFiltrations.{v} := by
  intro K _ _ _ χ hne hcube x hx
  exact of_simple_flag (model_flags K χ hne hcube)
    (model_flags_simple K χ hne hcube) x
    (Cubic.first_quotient_spectrum χ hne hcube x hx)
    (Cubic.last_quotient_spectrum χ hne hcube x hx)

end Representation.SU3.FiveSmallModules.SevenRestriction.SmallFactors
