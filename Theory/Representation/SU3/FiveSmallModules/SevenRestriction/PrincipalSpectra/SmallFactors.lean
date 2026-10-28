module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Inputs
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Trivial
public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.PrincipalSpectra.SmallFactors.Cubic
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FieldTransport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.PairTransport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CharacterCoverage

/-!
# Assembly of the small simple-factor seven-spectra

An isomorphism of the matrix fields preserves fifth-power conjugation and the
literal standard Borel. The induced-module equivalence preserves the original
coefficient field and transports each simple quotient and its characteristic
polynomial. Character coverage reduces to the untwisted and nontrivial cubic
canonical calculations. The filtration theorem then covers every irreducible
subquotient, without absolute irreducibility or a central-kernel assumption.

The final theorem supplies both canonical spectral filtrations from their
checked matrix certificates and literal quotient coordinates. It covers the
trivial character and both nontrivial cubic characters over the original
coefficient field, with no remaining spectral-filtration premise.

Source application: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public noncomputable section
open BenderSuzuki.MatrixGroups
namespace Representation.SU3.FiveSmallModules.SevenRestriction
open Degrees Degrees.CubicCalculation SmallFactors
universe u v
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The two canonical calculations give a spectral filtration over every
permitted matrix field, with the original coefficient field unchanged. -/
theorem principal_series_spectral_filtration_of_model_filtrations
    (ht : TrivialModelSpectralFiltrations.{v})
    (hc : CubicModelSpectralFiltrations.{v})
    (F : Type u) [Field F] [Finite F] (J : HermitianForm 3 F)
    (hF : Nat.card F = 5 ^ 2) (hconj : ∀ a, J.conj a = a ^ 5)
    (K : Type v) [Field K] [Finite K] [CharP K 2]
    (χ : standardBorel J →* Kˣ) (x : standardGroup J) (hx : orderOf x = 7) :
    FactorPolynomialFiltration (SmallSpectrum K) x
      (ind (standardBorel J).subtype (scalarCharacter χ)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let : Fintype MatrixField := Fintype.ofFinite MatrixField
  let e : MatrixField ≃+* F := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
    exact GaloisField.card 5 2 (by decide))
  have hconj' (a : MatrixField) : e (modelForm.conj a) = J.conj (e a) := by
    rw [modelForm_conj, hconj, map_pow]
  let eg := standardFieldEquiv modelForm J e hconj'
  let eb := standardBorelFieldEquiv modelForm J e hconj'
  let ψ : standardBorel modelForm →* Kˣ := χ.comp eb.toMonoidHom
  have hcube (b : standardBorel modelForm) : ψ b ^ 3 = 1 :=
    borel_character_cube J hF χ (eb b)
  have hx' : orderOf (eg.symm x) = 7 := by
    rw [eg.symm.orderOf_eq, hx]
  have hm : FactorPolynomialFiltration (SmallSpectrum K) (eg.symm x)
      (ind (standardBorel modelForm).subtype (scalarCharacter ψ)) := by
    by_cases hψ : ψ = 1
    · rw [hψ]
      exact ht K (eg.symm x) hx'
    · exact hc K ψ hψ hcube (eg.symm x) hx'
  have hb (b : standardBorel modelForm) : eg b = eb b :=
    (standardBorelFieldEquiv_coe modelForm J e hconj' b).symm
  have hχ (b : standardBorel modelForm) : χ (eb b) = ψ b := rfl
  have h := hm.transport eg.toMonoidHom eg.surjective
    (ind (standardBorel J).subtype (scalarCharacter χ))
    (inductionPairEquiv _ _ eg eb hb ψ χ hχ)
    (inductionPairEquiv_intertwines _ _ eg eb hb ψ χ hχ)
  simpa only [MulEquiv.coe_toMonoidHom,
    eg.apply_symm_apply] using h

/-- Actual consumer of the two canonical spectral calculations. Restricting
the filtration to the specified subspace and following its simple quotient
proves the published small-factor contract. Both calculation inputs remain
explicit here; this theorem does not assert either certificate. -/
theorem principal_series_small_factor_seven_spectra_of_model_filtrations
    (ht : TrivialModelSpectralFiltrations.{v})
    (hc : CubicModelSpectralFiltrations.{v}) :
    PrincipalSeriesSmallFactorSevenSpectra.{0, v} := by
  intro F _ _ J hF hconj K _ _ _ χ S T hirr hd x hx
  have h := principal_series_spectral_filtration_of_model_filtrations
    ht hc F J hF hconj K χ x hx
  exact h.subquotient_spectrum S T hirr hd

/-- Every small irreducible subquotient of the literal principal series has
the stated spectrum at every group element of order seven. The canonical
trivial and cubic calculations discharge both inputs of the transport and
subquotient argument. -/
theorem principal_series_small_factor_seven_spectra :
    PrincipalSeriesSmallFactorSevenSpectra.{0, v} :=
  principal_series_small_factor_seven_spectra_of_model_filtrations
    trivial_model_spectral_filtrations cubic_model_spectral_filtrations

end Representation.SU3.FiveSmallModules.SevenRestriction
