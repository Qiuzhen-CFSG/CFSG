module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.BranchInputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CharacterCoverage
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.InductionConvention
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation

/-!
# Assembly of the SU₃(5) principal-series filtrations

Every character of the actual standard Borel over a characteristic-two field
has cube one. Thus the trivial-character and nontrivial-cubic calculations
cover all principal series, including over coefficient fields without a
nontrivial cube root of unity. Their literal simple-factor filtrations embed
in the common degree set without changing invariant subspaces or quotients.

The proved trivial and cubic calculations discharge both branch premises in
`principal_series_filtrations`. Their field transports and quotient simplicity
proofs retain the original involution and coefficient field.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
p.10; Aschbacher–Smith K.2, printed p.453.
-/

public section
namespace Representation.SU3.FiveSmallModules.Degrees
universe u v

private theorem enlarge_degrees
    {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
    {ρ : Representation K G V} {D E : Set ℕ}
    (h : FactorDegreeFiltration D ρ) (hle : D ⊆ E) : FactorDegreeFiltration E ρ := by
  induction h with
  | zero σ => exact .zero σ
  | step S previous simple degree ih => exact .step S ih simple (hle degree)

/-- The two concrete calculations suffice for all Borel characters. The cubic
premise is discharged by the actual root-and-torus character calculation. -/
theorem principal_series_filtrations_of_branches
    (htrivial : TrivialPrincipalSeriesFiltrations.{u, v})
    (hcubic : CubicPrincipalSeriesFiltrations.{u, v}) :
    PrincipalSeriesFiltrations.{u, v} := by
  intro F _ _ J hF hconj K _ _ _ χ
  by_cases hχ : χ = 1
  · subst χ
    exact enlarge_degrees (htrivial F J hF hconj K) (by
      intro d hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      simp only [principalSeriesDegrees, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop)
  · exact enlarge_degrees
      (hcubic F J hF hconj K χ hχ (borel_character_cube J hF χ)) (by
      intro d hd
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      simp only [principalSeriesDegrees, Set.mem_insert_iff, Set.mem_singleton_iff]
      aesop)

/-- Every principal-series character for the actual SU₃(5) Borel has the
required literal factor-degree filtration. The trivial and nontrivial cubic
calculations are over the original coefficient field and the character
coverage theorem supplies the branch hypotheses. -/
theorem principal_series_filtrations : PrincipalSeriesFiltrations.{0, v} :=
  principal_series_filtrations_of_branches
    trivial_principal_series_filtrations cubic_principal_series_filtrations

end Representation.SU3.FiveSmallModules.Degrees
