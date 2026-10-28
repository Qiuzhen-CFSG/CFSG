module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.CartanEndpoints
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry

/-!
# Chosen-flag applications of the component comparison reductions

The comparison uses exactly the field-flag pullbacks, solvable residuals,
and point from ComponentGeometry.ofFlag. Source 11.4.1(1) supplies fixed-space
vanishing from the earlier linear case and the full Proposition1132At
implication. It is not added as a new source hypothesis.

The initial comparison and the conditional Frattini/Cartan endpoint below
are proved. They do not prove full 11.4.2: the proper-overcomponent,
nonquasisimple, and quasisimple FF exclusions must still be supplied.
Source: Aschbacher--Smith, 11.4.2, printed pp.776--777.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

/-- The initial comparison on the actual marked field flag. The fixed-space
premise is discharged here by 11.4.1(1) from the earlier source implications. -/
theorem ofFlag_initial_comparison
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J) :
    let E := ofFlag S f X z H
    E.K ≤ E.Kz ∧
      (E.Kz ≠ E.K → E.K < E.Kz ∧ E.L₁ < E.Kz ∧ ¬ E.Kz ≤ E.G₁) ∧
      ∃ Kplus ∈ Chapter1.LStar G (T : Subgroup G), E.Kz ≤ Kplus := by
  have hf := (fixed_and_transitive D S _ hlinear h1132).1
  exact ⟨h.line_component_le_point hf, h.strict_comparison hf,
    h.exists_maximal_overcomponent⟩

/-- The actual chosen-module application of the nonquasisimple Cartan
endpoint. This discharges fixed-space vanishing, but not the displayed
Frattini factorization, radical-centralization or Cartan-invariance premises. -/
theorem ofFlag_eq_of_fitting_normalizer_split
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hF : fittingPreimage (ofFlag S f X z H) ≤
      centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hsplit : (ofFlag S f X z H).Kz =
      fittingPreimage (ofFlag S f X z H) ⊔ normalizerResidual (ofFlag S f X z H))
    (hX : X ≤ normalizer (normalizerResidual (ofFlag S f X z H) : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K :=
  eq_of_fitting_normalizer_split h (fixed_and_transitive D S _ hlinear h1132).1
    hline hF hsplit hX

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison
