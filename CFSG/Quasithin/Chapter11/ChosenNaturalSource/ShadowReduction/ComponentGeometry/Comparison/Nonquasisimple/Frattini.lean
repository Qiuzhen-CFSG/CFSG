module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Quotient
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry

/-!
# Chosen-flag consumers of the nonquasisimple Frattini argument

Fitting centralization excludes the first source alternative directly.
For the exceptional SL₂ alternative, the proved factorization supplies the
Cartan endpoint without a separate radical, Sylow or product assumption.
The complete-catalogue reduction producing that alternative and the
two-group kernel calculation remain separate obligations. In particular,
these conditional consumers do not assert completion of 11.4.2.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- Centralization alone excludes the first nonquasisimple alternative.
The canonical-star producer supplies this centralization independently. -/
theorem not_fitting_seed_split_of_centralizes (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hF : fittingPreimage E ≤ centralizer (E.V₁ : Set G)) :
    E.Kz ≠ fittingPreimage E ⊔ E.L₁ := by
  intro he
  apply hne
  apply (h.eq_iff_point_centralizes_line hf).mpr
  rw [he]
  exact sup_le hF h.seed_centralizes

/-- Actual consumer of the proved Frattini product. The earlier 11.4.1(1)
premises and independently produced Cartan normalization remain explicit. -/
theorem ofFlag_eq_of_fitting_model_and_cartan (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (c.binarySubspace (f.space 0)) J →
      Proposition1132At D S (c.binarySubspace (f.space 0)) J)
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hm : Source.IsSL ((ofFlag S f X z H).Kz ⧸ twoFittingCore (ofFlag S f X z H).Kz) 2 p)
    (hF : fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hline : (ofFlag S f X z H).V₁ = ⁅zpowers z, X⁆)
    (hX : X ≤ normalizer (normalizerResidual (ofFlag S f X z H) : Set G)) :
    (ofFlag S f X z H).Kz = (ofFlag S f X z H).K :=
  eq_of_fitting_normalizer_split h (fixed_and_transitive D S _ hlinear h1132).1
    hline hF (ofFlag_fitting_factorization_of_model S f X z H h hA hseed hp hm) hX

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
