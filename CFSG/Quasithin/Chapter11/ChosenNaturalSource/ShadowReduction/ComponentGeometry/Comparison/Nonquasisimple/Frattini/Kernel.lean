module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Kernel.Source

/-!
# The original Frattini product and residual quotient from the elementary row

The literal elementary extension identifies the Fitting kernel and supplies
the SL₂(p) model required by the existing Frattini product proof. The new
kernel calculation identifies the actual residual projection kernel with
O₂ of that residual. The resulting equivalence retains the original
inclusion and quotient maps, as recorded by its public representative equation.

These chosen-flag applications discharge the former kernel and separate
Fitting-model premises. The complete-catalogue reduction, original radical
centralization and Cartan normalization remain obligations of the consolidated
owner qt-d-1222-comparison-nonquasisimple; this does not complete 11.4.2.
Source: Aschbacher--Smith, 11.4.2, printed p.777.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V}

private theorem fitting_model_of_exceptional_extension
    {A : Type*} [Group A] [Finite A] {p : ℕ} (hp : Source.ExceptionalPrime p)
    (he : HasExtension (A ⧸ pCore 2 A) (ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) : Source.IsSL (A ⧸ twoFittingCore A) 2 p := by
  let : Fact p.Prime := ⟨hp.1⟩
  have hp3 : 3 < p := by
    have hpl := hp.1.two_le
    have h5 := hp.2.1
    omega
  exact twoFitting_sl2_of_elementary_extension hp3 he
/-- The residual kernel is exactly its original two-core, using the proved
Frattini product and the elementary extension calculation. -/
theorem ofFlag_residualProjection_ker_eq_core (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (he : Chapter1.Section02.LocalModels.HasExtension
      ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) :
    (residualProjection (ofFlag S f X z H)).ker =
      pCore 2 (normalizerResidual (ofFlag S f X z H)) :=
  residualProjection_ker_eq_core
    (ofFlag_fitting_factorization_of_model S f X z H h hA hseed hp (fitting_model_of_exceptional_extension hp he))
    (Kernel.ofFlag_residualProjection_kernel_isPGroup S f X z H h hA hseed hp hn he)

/-- The exact inclusion-induced quotient equivalence. Its kernel and Frattini
product are proved from the displayed source models. -/
def ofFlag_residualQuotientEquiv (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (he : Chapter1.Section02.LocalModels.HasExtension
      ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) :
    (normalizerResidual (ofFlag S f X z H) ⧸ pCore 2 (normalizerResidual (ofFlag S f X z H))) ≃*
      ((ofFlag S f X z H).Kz ⧸ solvableRadical (ofFlag S f X z H).Kz) :=
  residualQuotientEquiv
    (ofFlag_fitting_factorization_of_model S f X z H h hA hseed hp (fitting_model_of_exceptional_extension hp he))
    (Kernel.ofFlag_residualProjection_kernel_isPGroup S f X z H h hA hseed hp hn he)

/-- The chosen-flag equivalence commutes with the original projections,
including the original inclusion of the residual in Kz. -/
theorem ofFlag_residualQuotientEquiv_mk (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (he : Chapter1.Section02.LocalModels.HasExtension
      ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p))
    (x : normalizerResidual (ofFlag S f X z H)) :
    ofFlag_residualQuotientEquiv S f X z H h hA hseed hp hn he
      (QuotientGroup.mk' (pCore 2 (normalizerResidual (ofFlag S f X z H))) x) =
        residualProjection (ofFlag S f X z H) x :=
  residualQuotientEquiv_mk _ _ x

/-- The actual normalizer residual has the required PSL₂(p) two-core
quotient, with no kernel, Sylow or Frattini product hypothesis. -/
theorem ofFlag_residual_psl_of_extension (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (he : Chapter1.Section02.LocalModels.HasExtension
      ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (Chapter1.Section02.LocalModels.ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) :
    ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
      pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p :=
  ofFlag_residual_psl_of_fitting_model_and_kernel S f X z H h hA hseed hp (fitting_model_of_exceptional_extension hp he)
    (Kernel.ofFlag_residualProjection_kernel_isPGroup S f X z H h hA hseed hp hn he)

/-- The elementary row supplies the literal Frattini factorization, with
its Fitting-quotient model derived from the displayed extension. -/
theorem ofFlag_fitting_factorization_of_extension (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (he : HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
      (ElementaryModel p 2) (fun Q _ => Source.IsSL Q 2 p)) :
    (ofFlag S f X z H).Kz = fittingPreimage (ofFlag S f X z H) ⊔
      normalizerResidual (ofFlag S f X z H) :=
  ofFlag_fitting_factorization_of_model S f X z H h hA hseed hp
    (fitting_model_of_exceptional_extension hp he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
