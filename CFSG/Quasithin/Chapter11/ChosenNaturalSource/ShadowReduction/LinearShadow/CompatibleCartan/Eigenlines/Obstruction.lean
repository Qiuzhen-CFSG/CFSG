module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Nonzero
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Eigenlines.Structures
/-!
# Applying the commutator obstruction to the source complements

The existing obstruction consumes the three field subgroups constructed
by Source and Canonical. The source complement identities discharge its
nonvanishing, centrality and normalization requirements here. Only the two
Cartan scalar families and terminal weights remain explicit; this theorem
does not assert that they have been constructed from the source geometry.
Their construction and discharge remain with the eigenline assembly.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 11.3.9 and
the final paragraph of Proposition 11.3.2, printed p.775.
-/

open Subgroup Representation
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
open CFSG.Quasithin.Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {P I X : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]
    [Module S.field.Carrier (Additive P)] [Module S.field.Carrier (Additive V)]

/-- Apply the proved source commutator construction with the literal ambient scalars. -/
theorem false_of_source_complements
    (hPV : P ⊓ V = f.Vi 1)
    (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (hproper : P ⊓ f.Ri 0 < P)
    (hP : P = (f.Li 1).pCoreIn 2) (hVY : V ≤ f.Li 1 ⊔ I)
    (hYP : f.Li 1 ⊔ I ≤ normalizer (P : Set G))
    (U₁ : Submodule S.field.Carrier (Additive V))
    (U₂ C : Submodule S.field.Carrier (Additive P))
    (hC : ambientSubgroup C = ⁅ambientSubgroup U₁, ambientSubgroup U₂⁆)
    (hs₁ : f.Vi 1 ⊔ ambientSubgroup U₁ = V)
    (hs₂ : (P ⊓ f.Ri 0) ⊔ ambientSubgroup U₂ = P)
    (hn₁ : X ≤ normalizer (ambientSubgroup U₁ : Set G))
    (hn₂ : X ≤ normalizer (ambientSubgroup U₂ : Set G)) :
    letI := subgroupFieldModule U₁ rfl
    letI := subgroupFieldModule U₂ rfl
    letI := subgroupFieldModule C rfl
    (∀ a : S.field.Carrier, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation (ambientSubgroup U₁) x a ∧
      ScalarConjugation (ambientSubgroup U₂) x (1 : S.field.Carrier) ∧
      ScalarConjugation (ambientSubgroup C) x a) →
    (∀ a : S.field.Carrier, a ≠ 0 → ∃ x ∈ X,
      ScalarConjugation (ambientSubgroup U₁) x (1 : S.field.Carrier) ∧
      ScalarConjugation (ambientSubgroup U₂) x a ∧
      ScalarConjugation (ambientSubgroup C) x a) →
    ∀ (a : S.field.Carrier), a ≠ 0 → orderOf a = 2 ^ S.field.degree - 1 →
    ∀ y : X,
      ScalarConjugation (ambientSubgroup U₁) (y : G) (a ^ 2) →
      ScalarConjugation (ambientSubgroup U₂) (y : G) a →
      ScalarConjugation (ambientSubgroup C) (y : G) a⁻¹ → False := by
  let := subgroupFieldModule U₁ rfl
  let := subgroupFieldModule U₂ rfl
  let := subgroupFieldModule C rfl
  intro hleft hright a ha horder y hy₁ hy₂ hy₃
  have hc := source_complement_commutator D S f hPV hfixed hproper hP hVY hYP hs₁ hs₂ hn₁ hn₂
  apply false_of_cartan_commutator (ambientSubgroup U₁) (ambientSubgroup U₂)
    (ambientSubgroup C) X hC.symm (hC ▸ hc.1) (hC ▸ hc.2.2.1)
    hn₁ hn₂ (hC ▸ hc.2.2.2) hleft hright S.nonbinary ha horder y hy₁ hy₂ hy₃
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
