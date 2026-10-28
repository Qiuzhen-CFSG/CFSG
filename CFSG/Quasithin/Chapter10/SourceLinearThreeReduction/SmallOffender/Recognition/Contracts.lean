module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.Recognition.Index

/-!
# Independent source obligations for small-offender recognition

The model step selects a contained full module and either marks a surviving
natural action or supplies the numerical bounds of a larger row of 10.1.1.
Those bounds concern the full literal local automizer, not just its component.
The geometric step proves normalization and the uniform fixed-space identity
(*) of 10.2.12, assuming only crossed centralization and fixed quotient size
greater than eight. It does not assume the numerical moduleA bound.

These definitions specify outstanding obligations. The conditional assembly
in `Recognition.Source` combines them; it does not establish either source
input. Minimality transports the original offender to a contained reselection.

Source: Aschbacher--Smith, 10.1.1--2 and 10.2.12, pp.741--742,754--755;
the model selection also uses genuine 3.2.6 and 7.0.1.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Numerical data sufficient to exclude a nonsurviving source row.
All actions and indices retain the original moved factor and maximal local. -/
structure LargeModuleBounds (D : FundamentalSetup KnownSimple.IsKnownSimple T L) where
  dimension : ℕ
  dimension_gt : 3 < dimension
  fixed_size : 2 ^ dimension ≤ (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆
  rank : ℕ
  automizer_rank : primeRank 2 (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal) ≤ rank
  rank_small : 2 ^ rank < Nat.card (⁅D.fullModule,L⁆ : Subgroup G)
  parameter_small : let _ := source_full_moved_elementary D
    moduleA ((automizerRepresentation ⁅D.fullModule,L⁆).comp
      (inducedAutomizer ⁅D.fullModule,L⁆ D.maximalLocal).subtype) <
        ((dimension-2 : ℕ) : ℕ∞)
  crossed : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)

/-- The exact normalization and fixed-space geometry needed before the
numerical contradiction. There is no conclusion about module models here. -/
def FixedSpaceGeometry (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∀ x ∉ D.maximalLocal,
    subgroupCorank (D.fullModule.map (MulAut.conj x).toMonoidHom)
      (D.fullModule.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal) ≤ 2 →
    let W := ⁅D.fullModule,L⁆
    let A := W.map (MulAut.conj x).toMonoidHom ⊓ D.maximalLocal
    A ≤ normalizer (W : Set G) ∧
      ∀ a ∈ A, a ∉ centralizer (L.map (MulAut.conj x).toMonoidHom : Set G) →
        W ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)

/-- The 10.1.1 source selection and its model-specific numerical bounds.
This is weaker than recognition: the large-module alternative is still open. -/
def ModelBoundsAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
    Configuration T D g →
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) ∨
    ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.fullModule ≤ D.fullModule ∧
        (Nonempty (SourceLinearThreeGeometry T E) ∨ Nonempty (LargeModuleBounds E))

/-- The independent geometric portion of 10.2.12 through (*), using the
earlier 10.2.9--10 point and intersection arguments. No moduleA bound or
small-offender recognition is an input. -/
def GeometryAt (T : Sylow 2 G) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
    D.IsMinimalFullModule →
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) →
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) →
    (∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 → centralizer ({v} : Set G) ≤ D.maximalLocal) →
    (∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
      (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) →
    8 < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆ →
    FixedSpaceGeometry D

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
