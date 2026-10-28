module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Numerical
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Independent steps of the original small-offender argument

The model-selection step of 10.2.12 leaves the natural linear-three row or
an actual SL₂(4) quotient. The separate corank-one step treats the literal
natural linear-three geometry, including its possible central extension.
Both steps keep the original minimum offender and point-centralizer data.
They can be proved independently: the second takes the natural geometry
explicitly. These are obligations, not source theorems. `SmallOffender.Source`
owns their final assembly and the actual SL₂(4) = A₅ exclusion.

Source: Aschbacher--Smith, 10.1.1--2 and 10.2.12, printed pp.741--742,
754--755. The corank-one branch also uses 10.2.10--11 on pp.753--754.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender
open Chapter3.Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The actual small-offender hypotheses, with no module model or lower
bound on the weak-closure parameter included. -/
structure Configuration {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G) : Prop where
  many : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard
  minimal : D.IsMinimalFullModule
  nonnormal : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)
  notA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  pointCentralizers : ∀ v ∈ ⁅D.fullModule,L⁆, v ≠ 1 →
    centralizer ({v} : Set G) ≤ D.maximalLocal
  outside : g ∉ D.maximalLocal
  noncommuting : ⁅D.fullModule,D.fullModule.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥
  attained : globalW D.fullModule (T : Subgroup G) =
    (subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) : ℕ∞)
  small : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
    (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 2

/-- Model recognition before the field-four alternative is excluded.
Full-module containment is enough: minimality will give equality. -/
def RecognitionAt : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
    Configuration T D g →
    Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) ∨
    ∃ E : FundamentalSetup KnownSimple.IsKnownSimple T L,
      E.fullModule ≤ D.fullModule ∧ Nonempty (SourceLinearThreeGeometry T E)

/-- The remaining natural linear-three contradiction, with the model as an
explicit independent input. It includes both zero and one corank. -/
def NaturalSmallCorankExclusionAt : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (g : G),
    Configuration T D g → SourceLinearThreeGeometry T D →
    subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ 1 → False

end CFSG.Quasithin.Chapter10.SmallOffender
