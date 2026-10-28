module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitMarking

/-!
# Structural and module assembly from the original orbit source inputs

The normalized non-FF exit and the rank-one module theorem give FF on the
actual Sylow orbit, before identifying that orbit with the chosen seed.
In the moved branch of the proved 3.2.5 trichotomy, the completed doubled
marking then gives precisely the full-normalizer input to 12.1.11. Its
exclusion leaves the two orbit equalities needed for structural 12.2.2.
The separate nonbinary exclusion also supplies the seven module alternatives.

Normalization is independent of every chosen module. The remaining orbit,
rank-one, doubled and nonbinary source implications retain their existing
producers; qt-d-1222-modules and qt-d-1222-source own their final discharge.
These conditional implications preserve the original G,T and hmany, and
do not assert any universal singleton-overgroup theorem.
Source: Aschbacher--Smith, 3.2.5, 6.2.20, 7.0.1, 11.0.1, 12.1.11 and
12.2.2(3), printed pp.580,691,695,759,794--796.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter12.Section01.DoubleNaturalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The source exits exclude the moved seed using the literal FF orbit and
the full normalizer quotient of its constructed doubled marking. -/
theorem ChosenModule.not_markedDoubled_of_orbit_source_inputs
    {L V : Subgroup G} (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hdouble : ∀ n, DoubledBranch T L V n → False) : ¬ D.MarkedDoubled := by
  intro hd
  obtain ⟨n, ⟨B⟩⟩ := D.doubledOrbit_branch h.toHypothesis1221 hd
    (D.orbit_ff_of_normalized_source_and_rankOne h hrank hexit)
  exact hdouble n B

variable
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (normalization : SourceNormalization1222At KnownSimple.IsKnownSimple T)
    (hexit : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) →
      IsFFModule D.sourceOrbitNormalizerRepresentation ∨
        Chapter7.NormalizedSource.OrthogonalMinusAlternative
          D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, 1 < n →
      ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hdouble : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      ChosenModule T L V → ∀ n, DoubledBranch T L V n → False)

include hmany normalization hexit hrank hdouble

/-- The proved 3.2.5 and doubled marking discharge the qualitative FSU
callback in the local structural assembly. All remaining source inputs
refer to the same original component, seed and Sylow subgroup. -/
theorem structural1222At_of_orbit_source_inputs_of_many :
    Structural1222At KnownSimple.IsKnownSimple T := by
  apply structural1222At_of_source_branches normalization
  intro L V h D
  rcases D.source325_of_many h hmany with ⟨_, hU⟩ | ⟨hW, hc, _⟩ | hd
  · exact Or.inl (hU ▸ le_normalizer_componentOrbit V (normalizer (L : Set G)))
  · exact Or.inr ⟨hW ▸ le_normalizer_componentOrbit V (T : Subgroup G), hc⟩
  · exact (D.not_markedDoubled_of_orbit_source_inputs h (hexit L V h D)
      (hrank L V h D) (hdouble L V h D) hd).elim

/-- Assemble both distinct 12.2.2 conclusions. The seven-case result uses
the independent nonbinary exclusion and retains every literal action and
quotient in ModuleAlternatives1222; it is not inferred from structure. -/
theorem source1222At_of_orbit_source_inputs_of_many
    (hnonbinary : ∀ (L V : Subgroup G), Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → D.NonbinaryNaturalInput → False) :
    Structural1222At KnownSimple.IsKnownSimple T ∧
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T := by
  refine ⟨structural1222At_of_orbit_source_inputs_of_many
    hmany normalization hexit hrank hdouble, ?_⟩
  intro L V h D
  exact D.alternatives_of_source_inputs_of_many h hmany (D.source325_of_many h hmany)
    (hexit L V h D) (hrank L V h D) (hnonbinary L V h D) (hdouble L V h D)

end CFSG.Quasithin.Chapter12.Section02
