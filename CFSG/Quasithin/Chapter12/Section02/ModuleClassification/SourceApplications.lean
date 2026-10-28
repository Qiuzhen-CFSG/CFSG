module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.FFApplications
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.OrbitRankOne
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.OrbitTransport
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Setup

/-!
# Literal source assembly for the seven module alternatives

The normalized source exit and the rank-one exit give FF on the actual
Sylow orbit. A marked FF doubled-orbit comparison is the precise remaining
input to 12.1.11. After its exclusion, the actual 3.2.5 branch identifies
the seed with that orbit. Only then do we transport FF to the chosen space
and apply all corrected B.5 rows.

The source implications and the doubled-orbit comparison remain explicit.
No universal or singleton-overgroup classification is asserted.
Source: Aschbacher--Smith 3.2.5, 6.2.20, 7.0.1, 11.0.1, 12.1.11 and 12.2.2,
printed pp.580,691,695,759--760,794--796.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The retained source branch supplies the seed/orbit equality needed for
FF transport. In particular FF alone is never used to infer that equality. -/
theorem alternatives_of_orbit_source_exits_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False) : ModuleAlternatives1222 D := by
  have hT := (D.structural_of_orbit_equalities_of_many h hmany horbits).1
  have hVW : V = D.sourceOrbit := by
    rw [D.sourceOrbit_eq]
    exact (le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hT)
      (le_componentOrbit V T)).symm
  have hff := (D.chosen_normalizer_ff_iff_orbit_of_eq hVW).mpr
    (D.orbit_ff_of_normalized_source_and_rankOne h hrank hexit)
  exact D.alternatives_of_fullNormalizer_source_exits_of_many
    h hmany horbits hff hrank hnonbinary

/-- The five earlier source implications feed the module conclusion once
the marked FF doubled-orbit comparison has supplied the exact 12.1.11 input. -/
theorem alternatives_of_source_inputs_and_doubled_comparison_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h325 : D.Source325Alternatives)
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (hmark : D.MarkedDoubled → IsFFModule D.sourceOrbitNormalizerRepresentation →
      ∃ n, Nonempty (DoubledBranch T L V n))
    (hdouble : ∀ n, DoubledBranch T L V n → False) : ModuleAlternatives1222 D := by
  apply D.alternatives_of_orbit_source_exits_of_many h hmany _ hexit hrank hnonbinary
  rcases h325 with ⟨_,hU⟩ | ⟨hW,hC,_⟩ | hd
  · exact Or.inl hU
  · exact Or.inr ⟨hW,hC⟩
  · obtain ⟨n,⟨B⟩⟩ := hmark hd
      (D.orbit_ff_of_normalized_source_and_rankOne h hrank hexit)
    exact (hdouble n B).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
