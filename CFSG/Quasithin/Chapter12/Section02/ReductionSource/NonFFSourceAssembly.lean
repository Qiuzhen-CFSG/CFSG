module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesDefs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuComplete

/-!+# Conditional normalized source 7.0.1 on the chosen orbit

Source 3.2.5 distinguishes the original seed from its Sylow orbit. In the
non-FF branch, the marked doubled exclusion forces these to agree. The
multiple-overgroup hypothesis then supplies the standing guard and the
Chapter K hypotheses for the unchanged orbit representation. The completed
non-Mathieu argument gives the marked minus orthogonal action; the Mathieu
source implication gives a concrete ambient J4 isomorphism.

The inputs are the literal source 3.2.5 alternatives and the exact outputs
of `qt-d-1222-nonff-doubled` and `qt-d-1222-nonff-mathieu`. Neither branch
output is asserted here. Final discharge belongs to `qt-d-1222-modules`
and `qt-d-1222-source`. In particular this is a conditional normalized
source theorem, not an unconditional classification or a statement about
the nonnormal component cases.

Source: Aschbacher--Smith, 3.2.5, 7.0.1 and the proof of 12.2.2,
printed pp.580--581, 695--696 and 795; `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The three normalized source alternatives on the literal full orbit.
The doubled input concerns the marked 3.2.5 output, not an assumed
seed/orbit equality or a classification of the whole orbit. -/
theorem sourceOrbit_alternatives_of_source_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h325 : D.Source325Alternatives)
    (hdoubled : D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model)) :
    Alternatives G D.orbitRepresentation D.orbitComponent := by
  classical
  by_cases hff : IsFFModule D.sourceOrbitNormalizerRepresentation
  · exact Or.inl hff
  have hV : V = D.sourceOrbit := by
    rcases h325 with ⟨hW, _⟩ | ⟨hW, _, _⟩ | hd
    · exact hW.symm.trans D.sourceOrbit_eq.symm
    · exact hW.symm.trans D.sourceOrbit_eq.symm
    · exact (hdoubled hd hff).elim
  have hs := D.sourceOrbit_chapterK_of_many h hmany hff hV
  by_cases hm : HasMathieuCentralQuotient D.orbitComponent
  · exact Or.inr (Or.inr (hmathieu hV hs hm hff))
  · exact Or.inr (Or.inl
      (D.sourceOrbit_orthogonal_of_nonMathieu_of_many h hmany hV hs hm hff))

/-- Exclude the concrete J4 alternative using the original ambient
hypothesis. The orthogonal marking is still on the original component and
orbit, with exponent greater than one. -/
theorem sourceOrbit_ff_or_orthogonal_of_source_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h325 : D.Source325Alternatives)
    (hdoubled : D.MarkedDoubled →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model)) :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent := by
  have halt : Alternatives G D.orbitRepresentation D.orbitComponent :=
    D.sourceOrbit_alternatives_of_source_inputs_of_many h hmany h325 hdoubled hmathieu
  exact halt.imp_right (fun hrest => hrest.resolve_right h.no_J4)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
