module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseSetup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Interface
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.KernelMembership

/-!
# Pointwise conjugate exclusion in the literal presentation

The finite Boolean implication is proved in `Boolean`: the selected equations
force the literal envelope pattern or an eleven-dimensional kernel pattern.
This module connects that implication to the actual presented group.
`coordinateTests_of_card` in `GroupTests` extracts the equations from the square
and pairwise conjugate tests using normal-form uniqueness. The independent
kernel-membership calculation realizes the kernel pattern in the original
eleven-word subgroup. The envelope membership is proved here directly.

`pointwiseExclusion_of_card` discharges both calculation contracts with only
the presentation cardinality hypothesis. The existing
`envelope_bound_of_pointwise` consumes it for normal elementary subgroups;
the parent localization module owns the subsequent interval assembly.
Source context: Aschbacher–Smith A.3.12, pp.47–48; see `source/README.md`.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation
open PointwiseCalculation

/-- The envelope pattern uses precisely the ten original envelope generators. -/
theorem envelopePattern_mem (b : Boolean.Bits) (h : Boolean.EnvelopePattern b) :
    Symbolic.boolValue b ∈ envelope := by
  have hs : ∀ i : Fin 21, b i = true →
      i ∈ ([9,11,13,14,15,16,17,18,19,20] : List (Fin 21)) := by
    intro i hi
    fin_cases i <;> simp_all [Boolean.EnvelopePattern]
  unfold Symbolic.boolValue
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  split_ifs with hi
  · have hw : [i] ∈ envelopeWords :=
      (by decide +kernel : ∀ i : Fin 21,
        i ∈ ([9,11,13,14,15,16,17,18,19,20] : List (Fin 21)) →
          [i] ∈ envelopeWords) i (hs i hi)
    have hm := (wordSubgroup_le_iff generator envelopeWords envelope).mp le_rfl [i] hw
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hm
  · exact envelope.one_mem

/-- Final pointwise assembly once the two independent word calculations are supplied. -/
theorem pointwiseExclusion_of_coordinate_tests
    (ht : CoordinateTests) (hk : KernelPatternMembership) : PointwiseExclusion := by
  intro x hx hc
  obtain ⟨b, rfl⟩ := Symbolic.boolValue_surjective x
  rcases Boolean.pattern_of_tests b (ht b hx hc) with hb | hb
  · exact Or.inl (hk b hb)
  · exact Or.inr (envelopePattern_mem b hb)

/-- Every square-one element whose identity and generator conjugates commute
pairwise lies in the original kernel or envelope. Full presentation cardinality
is the sole premise, used for uniqueness of ascending normal forms. -/
theorem pointwiseExclusion_of_card (hcard : Nat.card Carrier = 2 ^ 21) :
    PointwiseExclusion :=
  pointwiseExclusion_of_coordinate_tests (coordinateTests_of_card hcard)
    kernelPatternMembership

/-- The g12 diagnostic: its g0 and g2 conjugates fail the actual pairwise test. -/
theorem generator_twelve_not_pairwise (hcard : Nat.card Carrier = 2 ^ 21) :
    ¬ PairwiseConjugateCommutation (generator 12) := by
  intro h
  have h0 : conjugateTest (generator 12) (some 0) = Profiles.wordValue [12,14,20] := by
    have he := Symbolic.word_eq_of_collect 7
      (Profiles.inverseGeneratorWord 0 ++ [12,0]) [12,14,20] (by decide +kernel)
    simpa only [conjugateTest, Profiles.wordValue_append,
      Profiles.wordValue_inverseGeneratorWord, Profiles.wordValue_cons,
      Profiles.wordValue_nil, mul_one, mul_assoc] using he
  have h2 : conjugateTest (generator 12) (some 2) = Profiles.wordValue [12,13,18,20] := by
    have he := Symbolic.word_eq_of_collect 4
      (Profiles.inverseGeneratorWord 2 ++ [12,2]) [12,13,18,20] (by decide +kernel)
    simpa only [conjugateTest, Profiles.wordValue_append,
      Profiles.wordValue_inverseGeneratorWord, Profiles.wordValue_cons,
      Profiles.wordValue_nil, mul_one, mul_assoc] using he
  have h12 := Symbolic.word_eq_of_collect 6
    ([12,14,20] ++ [12,13,18,20]) [13,14,18,20] (by decide +kernel)
  have h21 := Symbolic.word_eq_of_collect 7
    ([12,13,18,20] ++ [12,14,20]) [13,14,18] (by decide +kernel)
  rw [Profiles.wordValue_append] at h12 h21
  have hc := (h (some 0) (some 2)).eq
  rw [h0, h2, h12, h21] at hc
  change normalForm 1335296 = normalForm 286720 at hc
  exact (by decide : (1335296 : Fin (2 ^ 21)) ≠ 286720)
    ((normalForm_bijective_of_card hcard).injective hc)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
