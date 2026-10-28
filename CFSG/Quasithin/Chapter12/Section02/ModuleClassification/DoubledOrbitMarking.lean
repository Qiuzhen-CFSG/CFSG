module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitApplications

/-!
# The complete FF doubled-orbit marking and its Chapter 12 consumer

The actual FF and MarkedDoubled hypotheses select the nonhomogeneous B.5.1
natural-plus-dual row. Cover recovery identifies the original L/O₂(L) and
supplies coordinates on the original T-orbit, with its literal conjugation
formula. The marked element t moves the seed and lies in N_G(L). Together
with the trivial binary centralizer, it supplies the full normalizer-action
quotient from DoubledOrbitNormalizer.

Thus every field of the unchanged DoubledBranch is constructed, with no
ambient H.9 model or normalizer-recognition callback. The final theorem
applies the existing seven-alternative consumer. Its five earlier-source
inputs (3.2.5, the non-FF exit, rank-one recognition, nonbinary exclusion,
and the doubled-branch contradiction) remain with their existing owners;
qt-d-1222-modules owns their final assembly.

Source: Aschbacher--Smith, B.5.1(3), H.9, 12.1.11 and 12.2.2,
printed pp.99,389--390,794--795. This is the FF doubled marking, not the
separate 12.1.11 exclusion or the opposite non-FF branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open BinaryLinear.OuterCyclic BinaryNaturalDual
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The FF marked doubled orbit has the complete literal natural-plus-dual
marking, including its full normalizer-action quotient. -/
theorem doubledOrbit_branch
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hff : IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ∃ n, Nonempty (DoubledBranch T L V n) := by
  obtain ⟨n,hn,e,c,hc⟩ := D.doubledOrbit_component_marking h hd hff
  obtain ⟨t,ht,htV,horbit,_⟩ := hd.2.2
  obtain ⟨ef⟩ := ModuleClassification.DoubledOrbit.normalizer_full_of_marking
    L T V horbit.symm e c hc hn D.normalizes
    ⟨⟨t,D.sylow_normalizes_component ht⟩,htV⟩
  exact ⟨n,⟨⟨hn,horbit.symm,e,c,hc,ef⟩⟩⟩

/-- The seven-alternative consumer with the FF doubled marking discharged.
The five independent earlier-source implications remain with their owners. -/
theorem alternatives_of_source_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h325 : D.Source325Alternatives)
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (hdouble : ∀ n, DoubledBranch T L V n → False) : ModuleAlternatives1222 D := by
  apply D.alternatives_of_source_inputs_and_doubled_comparison_of_many
    h hmany h325 hexit hrank hnonbinary _ hdouble
  exact fun hd hff => D.doubledOrbit_branch h.toHypothesis1221 hd hff
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
