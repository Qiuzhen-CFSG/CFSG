module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitCover
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.SourceApplications

/-!
# The remaining ambient quotient in the FF doubled branch

The source row, original quotient and compatible natural-plus-dual coordinates
are constructed in DoubledOrbitCover. Only the full ambient normalizer-action
quotient remains explicit here. This boundary applies to the unchanged
SourceApplications consumer and keeps its five earlier-source implications.

The full-quotient premise is still owned by qt-d-1222-ff-doubled-marking. This
conditional assembly does not assert the ambient recognition or complete H.9.
Source: Aschbacher--Smith, H.9, 12.1.11 and 12.2.2, pp.389--390,794--795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The remaining full-normalizer equivalence completes the original branch
using the row and coordinates already constructed from the actual hypotheses. -/
theorem doubledOrbit_branch_of_full
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hff : IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hfull : ∀ n, (n = 4 ∨ n = 5) →
      Nonempty ((L ⧸ pCore 2 L) ≃* LinearGroup n) →
      ∀ he : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G)),
      Nonempty ((normalizer (L : Set G) ⧸ (normalizerAction T L V he).ker) ≃*
        MulAut (LinearGroup n))) : ∃ n, Nonempty (DoubledBranch T L V n) := by
  obtain ⟨n,hn,e,c,hc⟩ := D.doubledOrbit_component_marking h hd hff
  obtain ⟨_,_,_,horbit,_⟩ := hd.2.2
  obtain ⟨ef⟩ := hfull n hn ⟨e⟩ horbit.symm
  exact ⟨n,⟨⟨hn,horbit.symm,e,c,hc,ef⟩⟩⟩

/-- The literal seven-alternative consumer now requires only the ambient
normalizer recognition from this owner, together with its five earlier inputs. -/
theorem alternatives_of_source_inputs_and_doubled_full_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h325 : D.Source325Alternatives)
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hnonbinary : D.NonbinaryNaturalInput → False)
    (hfull : D.MarkedDoubled → IsFFModule D.sourceOrbitNormalizerRepresentation →
      ∀ n, (n = 4 ∨ n = 5) → Nonempty ((L ⧸ pCore 2 L) ≃* LinearGroup n) →
      ∀ he : componentOrbit V (T : Subgroup G) = componentOrbit V (normalizer (L : Set G)),
      Nonempty ((normalizer (L : Set G) ⧸ (normalizerAction T L V he).ker) ≃*
        MulAut (LinearGroup n)))
    (hdouble : ∀ n, DoubledBranch T L V n → False) : ModuleAlternatives1222 D := by
  apply D.alternatives_of_source_inputs_and_doubled_comparison_of_many
    h hmany h325 hexit hrank hnonbinary _ hdouble
  intro hd hff
  exact D.doubledOrbit_branch_of_full h.toHypothesis1221 hd hff (hfull hd hff)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
