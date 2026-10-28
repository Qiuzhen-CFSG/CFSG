module
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOne
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneFixedSpace

/-!
# Suzuki fixed-space bounds on the literal chosen orbit

The ambient automizer acts faithfully inside the full linear normalizer of
the marked component. The coordinates retain every ambient conjugation
operator. Suzuki involution innerness and binary Schur's lemma then give
fixed codimension 2(2m+1) for every nontrivial elementary automizer subgroup,
and hence the local m-column of Table 7.2.1. Recognition uses the specified
central quotient equivalence and the original orbit representation.

These are local bounds; the global w/r estimates still require the ambient
arguments of Sections 7.3--7.4. The private import continues Actor.Orbit only
to verify its original component homomorphism's conjugation formula.
Source: Aschbacher--Smith, K.3.6 and Table 7.2.1, printed pp.457,698.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full action marking, beyond its consequence for the automizer rank. -/
theorem sourceOrbit_automizer_marking
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    ∃ j : ChapterE.Automizer D.sourceOrbit →*
        linearNormalizer (D.orbitRepresentation.comp D.orbitComponent.subtype),
      Function.Injective j ∧ ∀ a v,
        D.sourceOrbitCoordinates
          (normalizerRepresentation (D.orbitRepresentation.comp D.orbitComponent.subtype) (j a) v) =
        ChapterE.automizerRepresentation D.sourceOrbit a (D.sourceOrbitCoordinates v) := by
  apply Chapter7.NormalizedSource.automizer_marked_normalizer
    D.sourceOrbit L D.sourceOrbit_component_normalizes (D.sourceOrbit_normalizer_le h)
    (D.orbitRepresentation.comp D.orbitComponent.subtype)
    D.orbitComponentHom D.orbitComponentHom_surjective D.sourceOrbitCoordinates
  intro l v
  apply Additive.toMul.injective
  apply Subtype.ext
  simp only [sourceOrbitCoordinates_apply]
  rfl

/-- Every elementary subgroup of the literal automizer has the Suzuki
natural fixed codimension, including actors initially outside the component. -/
theorem sourceOrbit_suzuki_automizer_fixedCodim
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m)
    (A : Subgroup (ChapterE.Automizer D.sourceOrbit)) (hA : IsElementaryTwo A) :
    fixedCodim (ChapterE.automizerRepresentation D.sourceOrbit) A = 2 * (2 * m + 1) := by
  obtain ⟨j, hj, hcoord⟩ := D.sourceOrbit_automizer_marking h.toHypothesis1221
  exact Chapter7.NormalizedSource.suzuki_fixedCodim_of_normalizer_marking hm
    (hs.suzukiModel hm e) hs.faithful hs.irreducible
    (ChapterE.automizerRepresentation D.sourceOrbit) j hj D.sourceOrbitCoordinates hcoord A hA

/-- The local involution parameter in the Suzuki row of Table 7.2.1. -/
theorem sourceOrbit_suzuki_localM
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    2 * (2 * m + 1) ≤ ChapterE.localM D.sourceOrbit := by
  obtain ⟨j, hj, hcoord⟩ := D.sourceOrbit_automizer_marking h.toHypothesis1221
  exact Chapter7.NormalizedSource.suzuki_moduleM_of_normalizer_marking hm
    (hs.suzukiModel hm e) hs.faithful hs.irreducible
    (ChapterE.automizerRepresentation D.sourceOrbit) j hj D.sourceOrbitCoordinates hcoord

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
