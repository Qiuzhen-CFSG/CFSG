module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification.Orientation
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSource
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# The normalized 7.0.1 alternatives force FF on the original orbit

Simplicity identifies I/O₂(I) with the actual component acting on the entire
FSU orbit. Its field-four order excludes the orthogonal-minus rank-one
alternative; the original global hypotheses exclude J₄. Thus the source
7.0.1 conclusion yields FF for the full linear normalizer on that orbit,
without identifying the orbit with its chosen seed.

Source: Aschbacher--Smith 7.0.1 and 11.0.2, printed pp.695 and 759--760.
The normalized 7.0.1 implication is owned by `qt-d-1222-normalized-nonff`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
open Chapter12.Section02 ChapterB.QuasisimpleSource LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L I U : Subgroup G}

/-- The unchanged component quotient acts faithfully on the full seed orbit. -/
def orbitComponentEquiv (D : ChosenModule T I U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T I)
    (hs : IsSimpleGroup (I ⧸ pCore 2 I)) :
    (I ⧸ pCore 2 I) ≃* D.orbitComponent := by
  let := hs
  exact MulEquiv.ofBijective (D.orbitComponentQuotientHom h)
    ⟨(D.orbitComponentQuotientHom h).injective_of_surjective_of_simple
      (D.orbitComponentQuotientHom_surjective h),
      D.orbitComponentQuotientHom_surjective h⟩

/-- The field-four group clause removes the genuine orthogonal action row. -/
theorem not_orthogonal_orbit (D : ChosenModule T I U)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I) :
    ¬ Chapter7.NormalizedSource.OrthogonalMinusAlternative
      D.orbitRepresentation D.orbitComponent := by
  rintro ⟨n, hn, ⟨m⟩⟩
  let : NeZero n := ⟨by omega⟩
  let F : BinaryField := {
    Carrier := OrthogonalFourMinus.FiniteModel.Field n
    degree := 2 * n
    degree_pos := by omega
    card_eq := GaloisField.card 2 (2 * n) (by omega) }
  have he := (orbitComponentEquiv D h (orientation_simple ho)).trans m.groupEquiv
  exact no_linearTwo_order F ((Nat.card_congr he.toEquiv) ▸ orientation_order ho)

/-- Original normalized 7.0.1, specialized to this chosen triangle orbit.
The source disjunction is an explicit earlier result, not a natural marking
or an FF premise for the chosen seed. -/
theorem orbit_ff_of_source701 (D : ChosenModule T I U)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (ho : TriangleOrientation L I)
    (h701 : Chapter7.NormalizedSource.Alternatives G
      D.orbitRepresentation D.orbitComponent) :
    IsFFModule D.sourceOrbitNormalizerRepresentation := by
  rcases h701 with hff | hm | hj
  · exact hff
  · exact (not_orthogonal_orbit D h.toHypothesis1221 ho hm).elim
  · exact (h.no_J4 hj).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Classification
