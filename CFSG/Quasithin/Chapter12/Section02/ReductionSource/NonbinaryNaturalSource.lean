module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonbinaryNaturalAssembly
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.DoubledOrbitMarking
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete

/-!
# Nonbinary natural exclusion from the preceding source geometry

The three natural actions are excluded on the original chosen fixed-space
quotient. The proof in `NonbinaryNaturalAssembly` constructs the selected
outside subgroup, removes both field-four triangle orientations, excludes
G₂ using the actual R₁-Sylow witness, and applies the classical closure
contradiction. Its symplectic distance-two step is internal. The present
existence contract therefore requires only the preceding geometry, with no
distance witness or C.1.32 recognition premise.

The literal-row application recovers the full L/O₂(L) action through
`LiteralComparison`, retaining the SL₃ center. The final application supplies
the nonbinary contradiction to the seven-module consumer on the same D.
Neither the contradiction nor a terminal closure conclusion is an input.

This completes the conditional implication owned by
qt-d-1222-nonbinary-natural. The local geometry, the earlier 7.0.1, 11.3.2 and
11.2.2 implications, and the odd-extension Fitting-index bound remain explicit.
Their final discharge belongs to qt-d-1222-modules and qt-d-1222-source, using
qt-d-1222-natural-local-geometry, qt-d-1222-natural-shadow-reduction and the
closure source producers. In particular this is not unconditional 11.0.1 or
12.2.2. The legacy distance-bearing APIs remain unchanged.

Source: Aschbacher--Smith, refs/quasithin.pdf, 3.2.8(2--4), 11.0.1--2,
11.1.2, 11.2.2, 11.3.2, 11.5.1--8 and 12.2.2,
printed pp.582,759--784,795.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original flag and preceding geometry, without the obsolete external
distance-two witness. The odd-extension index remains an explicit local field. -/
@[expose] def NonbinaryNaturalPrecedingSources : Prop :=
  ∀ S : D.NonbinaryNaturalInput, ∃ (c : Coordinates D S.field) (f : InvariantFlag c)
    (X : Subgroup G) (z : G), Nonempty (NonbinaryNaturalLocalInputs S f X z)

variable
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hlocal : D.NonbinaryNaturalPrecedingSources)
    (h701 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W),
      Hypothesis1223 KnownSimple.IsKnownSimple T J →
      Chapter7.NormalizedSource.Alternatives G D_J.orbitRepresentation D_J.orbitComponent)
    (h1132 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput) (c_J : Coordinates D_J S_J.field)
      (f_J : InvariantFlag c_J) JH,
      Hypothesis1131At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH →
      Proposition1132At D_J S_J (c_J.binarySubspace (f_J.space 0)) JH)
    (h1122 : ∀ (J W : Subgroup G) (D_J : ChosenModule T J W)
      (S_J : D_J.NonbinaryNaturalInput),
      Nonempty (ActionEquiv D_J.centralQuotientAction (binaryG2 S_J.field)) →
      ChapterE.indexedWeakClosure W (T : Subgroup G) 0 ≤
          (T : Subgroup G) ⊓ centralizer (W : Set G) ∧
        @ChapterE.globalS G _ W D_J.elementary = (2 * S_J.field.degree : ℕ) ∧
        (2 * S_J.field.degree : ℕ∞) < ChapterE.globalR W)

include hmany hlocal h701 h1132 h1122

/-- The exact nonbinary implication consumed by the module classification.
The natural-action input retains FF, the unchanged seed and the full actor;
the earlier implications also apply to the reselected field-four component. -/
theorem nonbinaryNatural_impossible_of_preceding_sources_of_many
    (S : D.NonbinaryNaturalInput) : False := by
  obtain ⟨c,f,X,z,⟨a⟩⟩ := hlocal S
  exact nonbinary_impossible_of_preceding_geometry_of_many S hmany f X z a h701 h1132 h1122

/-- Exclude precisely rows (2)--(4) of 3.2.8 in nonbinary degree on the
literal chosen-space section. Full-cover recovery precedes the exclusion. -/
theorem nonbinaryRow_impossible_of_preceding_sources_of_many
    {P : Type*} [Group P] {ρ : Representation (ZMod 2) P D.space} {K : Subgroup P}
    (cmp : D.LiteralComparison ρ K)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (horbits : componentOrbit V (normalizer (L : Set G)) = V ∨
      (componentOrbit V (T : Subgroup G) = V ∧ V ⊓ centralizer (L : Set G) = ⊥))
    (hff : IsFFModule (normalizerRepresentation D.chosenAction))
    (section_ : MovedSection ρ K) (hf : Function.Injective (section_.action.comp K.subtype))
    (F : BinaryField) (hF : 1 < F.degree)
    (row : LiteralComparison.NonbinaryRow section_ F) : False := by
  obtain ⟨S⟩ := cmp.nonbinaryInput_of_source_branch h hmany horbits hff section_ hf F hF row
  exact D.nonbinaryNatural_impossible_of_preceding_sources_of_many
    hmany hlocal h701 h1132 h1122 S

/-- Apply the conditional three-row exclusion to the actual seven-module
consumer. The seed trichotomy and FF doubled marking are already proved;
the independent non-FF, rank-one and doubled exclusions remain explicit. -/
theorem alternatives_of_nonbinary_preceding_sources_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hdouble : ∀ n, Chapter12.Section01.DoubleNaturalSource.DoubledBranch T L V n → False) :
    ModuleAlternatives1222 D := by
  exact D.alternatives_of_source_inputs_of_many h hmany (D.source325_of_many h hmany)
    hexit hrank
    (D.nonbinaryNatural_impossible_of_preceding_sources_of_many hmany hlocal h701 h1132 h1122)
    hdouble

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
