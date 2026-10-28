module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Models.FFAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesComplete

/-!
# The remaining normalized source branches for the outside component

Apply proved 3.2.5 and the completed non-Mathieu argument to the
literal chosen orbit. The only remaining normalized 7.0.1 inputs are the
marked non-FF doubled exclusion and the original Mathieu implication.
These inputs are quantified over every chosen module at the same G and T:
the parameter proof selects a new maximal overcomponent, so inputs for
the initial chosen module alone would not suffice.

The second theorem applies this reduction to that selected overcomponent,
yielding k=n and the outside component on the actual embedded O²(H).
It retains all earlier geometric, odd-kernel and residual/cubic premises.
The doubled and Mathieu inputs remain with qt-d-1222-nonff-doubled and
qt-d-1222-nonff-mathieu. Final discharge of those inputs remains
here; the earlier source premises retain their producers and final parent
qt-d-1222-shadow-linear-geometry. This is a conditional source assembly.

Source: Aschbacher--Smith, 3.2.5, 7.0.1 and 11.3.5--6,
printed pp.580--581,695--696,771--773; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource LocalGeometry

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The normalized source exit on an arbitrary chosen overcomponent.
Source 3.2.5 and the entire non-Mathieu branch are
discharged; the full orbit and its actual component marking are preserved. -/
theorem source_alternatives_of_nonff_branches
    {J W : Subgroup G} (E : Chapter12.Section02.ChosenModule T J W)
    (hsrc : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : E.MarkedDoubled →
      ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : W = E.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses E.orbitRepresentation E.orbitComponent →
      HasMathieuCentralQuotient E.orbitComponent →
      ¬ IsFFModule E.sourceOrbitNormalizerRepresentation →
      Nonempty (G ≃* Janko4.Model)) :
    Alternatives G E.orbitRepresentation E.orbitComponent :=
  E.sourceOrbit_alternatives_of_source_inputs_of_many hsrc hmany
    (E.source325_of_many hsrc hmany) hdoubled hmathieu

/-- Apply the two remaining normalized branches to the actual maximal
overcomponent selected by the parameter proof. No assumed normalized
classification, component recognition or parameter equality remains. -/
theorem conclusion_of_nonff_branch_sources
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    {c : LocalGeometry.Coordinates D S.field} (F : InvariantFlag c)
    (hpoint : c.binarySubspace (F.space 0) = U₁)
    (hs : @ChapterE.globalS G _ V D.elementary = WeakClosure.Parameters.naturalParameter D S c)
    (hcontrol : WeakClosure.Generation.OddKernelNormalizer (T := T) (L := L) (V := V))
    (hdoubled : ∀ (J W : Subgroup G) (E : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → E.MarkedDoubled →
      ¬ IsFFModule E.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : ∀ (J W : Subgroup G) (E : Chapter12.Section02.ChosenModule T J W),
      Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T J →
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      W = E.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses E.orbitRepresentation E.orbitComponent →
      HasMathieuCentralQuotient E.orbitComponent →
      ¬ IsFFModule E.sourceOrbitNormalizerRepresentation →
      Nonempty (G ≃* Janko4.Model))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    Conclusion S H := by
  apply conclusion_of_normalized_source h pr hc F hpoint hs hcontrol ?_ hres hcubic
  intro J W E hsrc hmany
  exact source_alternatives_of_nonff_branches E hsrc hmany
    (hdoubled J W E hsrc hmany) (hmathieu J W E hsrc hmany)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
