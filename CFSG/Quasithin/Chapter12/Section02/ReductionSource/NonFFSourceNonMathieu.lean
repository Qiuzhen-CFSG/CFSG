module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssembly
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible

/-!
# The literal chosen-module application of the non-Mathieu assembly

The selected PSL₂ branch constructs Chapter K hypotheses from the original
chosen-module setup and returns the marked orthogonal action. The conditional
consumer replaces exactly the existing non-Mathieu branch callback by the
family sieve and its unitary, Suzuki and Hermitian exclusions. The original
Sylow subgroup, both literal actions and all four branch hypotheses remain.
The independent source inputs are not asserted to be proved here.

Source: Aschbacher--Smith,3.2.9,7.0.1 and12.2.2, printed pp.582--583,695,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation.BinaryOffender BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.NonMathieuAssembly
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The selected PSL₂ source branch on the literal chosen orbit, deriving
Chapter K hypotheses from the original Sylow and multiple-overgroup data. -/
theorem sourceOrbit_orthogonal_of_psl2_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {r : ℕ} (hr : 2 ≤ r)
    (hq : ClassicalGroup.IsPSL (D.orbitComponent ⧸ center D.orbitComponent) 2 (2 ^ r)) :
    OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent :=
  orthogonal_of_psl2 (D.sourceOrbit_chapterK_of_many h hmany hnon hV) hnon hr hq

/-- The non-Mathieu assembly on the original orbit and component, with
the independent source producers still supplying the explicit inputs. -/
theorem sourceOrbit_orthogonal_of_nonMathieu_inputs
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hfamilies : SourceFamilies hs)
    (hunitary : ∀ s : ℕ, 2 ≤ s →
      ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s) → False)
    (hsuzuki : ∀ m : ℕ, 1 ≤ m →
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) → False)
    (hhermitian : HermitianRow hs → False) :
    OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent :=
  orthogonal_of_families hs hnon hfamilies hunitary hsuzuki hhermitian

/-- Apply the assembly at the unchanged `hother` boundary. Every source
producer receives the original invariant-seed, Chapter K, non-Mathieu and
full-normalizer non-FF hypotheses. Doubled and Mathieu inputs stay separate. -/
theorem sourceOrbit_ff_or_orthogonal_of_nonMathieu_inputs_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hdoubled : V ≠ D.sourceOrbit →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → False)
    (hmathieu : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → Nonempty (G ≃* Janko4.Model))
    (hfamilies : V = D.sourceOrbit →
      ∀ hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent,
      ¬ HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → SourceFamilies hs)
    (hunitary : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      ¬ HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation →
      ∀ s : ℕ, 2 ≤ s →
        ClassicalGroup.IsPSU (D.orbitComponent ⧸ center D.orbitComponent) 3 (2 ^ s) → False)
    (hsuzuki : V = D.sourceOrbit →
      ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent →
      ¬ HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation →
      ∀ m : ℕ, 1 ≤ m →
        Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) → False)
    (hhermitian : V = D.sourceOrbit →
      ∀ hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent,
      ¬ HasMathieuCentralQuotient D.orbitComponent →
      ¬ IsFFModule D.sourceOrbitNormalizerRepresentation → HermitianRow hs → False) :
    IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      OrthogonalMinusAlternative D.orbitRepresentation D.orbitComponent := by
  apply D.sourceOrbit_ff_or_orthogonal_of_branches_of_many h hmany hdoubled hmathieu
  intro hV hs hnm hnon
  exact D.sourceOrbit_orthogonal_of_nonMathieu_inputs hs hnon
    (hfamilies hV hs hnm hnon) (hunitary hV hs hnm hnon)
    (hsuzuki hV hs hnm hnon) (hhermitian hV hs hnm hnon)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
