module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuRankOneFixedSpace
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceRecognitionBound

/-!
# The initial ambient Suzuki bounds from E.6.3

The full automizer calculation gives m >= 2(2m+1) > 2. The literal chosen
orbit satisfies E.6.1 with the original Sylow subgroup and N_G(L), so E.6.3
gives r >= m and s = m. Its independent Held-cover premise is explicitly
retained; its existing producer is `qt-held-odd-center`. The final owner
`qt-d-1222-nonmathieu-unitary-suzuki-exclusion` must discharge this premise
and prove the stronger Section 7.4 bound before claiming the exclusion.

This is the source 7.3.2 application, not the stronger 7.4.1 estimate.
Source: Aschbacher--Smith, E.6.3 and 7.3.2, printed pp.245,698.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- E.6.3 applied to the original Suzuki orbit, retaining exactly its
independent finite quasisimple Held-cover input. -/
theorem sourceOrbit_suzuki_initial_parameters_of_held_center
    (hHeld : ∀ (X : Type u) [Group X] [Finite X] [IsQuasisimple X],
      Nonempty ((X ⧸ center X) ≃* Held.He) → Odd (Nat.card (center X)))
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hs : ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {m : ℕ} (hm : 1 ≤ m)
    (e : (D.orbitComponent ⧸ center D.orbitComponent) ≃* SuzukiMatrixGroup m) :
    ((2 * (2 * m + 1) : ℕ) : ℕ∞) ≤ ChapterE.globalR D.sourceOrbit ∧
      ChapterE.globalS D.sourceOrbit = (ChapterE.localM D.sourceOrbit : ℕ∞) ∧
      2 < ChapterE.globalS D.sourceOrbit := by
  have hlocal := D.sourceOrbit_suzuki_localM h hs hm e
  have h61 := D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon
  obtain ⟨hr, hS, hspos⟩ :=
    ChapterE.Section06.FrobeniusReduction.lower_bound_knownSimple_of_held_center
      hHeld h61 (by omega)
  exact ⟨(ENat.natCast_le_natCast.mpr hlocal).trans hr, hS, hspos⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
