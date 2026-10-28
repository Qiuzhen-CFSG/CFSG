module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuM23CodeBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuOddControl
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuRankOneOddCodimension
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Source

/-!
# The original M₂₃ code automizer is excluded

For a nonzero code subspace of corank less than six, the marked odd-prime
spectrum makes the actual local Cartan parameter one. The strict elementary
codimension gap makes its higher Thompson subgroup centralize the source
orbit. The proved Mathieu odd-normalizer control then completes every
hypothesis of E.6.27. Consequently r ≥ 6 on the original orbit, and w ≤ 2
supplies the existing fixed-span contradiction in 7.5.4.

These theorems retain the literal ambient automizer action. The remaining
Mathieu markings, shadow eliminations and ambient J₄ recognition stay with
the normalized Mathieu assembly; this module does not assert those results.
Source: Aschbacher--Smith E.6.27,7.4.1 and7.5.4, printed pp.257,700.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds
open Chapter7.NormalizedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The two H.16 displacement estimates discharge both local-action premises
of E.6.27 for a nonzero code subspace of corank less than six. -/
theorem sourceOrbit_m23Code_small_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hc : MathieuCode.IsM23Code (automizerRepresentation D.sourceOrbit))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hsmall : subgroupCorank D.sourceOrbit U < 6) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  have hp := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hp.2.1]; exact hp.1
  apply source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide) ?_ ?_ ?_
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon)
  · exact lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hp.2.2) hsr
  · apply induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit _ U
      (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right (b := 6) (c := 1)
    · intro p hp ho a ha
      simpa using m23Code_marked_odd_fixedCodim _ hc hp ho a ha
    · simpa using hsmall
  · exact le_inf (ChapterB.thompsonJ_le _ _ |>.trans inf_le_left)
      (thompson_centralizes_of_fixedCodim_gap D.sourceOrbit _
        (h61.normal_in_localCentralizer hU hUW).1
        (h61.localCentralizer_le_normalizer hU hUW)
        (m23Code_marked_fixedCodim_gap _ hc))

/-- Source 7.4.1 for the original M23 code automizer, with every local
rank, normalizer and representation premise discharged. -/
theorem sourceOrbit_m23Code_globalR_ge_six
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hc : MathieuCode.IsM23Code (automizerRepresentation D.sourceOrbit)) :
    6 ≤ globalR D.sourceOrbit := by
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV
    ((by decide : 6 ≤ 10).trans (D.sourceOrbit_mathieu_rank_ge_ten hV hm))
  intro U hUW hU hescape
  have hcor : 6 ≤ subgroupCorank D.sourceOrbit U := by
    by_contra hlt
    exact hescape (D.sourceOrbit_m23Code_small_centralizer h hmany hV hm hnon hc hU hUW
      (by omega))
  have hdim := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUW
  have heq : rank D.sourceOrbit = subgroupCorank D.sourceOrbit U + rank U := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hdim
  omega

/-- The original M23-code alternative in 7.5.4 is impossible on the source
orbit: the proved w≤2 and r≥6 feed its actual fixed-span contradiction. -/
theorem sourceOrbit_not_m23Code_of_mathieu
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    ¬ MathieuCode.IsM23Code (automizerRepresentation D.sourceOrbit) := by
  intro hc
  exact D.sourceOrbit_not_m23Code_of_many h hmany hnon
    (D.sourceOrbit_mathieu_globalW_le_two h hmany hV hm hnon)
    (D.sourceOrbit_m23Code_globalR_ge_six h hmany hV hm hnon hc) hc
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
