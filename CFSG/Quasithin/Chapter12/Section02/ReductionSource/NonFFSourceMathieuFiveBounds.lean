module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuAutomizer
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuFiveBounds

/-!
# The initial large-Mathieu escaping-space bound on the chosen orbit

The full automizer markings supply the actual odd-prime displacement and
near-offender estimates. Together with the proved odd-normalizer control,
these discharge every premise of E.6.27 for a nonzero subspace of corank below
five. The local centralizer is taken inside the original M=N_G(L).
The existing TI argument transports its containment to the minimum defining
r relative to N_G(W); the zero subspace is handled by the actual orbit rank.

Thus r ≥ 5 holds without a local-rank or action-transport callback in either
large Mathieu row. Combined with the companion upper bounds, M23 has
5 ≤ r ≤ 6 and M24 has 5 ≤ r ≤ 8. The distinguished-vector centralizers,
stronger cocode bounds, other Mathieu rows and ambient J4 recognition remain
with the normalized Mathieu assembly.
Source: Aschbacher--Smith, 7.4.1 and8.1.2, printed pp.700,713,
using E.6.27, p.257.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ChapterE ChapterE.Section06 ChapterE.Section06.FixedPointBounds
open Chapter7.NormalizedSource Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original E.6.27 application for both large Mathieu rows. Subspaces
of corank below five have their full centralizer in the original N_G(L). -/
theorem sourceOrbit_largeMathieu_small_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {U : Subgroup G} (hU : U ≠ ⊥) (hUW : U ≤ D.sourceOrbit)
    (hsmall : subgroupCorank D.sourceOrbit U < 5) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr hq)
  have hK := D.sourceOrbit_chapterK_of_many h hmany hnon hV
  have hmarked : MathieuCode.IsM23Code (automizerRepresentation D.sourceOrbit) ∨
      MathieuCode.IsM23Cocode (automizerRepresentation D.sourceOrbit) ∨
      Representation.MathieuSmall.IsM24ToddOrDual (automizerRepresentation D.sourceOrbit) := by
    rcases hq with h23 | h24
    · rcases D.sourceOrbit_m23_automizer_marking h.toHypothesis1221 hK h23 with hc | hd
      · exact Or.inl hc
      · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr (D.sourceOrbit_m24_automizer_marking h.toHypothesis1221 hK h24))
  have h61 := D.sourceOrbit_hypothesisE61_of_many h hmany hnon hV
  obtain ⟨hr,hs,hpos⟩ := D.sourceOrbit_mathieu_initial_parameters h hmany hV hm hnon
  have hsr : globalS D.sourceOrbit ≤ globalR D.sourceOrbit := by rw [hs]; exact hr
  apply source_proposition_E_6_27 h61 hU hUW (j := 1) (by decide) ?_ ?_ ?_
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV hm hnon)
  · exact lt_of_lt_of_le (lt_trans (by decide : (1 : ℕ∞) < 2) hpos) hsr
  · apply induced_nPrime_le_one_of_odd_fixedCodim D.sourceOrbit _ U
      (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right (b := 6) (c := 1)
    · intro p hp ho a ha
      simpa using largeMathieu_odd_fixedCodim_ge_six _ hmarked hp ho a ha
    · simpa using (by omega : subgroupCorank D.sourceOrbit U < 6)
  · exact le_inf (ChapterB.thompsonJ_le _ _ |>.trans inf_le_left)
      (largeMathieu_thompson_centralizes_of_small_corank D.sourceOrbit _ U
        (h61.normal_in_localCentralizer hU hUW).1
        (h61.localCentralizer_le_normalizer hU hUW) hUW inf_le_right hmarked hsmall)

/-- The initial bound in 7.4.1 for the original large Mathieu rows.
The stronger cocode estimates of 8.1.2 are separate obligations. -/
theorem sourceOrbit_largeMathieu_globalR_ge_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M23) ∨
      Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) :
    5 ≤ globalR D.sourceOrbit := by
  have hm : HasMathieuCentralQuotient D.orbitComponent := Or.inr (Or.inr hq)
  apply D.sourceOrbit_globalR_lower_of_local_ranks h hmany hnon hV
    ((by decide : 5 ≤ 10).trans (D.sourceOrbit_mathieu_rank_ge_ten hV hm))
  intro U hUW hU hescape
  have hcor : 5 ≤ subgroupCorank D.sourceOrbit U := by
    by_contra hlt
    exact hescape (D.sourceOrbit_largeMathieu_small_centralizer h hmany hV hq hnon hU hUW
      (by omega))
  have hdim := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUW
  have heq : rank D.sourceOrbit = subgroupCorank D.sourceOrbit U + rank U := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hdim
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
