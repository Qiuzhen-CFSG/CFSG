module

public import CFSG.Quasithin.Chapter7.Section01To05.SourceOffenders
public import CFSG.Quasithin.Chapter7.Section01To05.MathieuApplications
public import Theory.Mathieu.M23.Properties.TwoRank

/-!
# The M₂₃ code exclusion from the two global bounds

The actual M₂₃ marking gives the automizer two-rank bound. Weak closure
forces r = 6, w = 2 and offender rank four. The exact 7.5.3 subgroup span
then has codimension at least two, whereas the proved H.16.8 calculation
gives codimension at most one. This part of the equality argument does not
need C_V(A) = C_V(Vᵍ), so no bound on the local parameter m is required.

Only w ≤ 2 and r ≥ 6 remain for the earlier source 7.3.4/7.4.1 owners.
The source catalogue and the derivation of those global bounds from the
Fundamental Setup are not asserted by this theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 7.5.4 (M₂₃ code case), printed p.700, and H.16.8, printed p.405.
-/

public section
namespace CFSG.Quasithin.Chapter7
open Subgroup Representation.BinaryOffender ChapterE
open scoped IsMulCommutative

/-- The M₂₃-code part of 7.5.4 with the local rank and fixed-span inputs
discharged. The only remaining numerical premises are the two global bounds. -/
theorem not_m23Code_of_global_bounds
    {G : Type*} [Group G] [Finite G] {V : Subgroup G} [IsElementaryAbelian 2 V]
    {T : Sylow 2 G} (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hw : globalW V T ≤ 2) (hr : 6 ≤ globalR V) :
    ¬ MathieuCode.IsM23Code (automizerRepresentation V) := by
  intro hmodel
  obtain ⟨e, E, hE⟩ := hmodel
  have hq : primeRank 2 (Automizer V) ≤ 4 := by
    rw [Theory.GroupTheory.primeRank_equiv 2 e]
    exact Sporadic.Mathieu.m23_twoRank_le_four
  obtain ⟨hweq, hqeq, _, heq⟩ := mathieu_forced_parameters hT hFF hq hw hr
  obtain ⟨g, hg⟩ := exists_isWOffenderAt_of_globalW_ne_top hT (by rw [hweq]; simp)
  have hc := source_offender_span_bounds hT hFF hg heq
  have hI : rank (inducedAutomizer V (offenderNormalizer V g)) = 4 := hc.1.trans hqeq
  let I := inducedAutomizer V (offenderNormalizer V g)
  change rank I = 4 at hI
  let _ : IsElementaryAbelian 2 I := offender_inducedAutomizer_elementary V g
  have hcard : Nat.card I = 16 := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 I).exists_card_eq
    have hn4 : n = 4 := by
      simpa only [rank, hn, Nat.log_pow Nat.one_lt_two] using hI
    rw [hn, hn4]
    rfl
  have hdim := ChapterH.Section13To16.m23Code_fixedSpan_bound_of_native
    (automizerRepresentation V) ⟨e, E, hE⟩ m23Code_fixedSpan_bound I inferInstance hcard
  have hlo := hc.2.2
  rw [← offenderFixedSpan_eq_sourceFixedSpan, hweq, offenderFixedSpan_corank] at hlo
  have hlo' : 2 ≤ Module.finrank (ZMod 2) (Additive V ⧸
      fixedSpaceSpan (automizerRepresentation V) I) := by exact_mod_cast hlo
  omega

end CFSG.Quasithin.Chapter7
