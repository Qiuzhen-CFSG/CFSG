module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison.StarBorel
public import Theory.SpecificGroups.Alternating.FiveSylowNormalizerCard

/-!
# Excluding the contained component on the natural star row

C.2.7's natural row reconstructs either an L₂-block or an alternating-five
block and identifies the actual star intersection as a Sylow normalizer.
The core-to-star comparison restores this Borel in J/O₂(J). The original
order-five generator excludes the alternating-five possibility, whose
Sylow two-normalizers have order twelve. The L₂-block then supplies the
marked natural Borel used by the terminal central-involution contradiction.

This proves the contained branch once the actual natural row has been
selected. Row selection, construction of the normalizer geometry and
escaping component, and the outer branch remain obligations of the
14.6.15 assembly owner, qt-e-14615-quintic-exclusion. The parent
qt-e-suitable-odd-normalizer discharges the earlier-source inputs in Context.

Source: Aschbacher--Smith 14.6.15, printed p.1035; C.2.7(3)(a)(i),
pp.145--147.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T, sourceResidual M Mc, localModule T M, localModule T M, centralInvolutions T, H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))

variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : EscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The star Borel is the normalizer in the original core quotient of J. -/
theorem contained_core_borel_of_chiZero (h : d.K1 ≤ j.J)
    (hc : ChapterC.IsChiZeroBlock j.J)
    (hb : IsRankOneBorel (starImage j.J (Mc.pCoreIn 2) j.J)
      (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G)))) :
    ∃ S : Sylow 2 (j.J ⧸ pCore 2 j.J),
      coreImage j.J (borelIntersection s d j) =
        normalizer (S : Set (j.J ⧸ pCore 2 j.J)) := by
  have hB : borelIntersection s d j = (Mc ⊓ normalizer (d.K2 : Set G)) ⊓ j.J := by
    unfold borelIntersection
    rw [contained_span s d j h, inf_comm]
  rw [hB]
  exact core_borel_of_chiZero (contained_input s d j h) hc hb

/-- The original order-five generator survives in the literal Borel image. -/
theorem five_dvd_core_intersection (h : d.K1 ≤ j.J) :
    5 ∣ Nat.card (coreImage j.J (borelIntersection s d j)) := by
  obtain ⟨k, hk, ho⟩ := exists_first_generator d
  let kJ : j.J := ⟨k, h hk⟩
  let π := QuotientGroup.mk' (pCore 2 j.J)
  have hπker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hoJ : orderOf kJ = 5 := (Subgroup.orderOf_coe _).symm.trans ho
  have hoπ : orderOf (π kJ) = 5 := by
    rw [π.orderOf_map_eq_of_coprime_of_isPGroup_ker hπker _ (by rw [hoJ]; decide), hoJ]
  have hkB : π kJ ∈ coreImage j.J (borelIntersection s d j) :=
    mem_map_of_mem π (first_le_intersection s d j h hk)
  let x : coreImage j.J (borelIntersection s d j) := ⟨π kJ, hkB⟩
  have hx : orderOf x = 5 := (Subgroup.orderOf_coe _).symm.trans hoπ
  exact hx ▸ orderOf_dvd_natCard x

/-- The actual Borel containing K₁ excludes the reconstructed A₅-block. -/
theorem not_alternating_five_of_star_borel (h : d.K1 ≤ j.J)
    (hb : IsRankOneBorel (starImage j.J (Mc.pCoreIn 2) j.J)
      (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G)))) :
    ¬ ChapterC.IsAlternatingBlock j.J 5 := by
  intro ha
  obtain ⟨P, hP⟩ := contained_core_borel_of_chiZero s d j h (Or.inr (Or.inr ha)) hb
  obtain ⟨e⟩ := ha.2.2.quotient_iso
  exact Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_not_five_of_alternating_five
    e P (hP ▸ five_dvd_core_intersection s d j h)

/-- The genuine natural row suffices, with no additional block or Borel premise. -/
theorem false_of_natural_row (h : d.K1 ≤ j.J)
    (row : NaturalStarRow j.J (Mc.pCoreIn 2)) : False := by
  obtain ⟨_, hb, _, hc⟩ := contained_row_geometry s d j h row
  rcases hc with ⟨n, hn⟩ | ha
  · exact false_of_core_block_borel s d j h hn
      (contained_core_borel_of_chiZero s d j h (Or.inl ⟨n, hn⟩) hb)
  · exact not_alternating_five_of_star_borel s d j h hb ha

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison
