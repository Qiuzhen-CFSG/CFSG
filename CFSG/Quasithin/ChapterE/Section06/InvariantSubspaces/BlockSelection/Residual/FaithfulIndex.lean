module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.IndexContracts
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.Contracts
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.Normalization
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.FaithfulIndex.Quotient

/-!
# Conditional assembly of the faithful-action three-index calculation

Conjugate-block commutation forces the Sylow three-subgroup containing the
faithful actor to normalize the selected block. Applying the intrinsic rank
bound above that normal block makes the quotient of their join cyclic.
The actor is outside C_G(W), so this cyclic quotient forces the selected
block to have index prime to three in C_G(W).

This is a conditional reduction, not the unconditional `faithfulIndexInput`.
Both structural inputs must be proved before this task is complete. The
commutation input belongs to C.1.9; the quotient-rank input is separate
intrinsic mathematics about actual chi-zero blocks. The reduction works for
any selected block and does not need the count-one hypothesis. The full
E.6.7 input in the source task is neither replaced nor weakened.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7 and
the proof of E.6.14, printed pp.246 and 251 (PDF pp.257 and 262).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]

/-- The faithful-action branch follows from conjugate-block commutation and
the intrinsic quotient-rank theorem. Both remain explicit proof obligations. -/
theorem faithfulIndexInput_of_commutation_and_quotient_rank
    (hc : ConjugateChiZeroCommutationInput G) (hq : NormalChiZeroQuotientRankInput G)
    {K : GroupClass} {T : Sylow 2 G} {M V : Subgroup G}
    (h : HypothesisE61 K T M V) : FaithfulIndexInput T M V := by
  intro W hW hchar hact d _ i
  obtain ⟨x, hxN, hx, hxH⟩ := hact.exists_element
  have hHN : centralizer (W : Set G) ≤ normalizer (W : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hnH : ((centralizer (W : Set G)).subgroupOf (normalizer (W : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hHN).mpr (normalizer_le_normalizer_centralizer W)
  have hr := normalizer_threeRank_le_two h hW.2.1 hW.1
  apply three_index_coprime_of_normalized_sylow_quotient hq hHN (d.le i)
    hnH (d.type i) hr ?_ hxN hx hxH
  intro y hy hyp
  apply normalizes_threePower_of_conjugate_commutation ((d.le i).trans hHN) hr
    (d.type i) hy hyp
  intro z hz hne
  apply hc _ _ hchar (d.le i) (d.type i) (d.subnormal i) z _ hne
  exact (normalizer_le_normalizer_centralizer W) ((zpowers_le.mpr hy) hz)

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
