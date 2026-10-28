module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Residual.IndexContracts

/-!
# Structural inputs for the faithful-action index calculation

Distinct conjugate chi-zero blocks commute by the appropriate specialization
of C.1.9. The full conjugating element is retained here: controlling only
actors of order three would not control an entire Sylow three-subgroup.

The independent normal-block calculation says that in three-rank at most
two a three-group quotient above a normal chi-zero block has three-rank
at most one.
It concerns the actual quotient, with normality relative to its overgroup.
These definitions are proof obligations, not assertions of either result.
The final index assembly uses them to rule out further three-elements in
C_G(W) when a cubic actor lies outside that centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.9 and
C.1.12 on printed pp.123–124, and the proof of E.6.14 on printed p.251.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
/-- The C.1.9 specialization needed for all three-power conjugating elements. -/
def ConjugateChiZeroCommutationInput (G : Type*) [Group G] : Prop :=
  ∀ H L : Subgroup G, HasCharacteristicTwo H → L ≤ H →
    ChapterC.IsChiZeroBlock L → (L.subgroupOf H).IsSubnormal →
    ∀ x ∈ normalizer (H : Set G), L.map (MulAut.conj x) ≠ L →
      L.map (MulAut.conj x) ≤ centralizer (L : Set G)

/-- The intrinsic rank bound above a relatively normal, actual chi-zero block. -/
def NormalChiZeroQuotientRankInput (G : Type*) [Group G] : Prop :=
  ∀ J L : Subgroup G, L ≤ J → ∀ hn : (L.subgroupOf J).Normal,
    ChapterC.IsChiZeroBlock L → primeRank 3 J ≤ 2 →
      letI := hn
      IsPGroup 3 (J ⧸ L.subgroupOf J) → primeRank 3 (J ⧸ L.subgroupOf J) ≤ 1

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
