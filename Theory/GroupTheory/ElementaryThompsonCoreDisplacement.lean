module
public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Maximum elementary subgroups under bounded core displacement

If J(S) lies in Q and an elementary subgroup W of S centralizes Q, every
maximum elementary subgroup of S contains W. Consequently [Q,K] ≤ W
makes K normalize each member of that family. Any subfamily generating
J(R) is preserved as well.

Source application: the block exclusion in Aschbacher–Smith 13.4.7(4),
printed p.903. The source uses Q=O₂(H₀), W=V₀ and R=O₂(LT).
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- Core displacement into a fixed elementary subgroup preserves each maximum. -/
theorem maxElementary_normalized_of_core_displacement
    (S Q W K : Subgroup G) [IsElementaryAbelian 2 W]
    (hW : W ≤ S) (hWQ : W ≤ centralizer (Q : Set G))
    (hJ : elementaryAbelianMaxJ S ≤ Q) (hmove : ⁅Q,K⁆ ≤ W)
    {A : Subgroup G} (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    K ≤ normalizer (A : Set G) := by
  have hAQ : A ≤ Q := (le_sSup hA).trans hJ
  have hWA : W ≤ A := maxElementary_contains_elementary_centralizer S A W hA hW
    (hWQ.trans (centralizer_le hAQ))
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono hAQ le_rfl).trans hmove).trans hWA

/-- A family inclusion transfers the same invariance to the smaller Thompson group. -/
theorem maxJ_normalized_of_core_displacement
    (S Q W K R : Subgroup G) [IsElementaryAbelian 2 W]
    (hW : W ≤ S) (hWQ : W ≤ centralizer (Q : Set G))
    (hJ : elementaryAbelianMaxJ S ≤ Q) (hmove : ⁅Q,K⁆ ≤ W)
    (hfamily : elementaryAbelianMaxSubgroups R ⊆ elementaryAbelianMaxSubgroups S) :
    K ≤ normalizer (elementaryAbelianMaxJ R : Set G) := by
  change K ≤ normalizer ((sSup (elementaryAbelianMaxSubgroups R) : Subgroup G) : Set G)
  rw [sSup_eq_iSup']
  apply le_trans _ (iInf_normalizer_le_normalizer_iSup
    (fun A : elementaryAbelianMaxSubgroups R => A.val))
  exact le_iInf fun A => maxElementary_normalized_of_core_displacement
    S Q W K hW hWQ hJ hmove (hfamily A.property)
end Stellmacher
