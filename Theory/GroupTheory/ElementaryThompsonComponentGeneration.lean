module
public import Theory.GroupTheory.CComponent.CommutatorDichotomy
public import Theory.GroupTheory.ElementaryThompsonSpan

/-!
# Commutator generation of normal Thompson components

The C-component commutator dichotomy reduces to the case where the Sylow
Thompson subgroup centralizes the component modulo the solvable radical.
Normality propagates this centralization to all Sylow conjugates and hence
to the global Thompson subgroup. A perfect component contained there would
then be solvable, a contradiction.

Source: Aschbacher–Smith A.3.3(7), pp.42–43, and the component paragraph
in the proof of 14.7.67(4), printed p.1070.
-/

public section
open Subgroup
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- A normal C-component lying in the global Thompson subgroup is generated
by its commutators with the Thompson subgroup of every Sylow two-subgroup. -/
theorem normal_cComponent_commutator_maxJ
    (S : Sylow 2 G) {B : Subgroup G} [B.Normal] (hB : B.IsCComponent)
    (hBJ : B ≤ elementaryAbelianMaxJ (⊤ : Subgroup G)) :
    ⁅B, elementaryAbelianMaxJ (S : Subgroup G)⁆ = B := by
  rcases hB.commutator_le_radical_or_eq_iSup_conjugates
    (elementaryAbelianMaxJ (S : Subgroup G)) with hc | hc
  · let q := QuotientGroup.mk' (solvableRadical G)
    let C := (centralizer (B.map q : Set (G ⧸ solvableRadical G))).comap q
    let : (B.map q).Normal := (inferInstance : B.Normal).map q (QuotientGroup.mk'_surjective _)
    have hSC : elementaryAbelianMaxJ (S : Subgroup G) ≤ C := by
      apply map_le_iff_le_comap.mp
      apply commutator_eq_bot_iff_le_centralizer.mp
      rw [← map_commutator, commutator_comm, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hc
    have hJC : elementaryAbelianMaxJ (⊤ : Subgroup G) ≤ C := by
      rw [elementaryAbelianMaxJ_eq_conjugateSpan_sylow S]
      exact conjugateSpanBy_le hSC (by rw [normalizer_eq_top])
    have hBC : B.map q ≤ centralizer (B.map q : Set (G ⧸ solvableRadical G)) :=
      map_le_iff_le_comap.mpr (hBJ.trans hJC)
    have hBR : B ≤ solvableRadical G := by
      have hh := commutator_eq_bot_iff_le_centralizer.mpr hBC
      rw [← map_commutator, Subgroup.isPerfect_iff.mp hB.perfect,
        Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hh
      exact hh
    exact (hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := inclusion hBR) (inclusion_injective hBR))).elim
  · apply le_antisymm (commutator_le_left _ _) _
    rw [hc]
    exact le_iSup_conjugates _ _

end Stellmacher
