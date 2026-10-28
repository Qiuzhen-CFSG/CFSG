module
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.Commutator.Basic
/-!
# The two-core of a normal three-group joined to a Sylow two-group

The two-core centralizes the normal three-group by coprimeness. Conversely,
the Sylow centralizer is normalized by both factors, so is a normal two-group
in their join. This identifies the actual embedded two-core with that
centralizer, preserving both the Sylow and the ambient subgroup maps.

Source application: Aschbacher–Smith, original 13.2.9, printed p.881.
-/
public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem core_join_odd_eq_sylow_centralizer (Z : Subgroup G) [Z.Normal]
    (hZ : IsPGroup 3 Z) (S : Sylow 2 G) :
    (Z ⊔ (S : Subgroup G)).pCoreIn 2 = (S : Subgroup G) ⊓ centralizer (Z : Set G) := by
  let B := Z ⊔ (S : Subgroup G)
  let D := (S : Subgroup G) ⊓ centralizer (Z : Set G)
  have hnQ : B ≤ normalizer (B.pCoreIn 2 : Set G) := B.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  have hQS : B.pCoreIn 2 ≤ (S : Subgroup G) := by
    have hh := pCoreIn_le_sylow B (S.subtype (show (S : Subgroup G) ≤ B from le_sup_right))
    change B.pCoreIn 2 ≤ ((S : Subgroup G).subgroupOf B).map B.subtype at hh
    rwa [map_subgroupOf_eq_of_le (show (S : Subgroup G) ≤ B from le_sup_right)] at hh
  apply le_antisymm
  · refine le_inf hQS ?_
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    have hd := (isPGroup_pCoreIn 2 B).disjoint_of_coprime hZ (by decide : Nat.Coprime 2 3)
    apply le_trans ?_ hd.le_bot
    exact le_inf (by rw [commutator_comm]; exact
      le_normalizer_iff_commutator_le_right.mp ((show Z ≤ B from le_sup_left).trans hnQ))
      (commutator_le_right _ _)
  · apply le_pCoreIn_of_normalizes (S.isPGroup'.to_le inf_le_left)
      (inf_le_left.trans le_sup_right)
    apply sup_le
    · exact (le_centralizer_iff.mp (show D ≤ centralizer (Z : Set G) from inf_le_right)).trans
        (centralizer_le_normalizer _)
    · exact (le_inf (S : Subgroup G).le_normalizer le_normalizer_of_normal).trans
        inf_normalizer_le_normalizer_inf
end Subgroup
