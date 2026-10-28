module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.EdgePerfect
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.OctadGraph.Source.Overgroup
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRowFlags
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceLocalIsomorphisms

/-!
# Marked Mathieu row comparisons preserving the actual flags and edge

The split natural row extension gives an isomorphism with the prescribed
map on every row element and on its literal quotient. The existing marked
intersection theorems, whose hypotheses do not require linear fusion,
then preserve both point–line and point–plane stabilizers. The derived-group
description of the edge fixer supplies the full edge restriction.

The final consumer applies this to the normalizer-generated subgroup with
its inherited 21/45 orientation. These are the row-side local maps of
Aschbacher, *Sporadic Groups* (1994), 41.4, printed p.222. Agreement with a
map of N_G(A₂) on the common subgroup and native identification remain to
be constructed. The private import reuses the general split-extension
comparison and its coordinate equation without altering the shared API.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
open UniquenessLinear SourceNormalizer
variable {G G' : Type*} [Group G] [Group G'] [Finite G] [Finite G']
  {z : G} {z' : G'} (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

/-- The row comparison retains its original four-space and literal quotient map. -/
theorem exists_row_normalizer_equiv (D : LocalData F) (D' : LocalData F') :
    ∃ e : rowNormalizer F ≃* rowNormalizer F',
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) ∧
      ∀ n, (QuotientGroup.mk (e n) : rowQuotient F') =
        ((LocalData.rowEquiv F D).trans (LocalData.rowEquiv F' D').symm)
          (QuotientGroup.mk n) := by
  let q := (LocalData.rowEquiv F D).trans (LocalData.rowEquiv F' D').symm
  apply split_normalizer_equiv F.row F'.row (rowMarkingEquiv F F') q (rowQuotientAction F')
  · intro n a
    apply Subtype.ext
    exact rowQuotientAction_mk_apply F' n a
  · intro n a
    obtain ⟨n', hn'⟩ := QuotientGroup.mk'_surjective
      (F'.row.subgroupOf (rowNormalizer F')) (q (QuotientGroup.mk n))
    rw [← hn']
    have hq : LocalData.rowEquiv F' D' (QuotientGroup.mk n') =
        LocalData.rowEquiv F D (QuotientGroup.mk n) := by
      change LocalData.rowEquiv F' D' ((QuotientGroup.mk' _) n') = _
      rw [hn']
      exact (LocalData.rowEquiv F' D').apply_symm_apply _
    have he : rowQuotientAction F' (QuotientGroup.mk n') (rowMarkingEquiv F F' a) =
        F'.row.normalizerMonoidHom n' (rowMarkingEquiv F F' a) :=
      Subtype.ext (rowQuotientAction_mk_apply F' n' _)
    change rowMarkingEquiv F F' (F.row.normalizerMonoidHom n a) =
      rowQuotientAction F' (QuotientGroup.mk n') (rowMarkingEquiv F F' a)
    rw [he]
    apply (rowCoordinates F').injective
    apply Multiplicative.toAdd.injective
    rw [UniquenessLinear.rowMarkingEquiv_coordinates, ← LocalData.rowEquiv_action F D,
      ← LocalData.rowEquiv_action F' D', hq, UniquenessLinear.rowMarkingEquiv_coordinates]
  · exact rowQuotientAction_injective F'
  · exact row_normalizer_splits F
  · exact row_normalizer_splits F'

/-- A marked row isomorphism preserves both actual flag intersections and the
whole pointwise edge fixer. Its kernel and quotient maps remain prescribed. -/
theorem exists_row_normalizer_edge_flag_equiv (D : LocalData F) (D' : LocalData F') :
    ∃ e : rowNormalizer F ≃* rowNormalizer F',
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) ∧
      ((planeNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (planeNormalizer F').subgroupOf (rowNormalizer F') ∧
      ((threeSpaceNormalizer F).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (threeSpaceNormalizer F').subgroupOf (rowNormalizer F') ∧
      ((edgeGroup F D).subgroupOf (rowNormalizer F)).map e.toMonoidHom =
        (edgeGroup F' D').subgroupOf (rowNormalizer F') ∧
      ∀ n, (QuotientGroup.mk (e n) : rowQuotient F') =
        ((LocalData.rowEquiv F D).trans (LocalData.rowEquiv F' D').symm)
          (QuotientGroup.mk n) := by
  obtain ⟨e, he, hq⟩ := exists_row_normalizer_equiv F F' D D'
  have hP := row_normalizer_equiv_plane_intersection F F' e he
  have hH := row_normalizer_equiv_threeSpace_intersection F F' e he
  exact ⟨e, he, hP, hH, row_equiv_edgeGroup F D F' D' e hP, hq⟩

/-- The row-side comparison needed for the source 41.1 induction system,
with its inherited orientation and every actual edge/plane subgroup. -/
theorem normalizerSpan_row_edge_flag_equiv (D : LocalData F) (D' : LocalData F') :
    ∃ e : rowNormalizer (normalizerSpanMarking F) ≃* rowNormalizer F',
      ((planeNormalizer (normalizerSpanMarking F)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map e.toMonoidHom =
          (planeNormalizer F').subgroupOf (rowNormalizer F') ∧
      ((threeSpaceNormalizer (normalizerSpanMarking F)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map e.toMonoidHom =
          (threeSpaceNormalizer F').subgroupOf (rowNormalizer F') ∧
      ((edgeGroup (normalizerSpanMarking F) (normalizerSpanLocalData F D)).subgroupOf
        (rowNormalizer (normalizerSpanMarking F))).map e.toMonoidHom =
          (edgeGroup F' D').subgroupOf (rowNormalizer F') := by
  obtain ⟨e, _, hP, hH, hE, _⟩ := exists_row_normalizer_edge_flag_equiv
    (normalizerSpanMarking F) F' (normalizerSpanLocalData F D) D'
  exact ⟨e, hP, hH, hE⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.OctadSource
