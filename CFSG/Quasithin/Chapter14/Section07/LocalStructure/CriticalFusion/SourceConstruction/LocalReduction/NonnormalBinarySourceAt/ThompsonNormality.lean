module
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource
import all CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.NonnormalBinarySourceAt.ThompsonMarking

/-!
# Original Thompson normality at the same G,T

The actual flag marking and equal-weight replacement prove normality of
J(T) in the original LT when J(T) lies in the original point radical.
Only the structural predecessor at that same Sylow is used.
Source: Aschbacher–Smith 14.3.9, printed pp.992–993.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section03.ThompsonSource
open Chapter12.Section08 Chapter12.Section02 Matrix.PSL3Two
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
  (F : InvariantFlag T V 3) (structural : Structural1222At KnownSimple.IsKnownSimple T)

include h structural in
theorem thompson_normal_at
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ F.Ri L 1) :
    ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal := by
  obtain ⟨e, q, hq, hk2, ha, hk, hT, hR⟩ := exists_marking_at h F structural
  let H := L ⊔ (T : Subgroup G)
  let E := V.subgroupOf H
  have hVH : V ≤ H := h.chosen.le_sylow.trans le_sup_right
  let := h.chosen.elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVH
  let : E.Normal := (normal_subgroupOf_iff_le_normalizer hVH).mpr
    (sup_le h.chosen.normalizes (h.sylow_normalizes_seed_at structural))
  let a : E ≃* V := subgroupOfEquivOfLe hVH
  let e' : Model ≃* E := e.trans a.symm
  have ha' (g : H) (v : Model) :
      (e' (slAut (q g) v) : H) = g * (e' v : H) * g⁻¹ := by
    apply Subtype.ext
    exact ha g v
  have hk' : q.ker = centralizer (E : Set H) := by
    rw [hk]
    ext g
    constructor
    · intro hg v hv
      apply Subtype.ext
      exact hg v hv
    · intro hg v hv
      exact congrArg Subtype.val (hg ⟨v, hVH hv⟩ hv)
  let S : Sylow 2 H := T.subtype le_sup_right
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hSmap : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hSmap]
  have hJsub : elementaryAbelianMaxJ (S : Subgroup H) =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [hJmap, map_subgroupOf_eq_of_le (hJT.trans le_sup_right)]
  rw [← hJsub]
  apply thompson_normal_of_image_escape S E q hq hk' hk2
    (subgroupOf_mono _ h.chosen.le_sylow) MarkedAutomorphisms.pointV
  · rw [hJsub]
    exact hR ▸ map_mono (subgroupOf_mono _ hJ)
  · intro B hB hne _
    obtain ⟨C, _, hC, heq, _, g, hgS, hgD⟩ :=
      BinaryLinearThree.ThompsonEscape.exists_replacement_escape B hB hne
    refine ⟨C, hC, ⟨heq.1, ?_⟩, g, ?_, hgD⟩
    · rw [weight_transport E q hq hk' e' ha', weight_transport E q hq hk' e' ha']
      exact heq.2
    · exact hT ▸ hgS

end CFSG.Quasithin.Chapter14.Section03.ThompsonSource
