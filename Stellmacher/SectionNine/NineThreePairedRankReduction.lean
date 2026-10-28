module
import all Stellmacher.ElementaryAbelianMaxOrder
public import Stellmacher.SectionNine.NineThreeMixedGeometry
public import Stellmacher.ElementaryAbelianMaxJFixedCenter

/-!
# A necessary rank deficit in the native-centralization branch

For the actual two normalized center hyperplanes, native Thompson
centralization makes their join elementary abelian. The mixed commutator
lies in the initial center, which centralizes the Baumann subgroup, so the
proved vanishing of the Baumann-fixed mixed subgroup kills it. The other
hyperplane nevertheless acts nontrivially on the full initial center.
Consequently the elementary join cannot have maximum elementary order in T.

This is a reduction, not the missing native-action contradiction: no upper
bound on the maximum elementary order of T is asserted. In particular,
triviality of the restricted mixed action must not be confused with
triviality of the action on the whole initial center.

Source: the two extractions and relation (4) in Stellmacher (9.3), printed
pp.49–50, `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem elementary_subgroup_of_le
    {G : Type u} [Group G] (small large : Subgroup G)
    [IsElementaryAbelian 2 large] (hle : small ≤ large) :
    IsElementaryAbelian 2 small := by
  refine {
    toIsMulCommutative := Subgroup.le_centralizer_iff_isMulCommutative.mp
      ((hle.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)).trans
        (Subgroup.centralizer_le hle))
    exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro element
  exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
    (A := large) (element : G) (hle element.property))

public theorem elementary_noncentral_card_lt_maxOrder
    {G : Type u} [Group G] [Finite G]
    (T Z E : Subgroup G) (hET : E ≤ T)
    (hE : IsElementaryAbelian 2 E)
    (hJ : elementaryAbelianMaxJ T ≤ Subgroup.centralizer (Z : Set G))
    (hnot : ¬ E ≤ Subgroup.centralizer (Z : Set G)) :
    Nat.card E < elementaryAbelianMaxOrder T := by
  let largest := Classical.choose (elementaryAbelianMaxSubgroups_nonempty T)
  have hlargest := Classical.choose_spec (elementaryAbelianMaxSubgroups_nonempty T)
  change Nat.card E < Nat.card largest
  apply lt_of_le_of_ne (hlargest.2.2 E hET hE)
  intro heq
  have hmax : E ∈ elementaryAbelianMaxSubgroups T := by
    refine ⟨hET, hE, fun other hother helem => ?_⟩
    exact (hlargest.2.2 other hother helem).trans_eq heq.symm
  exact hnot ((le_sSup hmax).trans hJ)

public theorem nine_three_paired_join_strict_rank_deficit
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (first : NineThreeFirstConfigurationData ctx)
    (second : NineThreeSecondConfigurationData ctx first)
    (config : NineThreeNormalizedGeometry ctx first second)
    (hJ : elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    let m := ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l)
    let left := ZAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ m
    let right := ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a
    IsElementaryAbelian 2 (left ⊔ right : Subgroup G) ∧
      Nat.card (left ⊔ right : Subgroup G) < elementaryAbelianMaxOrder T := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act config.g (Γ.act first.extraction.x⁻¹ first.l)
  let left := ZAt Γ cp.a ⊓ GAt Γ m
  let right := ZAt Γ m ⊓ GAt Γ cp.a
  let mixed := (⁅left, right⁆ : Subgroup G)
  have hneighbor : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let : IsElementaryAbelian 2 (ZAt Γ cp.a) :=
    z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  have hZcore : ZAt Γ cp.a ≤ QAt Γ cp.a :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core _ _ hneighbor).trans
      ((omegaOneCenter_le_centerAmbient _).trans (Subgroup.map_subtype_le _))
  have hZT : ZAt Γ cp.a ≤ T :=
    hZcore.trans (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).1
  have hZomega := elementary_centralizer_maxJ_le_omegaCenter T (ZAt Γ cp.a)
    hZT (Subgroup.le_centralizer_iff.mp hJ)
  have hZcentral : ZAt Γ cp.a ≤ Subgroup.centralizer (baumannIn T : Set G) :=
    Subgroup.le_centralizer_iff.mp
      ((inf_le_right : baumannIn T ≤ Subgroup.centralizer
        (omegaOneCenterAmbient (elementaryAbelianMaxJ T) : Set G)).trans
          (Subgroup.centralizer_le hZomega))
  have hrightT := (nine_three_mixed_actor_quadratic ctx hb first second config).1
  have hmixedZ : mixed ≤ ZAt Γ cp.a :=
    (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp
        (inf_le_right.trans (stabilizer_le_normalizer_z Γ cp.a)))
  have hzero := nine_three_normalized_baumann_fixed_commutator_bot
    ctx hb hlarge first second config
  have hmixed : mixed = ⊥ :=
    (inf_eq_left.mpr (hmixedZ.trans hZcentral)).symm.trans hzero
  have hmneighbor : Γ.act config.g cp.a' ∈ neighborhood Γ m := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    exact Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp
      (show m ∈ neighborhood Γ (Γ.act config.g cp.a') from by
        change ctx.Γ.act config.g (ctx.Γ.act first.extraction.x⁻¹ first.l) ∈ _
        rw [← config.first_new_vertex]
        exact config.first_geometry.neighbor))
  let : IsElementaryAbelian 2 (ZAt Γ m) :=
    z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hmneighbor
  let : IsElementaryAbelian 2 left := elementary_subgroup_of_le left (ZAt Γ cp.a) inf_le_left
  let : IsElementaryAbelian 2 right := elementary_subgroup_of_le right (ZAt Γ m) inf_le_left
  have hjoin : IsElementaryAbelian 2 (left ⊔ right : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (Subgroup.le_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmixed))
  refine ⟨hjoin, elementary_noncentral_card_lt_maxOrder T (ZAt Γ cp.a)
    (left ⊔ right) (sup_le (inf_le_left.trans hZT) hrightT) hjoin hJ ?_⟩
  intro hcentral
  exact nine_three_mixed_actor_nontrivial_action ctx hb hlarge first second config
    (Subgroup.le_centralizer_iff.mp (le_sup_right.trans hcentral))

end Stellmacher.SectionNine
