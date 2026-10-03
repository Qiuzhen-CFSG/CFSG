module

public import Stellmacher.SectionNine.DistanceOneExtraction
public import Theory.GroupTheory.DihedralTwoCore

/-!
# The distance-one coatom is the next stabilizer intersection

For an ambient-retaining Section Nine context whose critical path has length
one, the coatom in a distance-one extraction is the intersection of Z_alpha
with G_next, where next is the translate of alpha by the inverse of the
extracted conjugator. The existential conclusion keeps the complete extraction
record unchanged, including its quotient, swapping involutions, actor
generation, and residual commutator. It supplies the identification needed
to read the record's cardinality and generation statements as (9.1)(ii),(v).

For one inclusion, an actor in G_next normalizes the elementary center Z_next.
If it were outside the coatom, actor generation would make E a two-group,
contradicting the coatom's description as Z_alpha intersect O₂(E).
For the reverse inclusion, the extracted quotient is an odd-dihedral group
times an abelian group, so its two-core is central by
`dihedralProduct_twoCore_le_center`. The image of O₂(E) lies in that core.
Thus an element of the coatom commutes with the conjugator modulo the
quotient kernel E intersect Q_beta. Since Q_beta lies in G_alpha, conjugating
the element back leaves it in G_alpha, as required. The second quotient
factor is abelian because the record identifies it as an image of the coatom;
no compatibility of the abstract product equivalence with that image is assumed.

Source: Stellmacher (9.1), journal p.46, initial relations (i)--(v), using the
proved elementary-actor extraction from (7.8). Hypothesis Two remains on the
ambient group H; it is not inferred for the graph group G. The further
commutator and local-geometry relations remain separate results.
-/

namespace Stellmacher.SectionNine

open Stellmacher.SectionsFiveToSeven CosetGraphContext Stellmacher.Later
open scoped Pointwise

universe u

attribute [local instance] QuotientDihedralProduct.barL_group
  QuotientDihedralProduct.barL_finite

private theorem distance_one_stabilizer_intersection_le_coatom
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx) :
    z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) ≤ data.coatom := by
  classical
  have hneighbor : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hneighbor
  have hfirst : IsPGroup 2 (z ctx.Γ ctx.criticalPath.a) :=
    IsElementaryAbelian.isPGroup 2 _
  have hsecond : IsPGroup 2 (z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)) := by
    rw [z_act, inv_inv]
    exact hfirst.map _
  intro actor hactor
  by_contra houtside
  have hgen := data.actor_generated actor hactor.1 houtside
  have hclosure : Subgroup.closure ({actor} : Set G) ≤ z ctx.Γ ctx.criticalPath.a :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hactor.1)
  have hnormal : Subgroup.closure ({actor} : Set G) ≤
      Subgroup.normalizer (z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) : Set G) :=
    (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
      (stabilizer_le_normalizer_z ctx.Γ _ hactor.2))
  have hE : IsPGroup 2 data.E := by
    rw [hgen]
    exact (hfirst.to_le hclosure).to_sup_of_normal_right' hsecond hnormal
  have htop : (⊤ : Subgroup data.E) ≤ pCore 2 data.E :=
    le_sSup ⟨inferInstance, hE.to_subgroup ⊤⟩
  have hactorE : actor ∈ data.E := by
    rw [data.generated]
    exact (show z ctx.Γ ctx.criticalPath.a ≤ _ from le_sup_left) hactor.1
  have hactorCore : actor ∈ twoCoreIn data.E :=
    Subgroup.mem_map_of_mem data.E.subtype (htop (show (⟨actor, hactorE⟩ : data.E) ∈ ⊤ from trivial))
  exact houtside (data.coatom_eq.symm ▸ ⟨hactor.1, hactorCore⟩)

private theorem coatom_transfer_of_quotient_core_central
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneExtractionData ctx)
    (model : QuotientDihedralProduct data.E (q ctx.Γ ctx.criticalPath.a') data.coatom)
    (hcentral : pCore 2 model.barL ≤ Subgroup.center model.barL) :
    data.coatom = z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) := by
  classical
  have hforward : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  have hbackward : ctx.criticalPath.a ∈ neighborhood ctx.Γ ctx.criticalPath.a' := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact ctx.criticalPath.endpoint_distance.trans hb
  have h73 := lemma_seven_three ctx.sectionSeven ctx.Γ
  have hqfirst : q ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a := by
    rw [q, ctx.Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hfirst : z ctx.Γ ctx.criticalPath.a ≤ stabilizer ctx.Γ ctx.criticalPath.a :=
    (h73.center_core _ _ hforward).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans
        ((Subgroup.map_subtype_le _).trans hqfirst))
  have hcore : q ctx.Γ ctx.criticalPath.a' ≤ stabilizer ctx.Γ ctx.criticalPath.a :=
    (h73.sylow_and_core _ _ hbackward default).2.2
  have hmap : (pCore 2 data.E).map model.quotientMap ≤ pCore 2 model.barL :=
    le_sSup ⟨pCore_normal.map model.quotientMap model.quotient_surjective,
      pCore_isPGroup.map model.quotientMap⟩
  apply le_antisymm ?_ (distance_one_stabilizer_intersection_le_coatom ctx hb data)
  intro actor hactor
  have hactorBoth := data.coatom_eq ▸ hactor
  refine ⟨hactorBoth.1, ?_⟩
  obtain ⟨actorE, hactorE, heq⟩ := hactorBoth.2
  change (actorE : G) = actor at heq
  have hactorCentral := hcentral (hmap (Subgroup.mem_map_of_mem model.quotientMap hactorE))
  let xE : data.E := ⟨data.x, data.x_mem_E⟩
  have hcomm := Subgroup.mem_center_iff.mp hactorCentral (model.quotientMap xE)
  have hkernel : xE⁻¹ * actorE * xE * actorE⁻¹ ∈ model.quotientMap.ker := by
    apply MonoidHom.mem_ker.mpr
    simp only [map_mul, map_inv]
    rw [mul_assoc (model.quotientMap xE)⁻¹, ← hcomm]
    simp
  have hkernelCore := (model.quotient_kernel ▸ hkernel).2
  have hconj : data.x⁻¹ * actor * data.x ∈ stabilizer ctx.Γ ctx.criticalPath.a := by
    have hmul := (stabilizer ctx.Γ ctx.criticalPath.a).mul_mem
      (hcore hkernelCore) (hfirst hactorBoth.1)
    change (data.x⁻¹ * (actorE : G) * data.x * (actorE : G)⁻¹) * actor ∈
      stabilizer ctx.Γ ctx.criticalPath.a at hmul
    simpa only [heq, mul_assoc, inv_mul_cancel, mul_one] using hmul
  rw [stabilizer_act, inv_inv]
  exact ⟨data.x⁻¹ * actor * data.x, hconj, by
    change data.x * (data.x⁻¹ * actor * data.x) * data.x⁻¹ = actor
    group⟩

public theorem distance_one_coatom_eq_stabilizer_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) :
    ∃ data : DistanceOneExtractionData ctx,
      data.coatom = z ctx.Γ ctx.criticalPath.a ⊓
        stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) := by
  obtain ⟨data⟩ := distance_one_extraction ctx hb
  obtain ⟨model⟩ := data.quotient
  have hforward : ctx.criticalPath.a' ∈ neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [neighborhood, ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hforward
  let _ : IsMulCommutative data.coatom :=
    IsMulCommutative.of_setLike_mul_comm fun first hfirst second hsecond =>
      setLike_mul_comm (s := z ctx.Γ ctx.criticalPath.a)
        (data.coatom_eq ▸ hfirst).1 (data.coatom_eq ▸ hsecond).1
  let _ : IsMulCommutative model.barA0 := by
    rw [model.barA0_image]
    infer_instance
  exact ⟨data, coatom_transfer_of_quotient_core_central ctx hb data model
    (dihedralProduct_twoCore_le_center model.barL model.barA0 (model.p ^ model.n)
      model.p_odd.pow model.model)⟩

end Stellmacher.SectionNine
