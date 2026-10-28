module
public import Stellmacher.SectionNine.NineTenPredecessorNoncommutation
public import Stellmacher.SectionNine.NineTenDistanceTwoNeighborhood
public import Stellmacher.SectionNine.NineNineCommutatorBound

/-!
# The normal predecessor-intersection bound in (9.10)

Retain the original geometric extraction and its prescribed actor, together
with the first coatom on the same path. If C is normalized by the first
stabilizer and its commutator with the first residual lies in first V, then
C meets the extracted predecessor module inside first V.

The residual conjugator moves the third module to the predecessor and acts
trivially on C modulo first V. Thus the predecessor intersection is contained
in the third intersection joined with first V. The prescribed actor centralizes
the third module and normalizes first V, so its commutator with the predecessor
intersection lies in first V. Apply the actual (9.4), using the original actor,
residual conjugator and the established common-neighbor edge generation.

This proves Stellmacher (9.10)(11), printed p.59, for every subgroup with the
two properties of the source's maximal normal C. No additional condition on
critical length beyond the previous extraction is required.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement
universe u

public theorem nine_ten_normal_predecessor_intersection_le_first
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hactorNeighbor : actor ∈ ZAt ctx.Γ neighbor)
    (hactorComm : twoResidualIn E ≤ ⁅twoResidualIn E, Subgroup.zpowers actor⁆)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hfirstCoatom : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ GAt ctx.Γ neighbor) 2)
    (C : Subgroup G)
    (hCnormal : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (C : Set G))
    (hCE : ⁅C, EAt ctx.Γ ctx.criticalPath.firstStep⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep) :
    C ⊓ VAt ctx.Γ (ctx.Γ.act data.x⁻¹
      (ctx.criticalPath.path ⟨3, by omega⟩)) ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 4 < cp.length := hb
  have hshort : 1 < cp.length := by omega
  let third := cp.path ⟨3, by omega⟩
  let predecessor := Γ.act data.x⁻¹ third
  let K := C ⊓ VAt Γ predecessor
  let P := GAt Γ cp.firstStep
  let V := VAt Γ cp.firstStep
  have hthird : IsCriticalPathOffset Γ cp 3 third := ⟨⟨3, by omega⟩, rfl, rfl⟩
  obtain ⟨hdistance, hactorGeometry, hactorNotCore, hxComm, hxFirst⟩ :=
    nine_ten_prescribed_actor_geometry ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor hactorComm
  have hEnormal : P ≤ Subgroup.normalizer (EAt Γ cp.firstStep : Set G) := by
    change GAt Γ cp.firstStep ≤ Subgroup.normalizer (e Γ cp.firstStep : Set G)
    rw [CosetGraphContext.e, Γ.twoResidualAt_def]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (twoResidualIn_le _)).mp
      (twoResidualIn_normal _)
  have hxE : data.x ∈ EAt Γ cp.firstStep := by
    simpa only [inv_inv] using (EAt Γ cp.firstStep).inv_mem
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((Subgroup.zpowers_le.mpr hactorGeometry.1).trans hEnormal)) hxComm)
  have hxP : data.x ∈ P := by simpa only [inv_inv] using P.inv_mem hxFirst
  have hKjoin : K ≤ (C ⊓ VAt Γ third) ⊔ V := by
    intro k hk
    have hkV : k ∈ v Γ (Γ.act data.x⁻¹ third) := hk.2
    rw [v_act, inv_inv] at hkV
    obtain ⟨v, hv, heq⟩ := hkV
    have hvC : v ∈ C := (Subgroup.mem_normalizer_iff.mp (hCnormal hxP) v).mpr (by
      have hh : (MulAut.conj data.x) v ∈ C := heq ▸ hk.1
      exact hh)
    have hcomm : ⁅data.x, v⁆ ∈ V := hCE (by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hxE hvC)
    have hkEq : k = ⁅data.x, v⁆ * v := by
      rw [← heq]
      simp [MulAut.conj_apply, commutatorElement_def, mul_assoc]
    rw [hkEq]
    exact ((C ⊓ VAt Γ third) ⊔ V).mul_mem
      (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left ⟨hvC, hv⟩)
  have hQfirstP : QAt Γ cp.firstStep ≤ P := by
    rw [QAt, q, Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hVP : V ≤ P := (nine_seven_module_le_own_core ctx.toLocalContext hshort cp.firstStep).trans hQfirstP
  have hthirdP : VAt Γ third ≤ P :=
    (v_le_distance_two_neighborhood Γ
      ((Γ.distance_symm cp.firstStep third).trans hdistance)).trans
      ((nine_ten_distance_two_neighborhood_geometry ctx.toLocalContext hb).1.trans hQfirstP)
  let bound := nineNineCommutatorBound P (Subgroup.zpowers actor) V (stabilizer_le_normalizer_v Γ cp.firstStep)
  have hVbound : V ≤ bound := (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
    ⟨hVP, Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((Subgroup.zpowers_le.mpr hactorGeometry.1).trans (stabilizer_le_normalizer_v Γ cp.firstStep))⟩
  have hthirdBound : VAt Γ third ≤ bound := by
    apply (le_nineNineCommutatorBound_iff _ _ _ _ _).mpr
    refine ⟨hthirdP, ?_⟩
    have hzero : ⁅VAt Γ third, Subgroup.zpowers actor⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff.mp (Subgroup.zpowers_le.mpr hactorGeometry.2))
    exact hzero.le.trans bot_le
  have hKbound : K ≤ bound := hKjoin.trans (sup_le (inf_le_right.trans hthirdBound) hVbound)
  have hKcomm : ⁅K, Subgroup.zpowers actor⁆ ≤ V :=
    ((le_nineNineCommutatorBound_iff _ _ _ _ _).mp hKbound).2
  have hdisplacement := (nine_ten_prescribed_actor_first_transvection ctx hshort hterminalNot
    neighbor hneighbor hfirstCoatom actor hactorNeighbor hactorNotCore).2
  have hgeneration : ∀ n : Γ.Vertex,
      n ∈ Neighborhood Γ cp.firstStep → n ∈ Neighborhood Γ predecessor →
      (GAt Γ cp.firstStep ⊓ GAt Γ n) ⊔ Subgroup.zpowers actor = GAt Γ cp.firstStep :=
    nine_ten_prescribed_actor_common_neighbor_generation ctx.toLocalContext third second neighbor
      hthird hneighbor actor E A0 data hactorNeighbor
  exact lemma_nine_four_ambient ctx hshort third hdistance actor hactorGeometry
    data.x⁻¹ hxComm K inf_le_right hKcomm hgeneration hdisplacement

end Stellmacher.SectionNine
