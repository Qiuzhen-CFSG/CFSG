module
public import Stellmacher.SectionNine.DistanceOneCentralThompsonFixedComplement
public import Stellmacher.SectionNine.DistanceOneNativeFixedIntersection
public import Stellmacher.SectionNine.DistanceOneRelativeEdgeGeneration
public import Stellmacher.SectionNine.NineThreeBaumannFixedGeneration

/-!
# The actual distance-one relative fixed complement is trivial

For the original ambient context at distance one and its supplied extraction
and faithful quotient witness, F=[O₂′(bar G_a),image V] fixes no nonidentity
element of the initial center. The statement keeps the actual image V and
its inherited action; no faithful classification or local conclusion is an
input.

The geometric containment places the fixed complement in the two-center
intersection, hence in the centralizer of the extracted generating group.
If the native Thompson subgroup centralizes the initial center, the separate
invariant-seed argument proves triviality. Otherwise the genuine native
Baumann factor decomposition supplies a nonidentity vector fixed by both F
and the Baumann subgroup. The (6.4) generating-centralizer consequence puts
that vector in the next center, so the entire edge fixes it. The exact
relative-commutator-plus-edge generation theorem now makes the whole initial
stabilizer fix it, contradicting its trivial center from (7.5).

These two branches complete the fixed-complement elimination between
Stellmacher (9.1)(7) and (8), Journal of Algebra 190 (1997), p.47,
refs/files/stellmacher-n-group.pdf. The centralizing branch explicitly handles
the case where the action-defined offender subgroup may be trivial.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix Subgroup
universe u
private theorem fixed_complement_bot_of_thompson_not_centralizes
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a))
    (hJ : ¬ elementaryAbelianMaxJ T ≤ centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    FixedPoints.subgroup (⁅SectionOne.oddCore w.X,X⁆ : Subgroup w.X)
      (ZAt ctx.Γ ctx.criticalPath.a) = ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let next := Γ.act data.x⁻¹ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let X := (V.subgroupOf P).map w.projection
  let F := ⁅SectionOne.oddCore w.X,X⁆
  let Y := (FixedPoints.subgroup F Za).map Za.subtype
  change FixedPoints.subgroup F Za = ⊥
  by_contra hfix
  let _ : (SectionOne.oddCore w.X).Normal := pPrimeCore_normal
  have hF : F ≤ SectionOne.oddCore w.X := commutator_le_left _ _
  have hYne := distance_one_odd_fixed_inf_baumann_ne_bot ctx hJ w F hF hfix
  have hYI : Y ≤ z Γ cp.a ⊓ z Γ next := distance_one_relative_fixed_complement_le_intersection ctx hb data w
  have hstep : cp.a' = cp.firstStep := by
    rw [← cp.path_end,← cp.path_first]
    congr 1
    exact Fin.ext hb
  have hYcent : Y ≤ centralizer (data.E : Set G) := by
    intro y hy
    obtain ⟨yn,hyn,rfl⟩ := data.intersection_central (hYI hy)
    exact mem_centralizer_iff.mpr fun e he => congrArg Subtype.val
      ((mem_center_iff.mp hyn) ⟨e,he⟩)
  have hYZ : Y ⊓ centralizer (baumannIn T : Set G) ≤ ZAt Γ cp.firstStep := by
    intro y hy
    apply nine_three_baumann_fixed_generation ctx hJ data.E
      (by
        change data.E ⊔ (GAt Γ cp.a ⊓ GAt Γ cp.firstStep) = GAt Γ cp.firstStep
        rw [← hstep]
        exact data.edge_generated)
    exact ⟨⟨map_subtype_le _ hy.1,hy.2⟩,hYcent hy.1⟩
  obtain ⟨y0,hy0ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hYne
  let y : G := y0
  have hy : y ∈ Y ⊓ centralizer (baumannIn T : Set G) := y0.property
  have hyne : y ≠ 1 := fun he => hy0ne (Subtype.ext he)
  obtain ⟨yn,hyn,he⟩ := hy.1
  have hyZ : y ∈ ZAt Γ cp.firstStep := hYZ hy
  have hycent : y ∈ centralizer (GAt Γ cp.firstStep : Set G) := by
    have hn := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).next_center
    rw [show ZAt Γ cp.firstStep = omegaOneCenter (GAt Γ cp.firstStep) from hn.2] at hyZ
    exact (omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _) hyZ
  let edge := GAt Γ cp.a ⊓ GAt Γ cp.a'
  let edgebar := (edge.subgroupOf P).map w.projection
  have hEdgefix : edgebar ≤ fixingSubgroup w.X ({yn} : Set Za) := by
    rintro a ⟨a0,ha0,rfl⟩
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hvyn : v = yn := Set.mem_singleton_iff.mp hv
    subst v
    apply Subtype.ext
    change ((w.action (w.projection a0)) yn : G) = yn
    rw [w.action_compatible]
    have hamem : (a0 : G) ∈ GAt Γ cp.firstStep := hstep ▸ ha0.2
    have hacomm := mem_centralizer_iff.mp hycent (a0 : G) hamem
    change (yn : G) = y at he
    rw [he,hacomm,mul_inv_cancel_right]
  have hFfix : F ≤ fixingSubgroup w.X ({yn} : Set Za) := by
    intro f hf
    rw [mem_fixingSubgroup_iff]
    intro v hv
    rw [Set.mem_singleton_iff.mp hv]
    exact hyn ⟨f,hf⟩
  have hfull := distance_one_relative_commutator_sup_edge ctx hb data w
  change F ⊔ edgebar = ⊤ at hfull
  have htop : (⊤ : Subgroup w.X) ≤ fixingSubgroup w.X ({yn} : Set Za) :=
    hfull ▸ sup_le hFfix hEdgefix
  have hcenter : (⟨y,w.module_le (he ▸ yn.property)⟩ : P) ∈ Subgroup.center P := by
    rw [mem_center_iff]
    intro p
    apply Subtype.ext
    have hfixp := (mem_fixingSubgroup_iff (M := w.X) (s := ({yn} : Set Za))).mp (htop (mem_top (w.projection p))) yn (Set.mem_singleton yn)
    have hh := congrArg Subtype.val hfixp
    change ((w.action (w.projection p)) yn : G) = yn at hh
    rw [w.action_compatible] at hh
    change (yn : G) = y at he
    rw [he] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hzbot := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).start_center_trivial
  rw [hzbot] at hcenter
  exact hyne (congrArg Subtype.val hcenter)

public theorem distance_one_relative_fixed_complement_trivial
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    FixedPoints.subgroup (⁅SectionOne.oddCore w.X,X⁆ : Subgroup w.X)
      (ZAt ctx.Γ ctx.criticalPath.a) = ⊥ := by
  classical
  by_cases hJ : elementaryAbelianMaxJ T ≤ centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)
  · exact distance_one_fixed_complement_bot_of_thompson_centralizes ctx hb data w hJ
  · exact fixed_complement_bot_of_thompson_not_centralizes ctx hb data w hJ
end Stellmacher.SectionNine
