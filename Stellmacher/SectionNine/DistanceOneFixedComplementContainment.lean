module
public import Stellmacher.SectionNine.DistanceOneImagePreparation
public import Stellmacher.SectionNine.DistanceOneImageMinimality
public import Stellmacher.SectionOne.RelativeCommutatorCover
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.NormalizingFixedPoints

/-!
# The relative odd fixed complement lies in the two-center intersection

For the original distance-one ambient context and actual extraction, the
fixed subgroup of F=[O₂′(bar G_a),image V] on Z_a lies in Z_a∩Z_next.
The same supplied faithful quotient witness and its action are used.

The actual image is elementary of measure two, minimal on its nontrivial
subgroups, and nonquadratic by source (5). The bounded relative commutator
cover puts [Z_a,image V] inside [Z_a,F]. Since F has odd order and is normalized
by image V, its coprime fixed complement is invariant under image V. Each
image-V action difference lies in both complementary subgroups, so vanishes.
The geometric fixed-space theorem identifies the resulting fixed space with
the actual center intersection.

This is the first fixed-complement reduction after Stellmacher (9.1)(7),
Journal of Algebra 190 (1997), p.47, refs/files/stellmacher-n-group.pdf.
No Sylow normality of V or ambient normality of F is assumed.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
private theorem fixed_le_of_coprime_commutator_cover
    {G V : Type*} [Group G] [Group V] [Finite G] [Finite V]
    [IsMulCommutative V] [MulDistribMulAction G V]
    (F X : Subgroup G) (hn : X ≤ Subgroup.normalizer (F : Set G))
    (hcop : Nat.Coprime (Nat.card F) (Nat.card V))
    (hcover : commutatorAction X V ≤ commutatorAction F V) :
    FixedPoints.subgroup F V ≤ FixedPoints.subgroup X V := by
  let C := FixedPoints.subgroup F V
  let _ : IsInvariant X V C := fixedPoints_isInvariant_of_normalizing_actor X F hn
  have hc : IsCompl C (commutatorAction F V) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun x y => IsMulCommutative.is_comm.comm x y)
      hcop inferInstance
  intro v hv x
  have hd : v⁻¹ * (x • v) ∈ commutatorAction F V := by
    apply hcover
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨x,v,rfl⟩
  have hdC : v⁻¹ * (x • v) ∈ C := C.mul_mem (C.inv_mem hv)
    ((IsInvariant.invariant (A := X) (G := V) (H := C) x v).mp hv)
  exact (inv_mul_eq_one.mp (hc.disjoint.le_bot ⟨hdC,hd⟩)).symm

public theorem distance_one_relative_fixed_complement_le_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    let F := ⁅SectionOne.oddCore w.X,X⁆
    (FixedPoints.subgroup F (ZAt ctx.Γ ctx.criticalPath.a)).map
      (ZAt ctx.Γ ctx.criticalPath.a).subtype ≤
      z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let X := (V.subgroupOf P).map w.projection
  let F := ⁅SectionOne.oddCore w.X,X⁆
  change (FixedPoints.subgroup F Za).map Za.subtype ≤ z Γ cp.a ⊓ z Γ next
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hsetup := SectionEight.local_quotient_sylow_action_setup ctx.sectionSeven Γ cp w
  have hX := distance_one_image_elementary ctx data w
  have hmeasure := distance_one_image_m_two ctx hb data w
  have hmin : ∀ Y : Subgroup w.X, Y ≤ X → Y ≠ ⊥ →
      SectionOne.m (V := Za) X ≤ SectionOne.m (V := Za) Y := by
    intro Y hYX hYne
    rw [hmeasure.2]
    exact distance_one_image_m_minimal ctx hb data w Y hYX hYne
  have hnon : commutatorAction₂ X Za ≠ ⊥ := by
    intro hquad
    have hsmall := distance_one_quadratic_image_card_le_two ctx hb data w X le_rfl hquad
    have hlarge : 4 ≤ Nat.card X := hmeasure.1
    omega
  have hcover := SectionOne.relative_commutator_le_oddCore_of_m_two_nonquadratic
    hsetup.1 X hX hmeasure.1 hmeasure.2 hmin hnon
  let _ : (SectionOne.oddCore w.X).Normal := pPrimeCore_normal
  have hFW : F ≤ SectionOne.oddCore w.X := Subgroup.commutator_le_left _ _
  have hcop : Nat.Coprime (Nat.card F) (Nat.card Za) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 Za).exists_card_eq
    rw [hn]
    exact ((pPrimeCore_coprime_card (p := 2) (G := w.X)).of_dvd_right
      (Subgroup.card_dvd_of_le hFW)).symm.pow_right n
  have hfix := fixed_le_of_coprime_commutator_cover F X
    (Subgroup.normalizer_commutator_ge_right _ _) hcop hcover
  have hVP : V ≤ P :=
    (distance_one_product_factors Γ cp.a next).2.2.1.trans inf_le_left
  have hm := Subgroup.map_mono (f := Za.subtype) hfix
  rw [w.fixedPoints_map_subtype V hVP, distance_one_product_fixed_space ctx hb data] at hm
  exact hm
end Stellmacher.SectionNine
