module
public import Stellmacher.SectionNine.DistanceOneQuadraticImage
public import Stellmacher.SectionNine.DistanceOneLocalGeometry
public import Stellmacher.SectionNine.DistanceOneImageFixedSpace

/-!
# Elementary image of the extracted product in (9.1)

For any faithful quotient witness on the actual initial center, the image
of the cross-center product V is elementary abelian. Its first factor lies
in the initial center and is killed by the quotient projection. Its second
factor lies in a conjugate of that elementary center. The image of V equals
the image of this second factor, so elementary abelianness descends through
the exact supplied projection. At distance one, the image has order at least
four and its Section One measure is two. Source (2) identifies the action
kernel on V with the first factor C; source (3) identifies the center of V
with the factor intersection I. A fixed initial-center vector outside C
would make V=C, contrary to (4), so the fixed subgroup is exactly I.
Equal factor cardinalities, their product-order formula and the coatom
index two give |I||image V|=|C| and |Za|=2|C|, hence m(image V)=2.
No faithful-classification or local-core conclusion is an extra premise.

This prepares the actor in Stellmacher (9.1), relations (5)–(7), journal
pp.46–47 of refs/files/stellmacher-n-group.pdf. The module/action witness
and the original cross-center factors are retained throughout.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_image_elementary
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    IsElementaryAbelian 2 ((V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let Zc := ZAt Γ next
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let _ := w.groupX
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hnext : Zc = Za.map (MulAut.conj data.x).toMonoidHom := by
    change z Γ (Γ.act data.x⁻¹ cp.a) = _
    rw [z_act, inv_inv]
  let _ : IsElementaryAbelian 2 Zc := by
    rw [hnext]
    exact IsElementaryAbelian.map (MulAut.conj data.x).toMonoidHom
  let _ : IsElementaryAbelian 2 D := {
    toIsMulCommutative := .of_setLike_mul_comm fun _ hx _ hy =>
      setLike_mul_comm (s := Zc) hx.1 hy.1
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun d =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := Zc) d d.property.1) }
  have hfactors := distance_one_product_factors Γ cp.a next
  have hCP : C ≤ P := le_sup_left.trans (hfactors.2.2.1.trans inf_le_left)
  have hDP : D ≤ P := inf_le_right
  have hCker : C.subgroupOf P ≤ w.projection.ker := by
    intro x hx
    rw [w.kernel_eq]
    exact ⟨x.property, Subgroup.le_centralizer Za hx.1⟩
  have hmap : ((C ⊔ D).subgroupOf P).map w.projection = (D.subgroupOf P).map w.projection := by
    rw [Subgroup.subgroupOf_sup hCP hDP, Subgroup.map_sup,
      (Subgroup.map_eq_bot_iff _).mpr hCker, bot_sup_eq]
  change IsElementaryAbelian 2 (((C ⊔ D).subgroupOf P).map w.projection)
  rw [hmap]
  let _ : IsElementaryAbelian 2 (D.subgroupOf P) := IsElementaryAbelian.subgroupOf hDP
  exact IsElementaryAbelian.map w.projection
public theorem distance_one_image_m_two
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
    4 ≤ Nat.card X ∧ SectionOne.m (V := ZAt ctx.Γ ctx.criticalPath.a) X = 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let I := z Γ cp.a ⊓ z Γ next
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let X := (V.subgroupOf P).map w.projection
  change 4 ≤ Nat.card X ∧ SectionOne.m (V := Za) X = 2
  have hfactors := distance_one_product_factors Γ cp.a next
  have hVP : V ≤ P := hfactors.2.2.1.trans inf_le_left
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hCcard : Nat.card Za = 2 * Nat.card C := by
    simpa only [data.coatom_stabilizer] using data.coatom_card
  have hnotC : ¬ Za ≤ C := by
    intro hle
    have heq : C = Za := le_antisymm inf_le_left hle
    rw [heq] at hCcard
    have hp : 0 < Nat.card Za := Nat.card_pos
    omega
  obtain ⟨a,ha,hout⟩ := SetLike.not_le_iff_exists.mp hnotC
  have haout : a ∉ data.coatom := by simpa only [data.coatom_stabilizer] using hout
  have hVa := distance_one_extracted_centralizer ctx hb data.toDistanceOneExtractionData a ha haout
  have hkernel : V ⊓ Subgroup.centralizer (Za : Set G) = C := by
    apply le_antisymm
    · exact (inf_le_inf_left V (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr ha))).trans hVa.le
    · exact le_inf le_sup_left (inf_le_left.trans (Subgroup.le_centralizer Za))
  have hcent : Za ⊓ Subgroup.centralizer (V : Set G) = I :=
    distance_one_product_fixed_space ctx hb data
  have hfixedcard : Nat.card (FixedPoints.subgroup X Za) = Nat.card I := by
    rw [w.fixedPoints_card V hVP,hcent]
  have hkerindex : C.relIndex V = Nat.card X := by
    rw [← Subgroup.relIndex_ker]
    have hker : (V.subgroupOf P) ⊓ w.projection.ker = C.subgroupOf P := by
      rw [w.kernel_eq]
      ext v
      change (v.val ∈ V ∧ v.val ∈ P ∧ v.val ∈ Subgroup.centralizer (Za : Set G)) ↔ v.val ∈ C
      constructor
      · rintro ⟨hv,_,hc⟩
        exact hkernel.le ⟨hv,hc⟩
      · intro hv
        exact ⟨Subgroup.mem_sup_left hv,v.property,hkernel.ge hv |>.2⟩
    conv_rhs => rw [← Subgroup.inf_relIndex_right, inf_comm, hker,
      Subgroup.relIndex_subgroupOf hVP]
  have hmul : Nat.card C * Nat.card X = Nat.card V := by
    have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) C V bot_le le_sup_left
    simpa only [Subgroup.relIndex_bot_left,hkerindex] using h
  have hfour : 4 ≤ Nat.card X := by
    have hgeometry := (distance_one_local_geometry ctx hb data).2.2
    have hcore := distance_one_extracted_core_intersection ctx hb data.toDistanceOneExtractionData
    change V ⊓ q Γ cp.a = C at hcore
    change 4 * Nat.card (V ⊓ q Γ cp.a : Subgroup G) ≤ Nat.card V at hgeometry
    rw [hcore, ← hmul] at hgeometry
    have hp : 0 < Nat.card C := Nat.card_pos
    nlinarith
  have hCD : Nat.card C = Nat.card D := by
    have hs := (distance_one_factor_transport ctx hb data.toDistanceOneExtractionData).1
    change C.map (MulAut.conj data.x).toMonoidHom = D at hs
    rw [← hs, Subgroup.card_map_of_injective (MulAut.conj data.x).injective]
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes C D hfactors.2.1
  rw [hfactors.2.2.2.2] at hprod
  change Nat.card C * Nat.card D = Nat.card I * Nat.card V at hprod
  have hIX : Nat.card I * Nat.card X = Nat.card C := by
    rw [← hCD, ← hmul] at hprod
    have hp : 0 < Nat.card C := Nat.card_pos
    nlinarith
  refine ⟨hfour,?_⟩
  unfold SectionOne.m
  rw [hfixedcard]
  have hIpos : 0 < Nat.card I := Nat.card_pos
  have hXpos : 0 < Nat.card X := Nat.card_pos
  apply (div_eq_iff (by positivity : (Nat.card I : ℚ) * Nat.card X ≠ 0)).mpr
  have hcast : (Nat.card I : ℚ) * Nat.card X = Nat.card C := by exact_mod_cast hIX
  rw [hcast]
  exact_mod_cast hCcard

end Stellmacher.SectionNine

