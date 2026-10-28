module
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Stellmacher.SectionNine.DistanceOneSmallQuotient
public import Stellmacher.ResidualQuadraticCore

/-!
# Distance-one local geometry through Stellmacher (9.1)(4)

For any actual distance-one extraction data, the center of the crossed
product V is centralized by O^2(E), its order exceeds four times the common
center intersection V0, and V intersect Q_alpha has index at least four.
The same conjugator, coatom, generated subgroup and action data are retained.

The center-residual companion proves (3) from the actual (7.5) central
omega-center data, (3.5), and P×Q. If V were abelian, (3) would make the
action of O^2(E) on Q_beta quadratic, since (1) puts [Q_beta,E] in V.
The residual quadratic core theorem then makes E a two-group, contradicting
the extracted index-two coatom Za intersect O2(E). Thus V is nonabelian.
The small-quotient companion uses the genuine E-action and swapping
conjugator to show that |V|≤4|V0| would force commutativity, giving the
strict bound. Finally the factors C,D are conjugate elementary two-groups.
The product-order formula gives |V|=|C|[C:V0], and the strict bound forces
this power-of-two index to be at least four. Relation (2) identifies C with
V intersect Q_alpha and supplies the final bound.

Source: Stellmacher, Journal of Algebra 190 (1997), proof of (9.1), p.46,
relations (3)–(4), in refs/files/stellmacher-n-group.pdf. No faithful-action,
local-recognition, core-equality, or later numbered conclusion is an input.
The isolated dihedral small-quotient example is excluded by the real
extracted E-action, rather than by involution generation alone.
-/

namespace Stellmacher.SectionNine
open Stellmacher.SectionsFiveToSeven CosetGraphContext Stellmacher.Later
open Stellmacher.SectionsFiveToSeven.SevenSix
universe u

public theorem distance_one_local_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    let V := C ⊔ D
    let V0 := z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next
    ⁅(Subgroup.center V).map V.subtype,twoResidualIn data.E⁆ = ⊥ ∧
      4 * Nat.card V0 < Nat.card V ∧
      4 * Nat.card (V ⊓ q ctx.Γ ctx.criticalPath.a : Subgroup G) ≤ Nat.card V := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let V0 := z Γ cp.a ⊓ z Γ next
  have h3 := distance_one_extracted_center_residual ctx hb data
  change ⁅(Subgroup.center V).map V.subtype,twoResidualIn data.E⁆ = ⊥ at h3
  change _ ∧ 4 * Nat.card V0 < Nat.card V ∧ _
  refine ⟨h3,?_⟩
  have hlen : cp.length = 1 := hb
  have hstep : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1,by omega⟩ := cp.path_first.symm
      _ = cp.path ⟨cp.length,Nat.lt_succ_self _⟩ := by congr 1; apply Fin.ext; exact hb.symm
      _ = cp.a' := cp.path_end
  have hnot : ¬ IsMulCommutative V := by
    intro habelian
    let _ := habelian
    have hcenter : (Subgroup.center V).map V.subtype = V := by
      rw [Subgroup.center_eq_top,← MonoidHom.range_eq_map,Subgroup.range_subtype]
    have hVR : ⁅V,twoResidualIn data.E⁆ = ⊥ := by rwa [hcenter] at h3
    let P := stabilizer Γ cp.a'
    have hPchar : IsCharacteristicTwoType P := by
      simpa only [hstep] using (edge_characteristic_data ctx.sectionSeven Γ cp).2
    have hPsolv : Group.IsSolvable P := by
      change Group.IsSolvable (stabilizer Γ cp.a')
      rw [← hstep]
      exact (edge_local_data ctx.sectionSeven Γ cp).2.2
    have hEsolv : Group.IsSolvable data.E := by
      let _ := hPsolv
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective data.E_le)
    have hcore : twoCoreAmbient P = q Γ cp.a' := by rw [q,Γ.twoCoreAt_def]; rfl
    have hQRV : ⁅twoCoreAmbient P,twoResidualAmbient data.E⁆ ≤ V := by
      rw [hcore]
      exact (Subgroup.commutator_mono le_sup_right (Subgroup.map_subtype_le _)).trans data.product_action
    have hquad : ⁅⁅twoCoreAmbient P,twoResidualAmbient data.E⁆,twoResidualAmbient data.E⁆ = ⊥ :=
      bot_unique ((Subgroup.commutator_mono hQRV le_rfl).trans_eq hVR)
    have hEp := isPGroup_of_residual_quadratic_on_core P data.E data.E_le hEsolv hPchar hquad
    have hEcore : twoCoreIn data.E = data.E := by
      have hp : pCore 2 data.E = ⊤ := top_unique (le_sSup ⟨inferInstance,
        hEp.to_subgroup (⊤ : Subgroup data.E)⟩)
      rw [twoCoreIn,hp,← MonoidHom.range_eq_map,Subgroup.range_subtype]
    have hfirstE : z Γ cp.a ≤ data.E := by rw [data.generated]; exact le_sup_left
    have hcoatom : data.coatom = z Γ cp.a := by
      rw [data.coatom_eq,hEcore,inf_eq_left.mpr hfirstE]
    have hc := data.coatom_card
    change Nat.card (z Γ cp.a) = 2 * Nat.card data.coatom at hc
    rw [hcoatom] at hc
    have hpos : 0 < Nat.card (z Γ cp.a) := Nat.card_pos
    omega
  have hstrict : 4 * Nat.card V0 < Nat.card V := by
    by_contra hn
    exact hnot (distance_one_product_abelian_of_small_quotient ctx hb data (by change Nat.card V ≤ 4 * Nat.card V0; omega))
  refine ⟨hstrict,?_⟩
  have hgeometry := distance_one_product_factors Γ cp.a next
  have hCD : C ⊓ D = V0 := hgeometry.2.2.2.2
  have hswap := (distance_one_factor_transport ctx hb data.toDistanceOneExtractionData).1
  change C.map (MulAut.conj data.x).toMonoidHom = D at hswap
  have hcardCD : Nat.card C = Nat.card D := by
    rw [← hswap,Subgroup.card_map_of_injective (MulAut.conj data.x).injective]
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes C D hgeometry.2.1
  rw [hCD] at hprod
  change Nat.card C * Nat.card D = Nat.card V0 * Nat.card V at hprod
  have hneigh : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood,Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneigh
  have hCp : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2 (z Γ cp.a)).to_le inf_le_left
  obtain ⟨k,hk⟩ := hCp.index ((C ⊓ D).subgroupOf C)
  change (C ⊓ D).relIndex C = 2 ^ k at hk
  have hmul := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (C ⊓ D) C bot_le inf_le_left
  simp only [Subgroup.relIndex_bot_left] at hmul
  rw [hk,hCD] at hmul
  have hpos : 0 < Nat.card V0 := Nat.card_pos
  have hk2 : 2 ≤ k := by
    by_contra hn
    have hklt : k < 2 := by omega
    interval_cases k <;> norm_num at hmul <;> nlinarith [hstrict]
  have hpow : 4 ≤ 2 ^ k := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk2
  have hVcard : Nat.card V = Nat.card C * 2 ^ k := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc
      Nat.card V0 * Nat.card V = Nat.card C * Nat.card D := hprod.symm
      _ = Nat.card C * Nat.card C := by rw [← hcardCD]
      _ = Nat.card C * (Nat.card V0 * 2 ^ k) := by rw [hmul]
      _ = Nat.card V0 * (Nat.card C * 2 ^ k) := by ac_rfl
  have hcore := distance_one_extracted_core_intersection ctx hb data.toDistanceOneExtractionData
  change V ⊓ q Γ cp.a = C at hcore
  change 4 * Nat.card (V ⊓ q Γ cp.a : Subgroup G) ≤ Nat.card V
  rw [hcore,hVcard]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Nat.card C) hpow
end Stellmacher.SectionNine
