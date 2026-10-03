module
public import Stellmacher.SectionNine.DistanceOneLocalGeometry
public import Stellmacher.SectionNine.DistanceOneProductCenter
public import Theory.GroupTheory.ElementaryEightPairQuaternionRecognition

/-!
# The actual extracted product is a quaternion central product

For the original ambient context at critical distance one, the explicit
faithful conclusion and actual extraction/action witness imply that its exact
two-factor product is a central product of quaternion eights. The theorem
preserves the supplied conjugator and extraction; it does not identify this
product with Vstar or assume the later local conclusion.

The proved local geometry supplies source (3) and the cardinal inequality in
(4). The subgroup cardinal-index identity converts the latter to the relative
index bound needed by the product-center theorem. That theorem gives both
factors order8 and the native product center order2. Each factor is elementary
because it lies in an actual elementary vertex center, with the second center
transported by the supplied graph conjugator.

Restrict the two factors to their exact join and apply the intrinsic
single-normalization quaternion recognition theorem. Map its quaternion
subgroups back through the join's injective subtype. This preserves models,
join, intersection order, and pairwise commutation. An element of their
intersection commutes with both generating factors, so lies in the ambient
image of the product center, supplying the final exact predicate field.

Source: Stellmacher (9.1), after relation(11), Journal of Algebra190 (1997),
p.48, with the structural geometry of relations(3) and(4) proved upstream.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
universe u

/-- The exact extracted distance-one product has the intended quaternion
central-product structure, with no remaining source-relation assumptions. -/
public theorem distance_one_extracted_quaternion_product
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (data : DistanceOneActionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    IsCentralProductQ8Q8 ((z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  have hgeom := distance_one_local_geometry ctx hb data
  have hfour : 4 ≤ (V ⊓ q Γ cp.a).relIndex V := by
    have hh := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (V ⊓ q Γ cp.a) V bot_le inf_le_left
    simp only [Subgroup.relIndex_bot_left] at hh
    have hpos : 0 < Nat.card (V ⊓ q Γ cp.a : Subgroup G) := Nat.card_pos
    have hbound : 4 * Nat.card (V ⊓ q Γ cp.a : Subgroup G) ≤ Nat.card V := hgeom.2.2
    nlinarith
  obtain ⟨hcenter, hzcard, hCcard, hDcard, _⟩ := distance_one_extracted_product_center_card
    ctx hb hfaith data.toDistanceOneExtractionData data.coatom_stabilizer hfour hgeom.1
  change Nat.card C = 8 at hCcard
  change Nat.card D = 8 at hDcard
  change (Subgroup.center V).map V.subtype = z Γ cp.a' at hcenter
  have hVcenter : Nat.card (Subgroup.center V) = 2 := by
    rw [← Subgroup.card_map_of_injective V.subtype_injective, hcenter]
    exact hzcard
  have hneighbor : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  let : IsElementaryAbelian 2 (z Γ cp.a) := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  have hZc : z Γ next = (z Γ cp.a).conjBy data.x := by
    dsimp only [next]
    rw [z_act, inv_inv]
    rfl
  let : IsElementaryAbelian 2 (z Γ next) := by
    rw [hZc]
    exact IsElementaryAbelian.map (MulAut.conj data.x).toMonoidHom
  have elementary_subgroup (X Y : Subgroup G) (hXY : X ≤ Y)
      [IsElementaryAbelian 2 Y] : IsElementaryAbelian 2 X := {
    toIsMulCommutative := IsMulCommutative.of_setLike_mul_comm (fun a ha b hb =>
      setLike_mul_comm (hXY ha) (hXY hb))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Y) (x : G) (hXY x.property))) }
  let : IsElementaryAbelian 2 C := elementary_subgroup C _ inf_le_left
  let : IsElementaryAbelian 2 D := elementary_subgroup D _ inf_le_left
  let Cn := C.subgroupOf V
  let Dn := D.subgroupOf V
  have hCV : C ≤ V := le_sup_left
  have hDV : D ≤ V := le_sup_right
  have hCn : IsElementaryAbelian 2 Cn := IsElementaryAbelian.subgroupOf hCV
  have hDn : IsElementaryAbelian 2 Dn := IsElementaryAbelian.subgroupOf hDV
  have hCncard : Nat.card Cn = 8 := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCV).toEquiv).trans hCcard
  have hDncard : Nat.card Dn = 8 := (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDV).toEquiv).trans hDcard
  have hgen : Cn ⊔ Dn = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hCV hDV]
    exact Subgroup.subgroupOf_self V
  have hn : Cn ≤ Subgroup.normalizer (Dn : Set V) := by
    have hnorm : C ≤ Subgroup.normalizer (D : Set G) := (distance_one_product_factors Γ cp.a next).1
    exact (Subgroup.subgroupOf_mono V hnorm).trans (Subgroup.le_normalizer_comap V.subtype)
  obtain ⟨L, R, hL, hR, hLR, hinter, hcomm⟩ := exists_quaternion_factors_of_elementary_eights
    Cn Dn hCn hDn hCncard hDncard hgen hn hVcenter
  let Lg := L.map V.subtype
  let Rg := R.map V.subtype
  have hLg : IsModel Lg Q8 := by
    obtain ⟨eL⟩ := hL
    exact ⟨(L.equivMapOfInjective V.subtype V.subtype_injective).symm.trans eL⟩
  have hRg : IsModel Rg Q8 := by
    obtain ⟨eR⟩ := hR
    exact ⟨(R.equivMapOfInjective V.subtype V.subtype_injective).symm.trans eR⟩
  have hjoin : V = Lg ⊔ Rg := by
    rw [← Subgroup.map_sup, hLR, ← MonoidHom.range_eq_map, V.range_subtype]
  have hinter : Nat.card (Lg ⊓ Rg : Subgroup G) = 2 := by
    rw [← Subgroup.map_inf L R V.subtype V.subtype_injective,
      Subgroup.card_map_of_injective V.subtype_injective, hinter]
  refine ⟨Lg, Rg, hLg, hRg, hjoin, hinter, ?_, ?_⟩
  · rintro l ⟨ll, hl, rfl⟩ r ⟨rr, hr, rfl⟩
    exact congrArg Subtype.val (hcomm ll hl rr hr)
  · intro x hx
    have hxmap : x ∈ (L ⊓ R).map V.subtype := by
      rw [Subgroup.map_inf L R V.subtype V.subtype_injective]
      exact hx
    obtain ⟨xx, hxx, rfl⟩ := hxmap
    refine ⟨xx, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro y
    have hle : L ⊔ R ≤ Subgroup.centralizer ({xx} : Set V) := by
      apply sup_le
      · intro l hl
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm l hl xx hxx.2)
      · intro r hr
        exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm xx hxx.1 r hr).symm
    rw [hLR] at hle
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))

end Stellmacher.SectionNine
