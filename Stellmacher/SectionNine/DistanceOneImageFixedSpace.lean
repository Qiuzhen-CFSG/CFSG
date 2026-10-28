module
public import Stellmacher.SectionNine.DistanceOneLocalGeometry
public import Stellmacher.SectionNine.DistanceOneProductCenterIntersection

/-!
# The extracted product fixes exactly the two-center intersection

At critical distance one, the actual crossed product V fixes on the initial
vertex center precisely its intersection with the extracted conjugate center.
A fixed vector outside the first crossed factor would make V equal that
factor by source (2), contradicting source (4). A fixed vector inside the
factor lies in the center of V, identified with the two-center intersection
by source (3). This exposes the geometric fixed-space calculation shared by
the measure computation and the fixed-complement elimination in (9.1).

Source: Stellmacher, Journal of Algebra 190 (1997), pp.46–47, (9.1)(2)–(4),
refs/files/stellmacher-n-group.pdf. The context and extraction are unchanged;
no later faithful classification or core equality is assumed.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_product_fixed_space
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    z ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (V : Set G) =
      z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let Za := z Γ cp.a
  let C := Za ⊓ stabilizer Γ next
  let V := C ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  let I := Za ⊓ z Γ next
  change Za ⊓ Subgroup.centralizer (V : Set G) = I
  apply le_antisymm
  · intro z hz
    have hzC : z ∈ C := by
      by_contra hn
      have ha' : z ∉ data.coatom := by simpa only [data.coatom_stabilizer] using hn
      have hVz := distance_one_extracted_centralizer ctx hb data.toDistanceOneExtractionData
        z hz.1 ha'
      have hVC : V ≤ C := by
        intro v hv
        exact hVz.le ⟨hv,Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_iff.mp hz.2 v hv)⟩
      have hgeometry := (distance_one_local_geometry ctx hb data).2.2
      have hcore := distance_one_extracted_core_intersection ctx hb data.toDistanceOneExtractionData
      change V ⊓ q Γ cp.a = C at hcore
      change 4 * Nat.card (V ⊓ q Γ cp.a : Subgroup G) ≤ Nat.card V at hgeometry
      rw [hcore, le_antisymm hVC le_sup_left] at hgeometry
      have hp : 0 < Nat.card C := Nat.card_pos
      omega
    have hzcenter : z ∈ (Subgroup.center V).map V.subtype := by
      refine ⟨⟨z,Subgroup.mem_sup_left hzC⟩,Subgroup.mem_center_iff.mpr ?_,rfl⟩
      intro v
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hz.2 v v.property)
    exact (distance_one_product_center_eq_intersection ctx hb data).le hzcenter
  · intro z hz
    have hzcenter := (distance_one_product_center_eq_intersection ctx hb data).ge hz
    obtain ⟨v,hv,rfl⟩ := hzcenter
    refine ⟨hz.1,Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hv ⟨x,hx⟩)
end Stellmacher.SectionNine
