module
public import Stellmacher.SectionNine.DistanceOneCenterResidual
public import Stellmacher.TwoResidualConjugator
public import Theory.GroupTheory.FixedProductCenter

/-!
# The center of the extracted product is the vertex-center intersection

For the actual distance-one action data, the center of the product of the
two cross intersections is exactly the intersection of the two vertex
centers. The extraction is unchanged, and no faithful-action conclusion
or cardinality hypothesis is required.

A residual conjugator carries the first elementary vertex center to its
extracted conjugate. Relation (1) makes that conjugator normalize the
product, so it also carries the first cross factor to the second. The
proved relation (3) makes it fix the product center pointwise. The
fixed-product-center theorem therefore identifies the center with the
factor intersection, which equals the vertex-center intersection by the
initial product geometry.

Source: Stellmacher, Journal of Algebra190 (1997), pp.46–47 / PDF36–37,
`refs/files/stellmacher-n-group.pdf`, proof of (9.1), relation (6), using
the fixed-center reduction of (1.5).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
public theorem distance_one_product_center_eq_intersection
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    (Subgroup.center (C ⊔ D : Subgroup G)).map (C ⊔ D).subtype =
      z ctx.Γ ctx.criticalPath.a ⊓ z ctx.Γ next := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let Za := z Γ cp.a
  let Zc := z Γ next
  let C := Za ⊓ stabilizer Γ next
  let D := Zc ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  have hgeom := distance_one_product_factors Γ cp.a next
  have hthree := distance_one_extracted_center_residual ctx hb data
  have hforward : cp.a' ∈ neighborhood Γ cp.a := by
    rw [neighborhood, Γ.neighbors_def]
    exact (Γ.distance_symm _ _).trans (cp.endpoint_distance.trans hb)
  let _ := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hforward
  have hZc : Zc = Za.conjBy data.x := by
    dsimp only [Zc, Za, next]
    rw [z_act, inv_inv]
    rfl
  let _ : IsMulCommutative Zc := by
    have hi : IsMulCommutative (Za.map (MulAut.conj data.x).toMonoidHom) := inferInstance
    exact hZc.symm ▸ hi
  let _ : IsMulCommutative C := IsMulCommutative.of_setLike_mul_comm
    (fun x hx y hy => setLike_mul_comm (s := Za) hx.1 hy.1)
  let _ : IsMulCommutative D := IsMulCommutative.of_setLike_mul_comm
    (fun x hx y hy => setLike_mul_comm (s := Zc) hx.1 hy.1)
  obtain ⟨r, hr, hrconj⟩ := Stellmacher.exists_twoResidual_conjugator Za data.E data.x
    data.x_mem_E (data.generated.trans (congrArg (Za ⊔ ·) hZc))
  have hRV : data.E ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono le_sup_left le_rfl).trans
        data.product_action)
  have hrE : r ∈ data.E := twoResidualIn_le data.E hr
  have hVr : V.map (MulAut.conj r).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRV hrE)
  have hCr : C.conjBy r = D := by
    change C.map (MulAut.conj r).toMonoidHom = D
    have hVC : V ⊓ Za = C := hgeom.2.2.2.1
    rw [← hVC, Subgroup.map_inf _ _ _ (MulAut.conj r).injective, hVr]
    change V ⊓ Za.conjBy r = D
    rw [hrconj, ← hZc]
    simpa only [sup_comm] using (distance_one_product_factors Γ next cp.a).2.2.2.1
  have hrfix : r ∈ Subgroup.centralizer
      (((Subgroup.center V).map V.subtype : Subgroup G) : Set G) := by
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hthree) hr
  exact (Subgroup.center_sup_eq_inf_of_fixed_conjugator C D hgeom.1 r hCr hrfix).trans
    hgeom.2.2.2.2

end Stellmacher.SectionNine
