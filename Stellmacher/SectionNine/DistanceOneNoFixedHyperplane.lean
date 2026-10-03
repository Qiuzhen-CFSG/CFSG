module
public import Stellmacher.SectionNine.DistanceOneProductCenterIntersection
public import Stellmacher.SectionNine.DistanceOneQuadraticImage
/-!
# No fixed hyperplane in the extracted image

For the actual distance-one extraction and any faithful quotient witness on
its initial center, no nontrivial subgroup of the image of V has fixed-point
index two. Neither an order-two actor nor the later faithful classification
is assumed.

The two abelian factors C and D have product center C∩D by source (3) and
the residual conjugator. Consequently C_V(C)=C. Source (2) says an initial
center vector outside C has centralizer C in V. A fixed hyperplane for a
lift Y therefore lies in C unless Y already lies there. Since C itself has
index two, the fixed hyperplane equals C, and C_V(C)=C then forces Y into
C. The faithful witness kills C, contradicting the nontrivial image.

This proves the transvection exclusion in Stellmacher (9.1), relation (6),
Journal of Algebra 190 (1997), printed p.47, refs/files/stellmacher-n-group.pdf.
The proof retains the exact extraction and quotient action throughout.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise
universe u
private theorem product_factor_selfcentralizer
    {G : Type u} [Group G] (C D : Subgroup G)
    [IsMulCommutative C] [IsMulCommutative D]
    (hn : C ≤ Subgroup.normalizer (D : Set G))
    (hz : (Subgroup.center ↥(C ⊔ D)).map (C ⊔ D).subtype = C ⊓ D) :
    (C ⊔ D) ⊓ Subgroup.centralizer (C : Set G) = C := by
  apply le_antisymm
  · intro y hy
    have hp : y ∈ (C : Set G) * (D : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right C D hn]
      exact hy.1
    obtain ⟨c,hc,d,hd,hcd⟩ := hp
    have hdC : d ∈ Subgroup.centralizer (C : Set G) := by
      have hh := (Subgroup.centralizer (C : Set G)).mul_mem
        ((Subgroup.centralizer (C : Set G)).inv_mem (C.le_centralizer hc)) hy.2
      rw [← hcd] at hh
      simpa only [inv_mul_cancel_left] using hh
    have hdZ : d ∈ (Subgroup.center ↥(C ⊔ D)).map (C ⊔ D).subtype := by
      refine ⟨⟨d, Subgroup.mem_sup_right hd⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
      have hV : C ⊔ D ≤ Subgroup.centralizer ({d} : Set G) := sup_le
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hdC a ha))
        (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
          ((D.le_centralizer hd) a ha))
      intro a
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (hV a.property)
    rw [hz] at hdZ
    rw [← hcd]
    exact C.mul_mem hc hdZ.1
  · exact le_inf le_sup_left C.le_centralizer

private theorem native_fixed_hyperplane
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (hcenter :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
      let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
      (Subgroup.center ↥(C ⊔ D)).map (C ⊔ D).subtype = C ⊓ D)
    (Y : Subgroup G)
    (hYV : Y ≤ (z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a)) ⊔
      (z ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a) ⊓
        stabilizer ctx.Γ ctx.criticalPath.a))
    (hcard : Nat.card (z ctx.Γ ctx.criticalPath.a) =
      2 * Nat.card ((z ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer (Y : Set G)) : Subgroup G)) :
    Y ≤ z ctx.Γ ctx.criticalPath.a := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let Za := z Γ cp.a
  let Zc := z Γ next
  let C := Za ⊓ stabilizer Γ next
  let D := Zc ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let F := Za ⊓ Subgroup.centralizer (Y : Set G)
  have hfactors := distance_one_product_factors Γ cp.a next
  by_contra hnot
  have hFC : F ≤ C := by
    intro a ha
    by_contra haC
    have hout : a ∉ data.coatom := by rw [data.coatom_stabilizer]; exact haC
    have hCV := distance_one_extracted_centralizer ctx hb data.toDistanceOneExtractionData
      a ha.1 hout
    apply hnot
    have hYC : Y ≤ C := by
      intro y hy
      apply hCV.le
      exact ⟨hYV hy, Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp ha.2 y hy)⟩
    exact hYC.trans inf_le_left
  have hFCeq : F = C := by
    apply Subgroup.eq_of_le_of_card_ge hFC
    have hc := data.coatom_card
    rw [data.coatom_stabilizer] at hc
    change Nat.card Za = 2 * Nat.card C at hc
    change Nat.card Za = 2 * Nat.card F at hcard
    omega
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
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
  have hself : V ⊓ Subgroup.centralizer (C : Set G) = C :=
    product_factor_selfcentralizer C D hfactors.1 hcenter
  apply hnot
  have hYC : Y ≤ C := by
    rw [← hself]
    apply le_inf hYV
    apply Subgroup.le_centralizer_iff.mp
    rw [← hFCeq]
    exact inf_le_right
  exact hYC.trans inf_le_left


public theorem distance_one_image_fixed_index_ne_two
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
    ∀ X : Subgroup w.X, X ≤ (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection →
      X ≠ ⊥ → (FixedPoints.subgroup X (ZAt ctx.Γ ctx.criticalPath.a)).index ≠ 2 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let C := z Γ cp.a ⊓ stabilizer Γ next
  let D := z Γ next ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  change ∀ X : Subgroup w.X, X ≤ (V.subgroupOf P).map w.projection →
    X ≠ ⊥ → (FixedPoints.subgroup X Za).index ≠ 2
  intro X hX hXne hi
  have hfactors := distance_one_product_factors Γ cp.a next
  have hVP : V ≤ P := hfactors.2.2.1.trans inf_le_left
  let Y1 := V.subgroupOf P ⊓ X.comap w.projection
  let Y := Y1.map P.subtype
  have hYP : Y ≤ P := Subgroup.map_subtype_le _
  have hYV : Y ≤ V := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hVP]
    exact Subgroup.map_mono inf_le_left
  have hYimage : (Y.subgroupOf P).map w.projection = X := by
    rw [show Y = Y1.map P.subtype from rfl, subgroupOf_map_subtype_eq]
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y,hy,he⟩ := hX hx
      exact ⟨y,⟨hy,show w.projection y ∈ X from he ▸ hx⟩,he⟩
  have hcard : Nat.card Za = 2 * Nat.card (Za ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) := by
    have hc := (FixedPoints.subgroup X Za).card_mul_index
    rw [hi, ← hYimage, w.fixedPoints_card Y hYP] at hc
    change Nat.card (Za ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) * 2 = Nat.card Za at hc
    omega
  have hcenter := (distance_one_product_center_eq_intersection ctx hb data).trans
    hfactors.2.2.2.2.symm
  have hYZa : Y ≤ Za := native_fixed_hyperplane ctx hb data hcenter Y hYV hcard
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  apply hXne
  rw [← hYimage, Subgroup.map_eq_bot_iff]
  intro y hy
  rw [w.kernel_eq]
  exact ⟨y.property, Za.le_centralizer (hYZa hy)⟩
end Stellmacher.SectionNine
