module

public import Stellmacher.SectionNine.DistanceOneCenterIntersection
public import Stellmacher.SectionNine.DistanceOneAction
public import Stellmacher.TwoResidualConjugator
public import Theory.GroupTheory.FixedProductCenter

/-!
# Center and order of the extracted distance-one product

The two cross factors in Stellmacher (9.1) each have order eight. A conjugator
in the extracted two-residual carries the first factor to the second and fixes
the product center by source relation (3). The fixed-product-center theorem
therefore identifies that center with the factor intersection, already known
to be the next vertex center. The source index inequality bounds its order
by two; nontriviality of the center of a two-group gives equality. The product
then has order 32 by the normalized-product index formula.

These conclusions precede core equality and the quaternion recognition. The
actual extraction, coatom intersection, source (3), and the index bound in (4)
remain explicit inputs. Source: Stellmacher, Journal of Algebra 190 (1997),
(9.1), journal pp.46–47, relations (1)–(4), (8), and the paragraph before (9).
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u

private theorem product_second_intersection
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B) (a c : Γ.Vertex) :
    ((z Γ a ⊓ stabilizer Γ c) ⊔ (z Γ c ⊓ stabilizer Γ a)) ⊓ z Γ c =
      z Γ c ⊓ stabilizer Γ a := by
  simpa only [sup_comm] using (distance_one_product_factors Γ c a).2.2.2.1

public theorem distance_one_extracted_product_center_card
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1)
    (hfaith : DistanceOneFaithfulConclusion ctx.toLocalContext)
    (data : DistanceOneExtractionData ctx)
    (hcoatom : data.coatom = z ctx.Γ ctx.criticalPath.a ⊓
      stabilizer ctx.Γ (ctx.Γ.act data.x⁻¹ ctx.criticalPath.a))
    (hfour :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      4 ≤ (V ⊓ q ctx.Γ ctx.criticalPath.a).relIndex V)
    (hthree :
      let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
      let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
        (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
      ⁅(Subgroup.center V).map V.subtype, twoResidualIn data.E⁆ = ⊥) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let C := z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next
    let D := z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a
    let V := C ⊔ D
    (Subgroup.center V).map V.subtype = z ctx.Γ ctx.criticalPath.a' ∧
      Nat.card (z ctx.Γ ctx.criticalPath.a') = 2 ∧
      Nat.card C = 8 ∧ Nat.card D = 8 ∧ Nat.card V = 32 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let Za := z Γ cp.a
  let Zc := z Γ next
  let C := Za ⊓ stabilizer Γ next
  let D := Zc ⊓ stabilizer Γ cp.a
  let V := C ⊔ D
  let Z := z Γ cp.a'
  have hgeom := distance_one_product_factors Γ cp.a next
  have hCD : C ⊓ D = Z := hgeom.2.2.2.2.trans
    (distance_one_center_intersection_eq_of_extraction ctx hb hfaith data hfour)
  have hCCard : Nat.card C = 8 := by
    have hc := data.coatom_card
    rw [hcoatom] at hc
    have ha : Nat.card (z Γ cp.a) = 16 := hfaith.1
    change Nat.card (z Γ cp.a) = 2 * Nat.card C at hc
    omega
  have hDCard : Nat.card D = 8 := by
    have hc := (distance_one_factor_transport ctx hb data).1
    have h := congrArg (fun K : Subgroup G => Nat.card K) hc
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective] at h
    exact h.symm.trans hCCard
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
        (distance_one_extracted_action ctx hb data hcoatom))
  have hrE : r ∈ data.E := twoResidualIn_le data.E hr
  have hVr : V.map (MulAut.conj r).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hRV hrE)
  have hCr : C.conjBy r = D := by
    change C.map (MulAut.conj r).toMonoidHom = D
    have hVC : V ⊓ Za = C := hgeom.2.2.2.1
    rw [← hVC, Subgroup.map_inf _ _ _ (MulAut.conj r).injective, hVr]
    change V ⊓ Za.conjBy r = D
    rw [hrconj, ← hZc]
    exact product_second_intersection Γ cp.a next
  have hrfix : r ∈ Subgroup.centralizer
      (((Subgroup.center V).map V.subtype : Subgroup G) : Set G) := by
    exact Subgroup.le_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hthree) hr
  have hcenter : (Subgroup.center V).map V.subtype = Z :=
    (Subgroup.center_sup_eq_inf_of_fixed_conjugator C D hgeom.1 r hCr hrfix).trans hCD
  have hZCard : Nat.card Z = 2 := by
    have hindex : 4 ≤ C.relIndex V := by
      change 4 ≤ (V ⊓ q Γ cp.a).relIndex V at hfour
      rw [distance_one_extracted_core_intersection ctx hb data] at hfour
      exact hfour
    let _ : (C.subgroupOf V).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hgeom.2.1)
    have hi := Subgroup.relIndex_sup_left (D.subgroupOf V) (C.subgroupOf V)
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.relIndex_subgroupOf le_rfl,
      Subgroup.relIndex_subgroupOf le_sup_right,
      ← Subgroup.inf_relIndex_right C D, hCD] at hi
    have hmult := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) Z D bot_le
      (hCD ▸ (inf_le_right : C ⊓ D ≤ D))
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hDCard] at hmult
    have hsmall : Nat.card Z ≤ 2 := by rw [hi] at hindex; nlinarith
    have hnon : Z ≠ ⊥ := by
      intro hz
      have hc : Subgroup.center V = ⊥ := by
        apply Subgroup.map_injective (f := V.subtype) V.subtype_injective
        simpa only [Subgroup.map_bot] using hcenter.trans hz
      have hVp : IsPGroup 2 V := by
        have hC := (IsElementaryAbelian.isPGroup 2 Za).to_le (inf_le_left : C ≤ Za)
        have hD : IsPGroup 2 D := by
          have hZcp : IsPGroup 2 Zc := by
            rw [hZc]
            exact (IsElementaryAbelian.isPGroup 2 Za).map _
          exact hZcp.to_le inf_le_left
        exact hC.to_sup_of_normal_right' hD hgeom.1
      let _ : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
        intro hv
        have hCb : C = ⊥ := bot_unique (hv ▸ (le_sup_left : C ≤ V))
        simp only [hCb, Subgroup.card_bot] at hCCard
        omega)
      exact (Subgroup.nontrivial_iff_ne_bot _).mp hVp.center_nontrivial hc
    exact Nat.le_antisymm hsmall ((Subgroup.one_lt_card_iff_ne_bot _).mpr hnon)
  have hVCard : Nat.card V = 32 := by
    let _ : (C.subgroupOf V).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (sup_le C.le_normalizer hgeom.2.1)
    have hi := Subgroup.relIndex_sup_left (D.subgroupOf V) (C.subgroupOf V)
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.relIndex_subgroupOf le_rfl,
      Subgroup.relIndex_subgroupOf le_sup_right,
      ← Subgroup.inf_relIndex_right C D, hCD] at hi
    have hmult := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) Z D bot_le
      (hCD ▸ (inf_le_right : C ⊓ D ≤ D))
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hDCard, hZCard] at hmult
    have hmultV := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) C V bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hCCard, hi] at hmultV
    omega
  exact ⟨hcenter, hZCard, hCCard, hDCard, hVCard⟩

end Stellmacher.SectionNine
