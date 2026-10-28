module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.MarkedModule
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Geometry.Model
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.SubgroupConjugation
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Constructing coordinates on the actual natural tensor constituent

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemmas
14.4.2(5) and 14.4.10, printed pp.1006 and 1010–1011.

`Constituent` specifies the unmarked natural module on the selected image
D/Z(U) inside the literal U/Z(U), with an actual isomorphism of the component
image and equivariance for its full preimage. The earlier equality
O₂(H)=C_H(U/Z(U)) supplies this full-preimage convention. `ofStandard`
transports the canonical Galois-field natural module through genuine field,
vector and group equivalences.

The independent group placements identify the component Sylow image and its
normalizer as the image of the literal X₂=O²(N_{H∞}(T∩H∞)). Given the earlier
fixed binary point Ṽ₂ and |Wᵍ*|=8, the component index six or twelve forces a
nontrivial component image of an element of Wᵍ. This element fixes the point.
A scalar times a determinant-one basis change marks both point and root. The
component Sylow becomes the full upper root group, so the actual X₂ image
preserves its fixed F₄-line and contains the diagonal cubic.

`exists_coordinates_of_model` constructs every field of `Natural.Coordinates`.
`second_mem_Y_of_source` applies these coordinates to the source commutator
bound. The common-family construction of D̃=[Ũ,A], the two group placements,
and the named earlier-source fixed-point and containment inputs remain
explicit. This conditional geometry result is not the assembly of all five
clauses of Lemma 14.4.10.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Geometry
open Representation.SL2FourNatural
variable {G : Type*} [Group G] {H T U V₂ D Wg : Subgroup G}

def conjugationHom (hn : H ≤ normalizer (U : Set G)) : H →* MulAut (U ⧸ center U) :=
  let _ := conjMulDistribMulActionOfLeNormalizer H U hn
  (quotientAut (center U)).comp (MulDistribMulAction.toMulAut H U)

variable [IsElementaryAbelian 2 (U ⧸ center U)]
def representation (hn : H ≤ normalizer (U : Set G)) :
    Representation (ZMod 2) H (Additive (U ⧸ center U)) where
  toFun h := (conjugationHom hn h).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (conjugationHom hn 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (conjugationHom hn (a * b) v.toMul) = _
    rw [map_mul]
    rfl

theorem representation_mk (hn : H ≤ normalizer (U : Set G)) (h : H) (u : U) :
    representation hn h (Additive.ofMul (QuotientGroup.mk' (center U) u)) =
      Additive.ofMul (QuotientGroup.mk' (center U)
        ⟨(h : G) * u * (h : G)⁻¹, le_normalizer_iff.mp hn h h.property u u.property⟩) := by
  let _ := conjMulDistribMulActionOfLeNormalizer H U hn
  exact congrArg Additive.ofMul (quotientAut_apply_mk (center U)
    (MulDistribMulAction.toMulAut H U h) u)

omit [IsElementaryAbelian 2 (U ⧸ center U)] in
theorem star_component : star H (component H) =
    (solvableResidual H).map (QuotientGroup.mk' (pCore 2 H)) := by
  unfold star component
  rw [← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]

omit [IsElementaryAbelian 2 (U ⧸ center U)] in
theorem component_star_normal : (star H (component H)).Normal := by
  rw [star_component]
  infer_instance

omit [IsElementaryAbelian 2 (U ⧸ center U)] in
theorem second_le_component : second H T ≤ component H :=
  (map_subtype_le _).trans inf_le_left

/-- The natural constituent before choosing any point, Borel or root coordinates.
The actor is exactly the image of H∞ in H/O₂(H). Equivariance includes its
full preimage, using the earlier source fact O₂(H)=C_H(U/Z(U)). -/
structure Constituent (H U D : Subgroup G)
    [IsElementaryAbelian 2 (U ⧸ center U)] (hn : H ≤ normalizer (U : Set G)) where
  componentEquiv : star H (component H) ≃* SL
  moduleEquiv : V ≃ₗ[ZMod 2] binarySpace (tilde U D)
  equivariant : ∀ (h : H) (hk : QuotientGroup.mk' (pCore 2 H) h ∈ star H (component H))
    (v : V), representation hn h (moduleEquiv v).val =
      (moduleEquiv (action (componentEquiv ⟨QuotientGroup.mk' (pCore 2 H) h, hk⟩) v)).val

variable {hn : H ≤ normalizer (U : Set G)}
def Constituent.embedding (n : Constituent H U D hn) :
    V →ₗ[ZMod 2] Additive (U ⧸ center U) :=
  (binarySpace (tilde U D)).subtype.comp n.moduleEquiv.toLinearMap

theorem Constituent.injective (n : Constituent H U D hn) :
    Function.Injective n.embedding := Subtype.val_injective.comp n.moduleEquiv.injective

theorem Constituent.image (n : Constituent H U D hn) :
    binarySubgroup n.embedding.range = tilde U D := by
  ext q
  constructor
  · rintro ⟨v, hv⟩
    have hh := (n.moduleEquiv v).property
    change n.embedding v ∈ binarySpace (tilde U D) at hh
    rw [hv] at hh
    exact hh
  · intro hq
    obtain ⟨v, hv⟩ := n.moduleEquiv.surjective ⟨Additive.ofMul q, hq⟩
    exact ⟨v, congrArg Subtype.val hv⟩

theorem Constituent.embedding_equivariant (n : Constituent H U D hn)
    (h : H) (hk : QuotientGroup.mk' (pCore 2 H) h ∈ star H (component H)) (v : V) :
    representation hn h (n.embedding v) =
      n.embedding (action (n.componentEquiv ⟨QuotientGroup.mk' (pCore 2 H) h, hk⟩) v) :=
  n.equivariant h hk v

/-- Convert the canonical Galois-field version of the natural constituent
using the actual field, vector and group equivalences from the model. -/
noncomputable def Constituent.ofStandard
    (eG : star H (component H) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2))
    (eV : (Fin 2 → GaloisField 2 2) ≃ₗ[ZMod 2] binarySpace (tilde U D))
    (heq : ∀ (h : H) (hk : QuotientGroup.mk' (pCore 2 H) h ∈ star H (component H))
      (v : Fin 2 → GaloisField 2 2), representation hn h (eV v).val =
        (eV (Representation.specialLinearNatural 2
          (eG ⟨QuotientGroup.mk' (pCore 2 H) h, hk⟩) v)).val) :
    Constituent H U D hn := by
  let s : V ≃+ (Fin 2 → GaloisField 2 2) :=
    AddEquiv.piCongrRight (fun _ => fieldEquiv.toAddEquiv)
  let f : V ≃+ binarySpace (tilde U D) :=
    s.trans eV.toAddEquiv
  refine {
    componentEquiv := eG.trans standardGroupEquiv.symm
    moduleEquiv := LinearEquiv.ofBijective (f.toAddMonoidHom.toZModLinearMap 2) f.bijective
    equivariant := ?_ }
  intro h hk v
  change representation hn h (eV (standardVectorEquiv v)).val =
    (eV (standardVectorEquiv (action
      (standardGroupEquiv.symm (eG ⟨QuotientGroup.mk' (pCore 2 H) h, hk⟩)) v))).val
  rw [heq, standard_equivariant, standardGroupEquiv.apply_symm_apply]

omit [IsElementaryAbelian 2 (U ⧸ center U)] in
private theorem eight_intersection (S K : Subgroup (coreQuotient H)) [K.Normal]
    (hS : Nat.card S = 8) (hK : K.index = 6 ∨ K.index = 12) :
    ∃ x, x ∈ S ∧ x ∈ K ∧ x ≠ 1 := by
  have hne : S ⊓ K ≠ ⊥ := by
    intro he
    have hh := K.relIndex_dvd_index_of_normal S
    rw [← inf_relIndex_left S K, he, relIndex_bot_left, hS] at hh
    rcases hK with hK | hK <;> rw [hK] at hh <;> norm_num at hh
  obtain ⟨x, hx⟩ := (ne_bot_iff_exists_ne_one).mp hne
  exact ⟨x, x.property.1, x.property.2, fun he => hx (Subtype.ext he)⟩


omit [IsElementaryAbelian 2 (U ⧸ center U)] in
theorem component_le : component H ≤ H := map_subtype_le _

omit [IsElementaryAbelian 2 (U ⧸ center U)] in
def componentActor (e : star H (component H) ≃* SL) {J : Subgroup G}
    (hJ : J ≤ component H) : J →* SL :=
  e.toMonoidHom.comp
    (((QuotientGroup.mk' (pCore 2 H)).comp (inclusion (hJ.trans component_le))).codRestrict
      (star H (component H)) (fun j => mem_map.mpr
        ⟨⟨j, (hJ.trans component_le) j.property⟩, hJ j.property, rfl⟩))

omit [IsElementaryAbelian 2 (U ⧸ center U)] in
theorem componentActor_range (e : star H (component H) ≃* SL) {J : Subgroup G}
    (hJ : J ≤ component H) :
    (componentActor e hJ).range = ((star H J).subgroupOf (star H (component H))).map
      e.toMonoidHom := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨_, ?_, rfl⟩
    exact mem_map.mpr ⟨⟨j, (hJ.trans component_le) j.property⟩, j.property, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨j, hj, he⟩ := hk
    refine ⟨⟨j, hj⟩, ?_⟩
    apply congrArg e
    exact Subtype.ext he

/-- The two placements expected from the independent finite-group calculation.
They refer to actual quotient images, before making any vector coordinates. -/
structure Placements (H T : Subgroup G) : Prop where
  sylow_card : Nat.card (star H (T ⊓ component H)) = 4
  residual_image : (star H (second H T)).subgroupOf (star H (component H)) =
    normalizer ((star H (T ⊓ component H)).subgroupOf
      (star H (component H)) : Set (star H (component H)))

/-- Coordinates are constructed from the unmarked natural constituent and
literal component/Sylow/Borel images. The fixed binary point and order-eight
image are earlier-source inputs, not conclusions of this theorem. -/
theorem exists_coordinates [Finite G]
    (hn : H ≤ normalizer (U : Set G)) (n : Constituent H U D hn)
    (placements : Placements H T)
    (hpoint : Nat.card (tilde U V₂) = 2)
    (hVD : tilde U V₂ ≤ tilde U D)
    (hfixed : ∀ h : H, (h : G) ∈ T ∨ (h : G) ∈ Wg →
      ∀ q ∈ tilde U V₂, representation hn h (Additive.ofMul q) = Additive.ofMul q)
    (hWcard : Nat.card (star H Wg) = 8)
    (houter : (star H (component H)).index = 6 ∨ (star H (component H)).index = 12) :
    Nonempty (Coordinates H T U V₂ D Wg hn) := by
  have hpne : tilde U V₂ ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hpoint
    norm_num at hpoint
  obtain ⟨q₀, hq₀⟩ := ne_bot_iff_exists_ne_one.mp hpne
  let q := q₀.val
  have hq : q ∈ tilde U V₂ := q₀.property
  have hqne : q ≠ 1 := fun he => hq₀ (Subtype.ext he)
  have hqD : q ∈ binarySubgroup n.embedding.range := by rw [n.image]; exact hVD hq
  obtain ⟨p, hpq⟩ := hqD
  change n.embedding p = Additive.ofMul q at hpq
  have hp : p ≠ 0 := by
    intro he
    rw [he, map_zero] at hpq
    apply hqne
    exact Additive.ofMul.injective hpq.symm
  have : (star H (component H)).Normal := component_star_normal
  obtain ⟨z, hzW, hzK, hzne⟩ := eight_intersection (star H Wg) (star H (component H))
    hWcard houter
  obtain ⟨root, hroot, hrz⟩ := hzW
  have hrootK : QuotientGroup.mk' (pCore 2 H) root ∈ star H (component H) :=
    hrz.symm ▸ hzK
  let r : SL := n.componentEquiv ⟨QuotientGroup.mk' (pCore 2 H) root, hrootK⟩
  have hrne : r ≠ 1 := by
    intro he
    have he' := n.componentEquiv.injective (he.trans n.componentEquiv.map_one.symm)
    have hh := congrArg Subtype.val he'
    exact hzne (hrz.symm.trans hh)
  have hrfix : action r p = p := by
    apply n.injective
    rw [← n.embedding_equivariant root hrootK p, hpq]
    exact hfixed root (Or.inr hroot) q hq
  obtain ⟨b, c, hc, hb, hbr⟩ := Model.exists_frame p hp r hrfix hrne
  let e := Model.rebase b c hc
  let f := n.embedding.comp e.toLinearMap
  have hfi : Function.Injective f := n.injective.comp e.injective
  let α := MulAut.conj b⁻¹
  let a₀ := componentActor n.componentEquiv (second_le_component (H := H) (T := T))
  let a := α.toMonoidHom.comp a₀
  let s := componentActor n.componentEquiv (show T ⊓ component H ≤ component H from inf_le_right)
  let P := s.range
  have hPfix : ∀ g ∈ P, action g p = p := by
    rintro g ⟨t, rfl⟩
    apply n.injective
    have htK : (t : G) ∈ component H := t.property.2
    have htT : (t : G) ∈ T := t.property.1
    let tH : H := ⟨t, component_le htK⟩
    have htq : QuotientGroup.mk' (pCore 2 H) tH ∈ star H (component H) :=
      mem_map.mpr ⟨tH, htK, rfl⟩
    calc
      n.embedding (action (s t) p) = representation hn tH (n.embedding p) :=
        (n.embedding_equivariant tH htq p).symm
      _ = n.embedding p := by
        rw [hpq]
        exact hfixed tH (Or.inl htT) q hq
  have hPcard : Nat.card P = 4 := by
    rw [show P = s.range from rfl, componentActor_range,
      card_map_of_injective n.componentEquiv.injective,
      Nat.card_congr (subgroupOfEquivOfLe
        (show star H (T ⊓ component H) ≤ star H (component H) from
          map_mono (subgroupOf_mono H inf_le_right))).toEquiv]
    exact placements.sylow_card
  have hPa : P.map α.toMonoidHom = Model.fixer Model.e1 :=
    Model.frame_sylow p b c hc hb P hPfix hPcard
  have ha₀ : a₀.range = normalizer (P : Set SL) := by
    rw [show a₀ = componentActor n.componentEquiv second_le_component from rfl,
      componentActor_range, placements.residual_image, map_equiv_normalizer_eq]
    rw [show P = s.range from rfl, componentActor_range]
  have ha : a.range = normalizer (Model.fixer Model.e1 : Set SL) := by
    rw [show a = α.toMonoidHom.comp a₀ from rfl, MonoidHom.range_comp,
      ha₀, map_equiv_normalizer_eq, hPa]
  refine ⟨{
    representation := representation hn
    conjugation := representation_mk hn
    embedding := f
    injective := hfi
    actor := a
    equivariant := ?_
    point_image := ?_
    constituent_image := ?_
    borel_stabilizes := by rw [ha]; exact Model.normalizer_stabilizes
    cubic_mem := by rw [ha]; exact Model.cubic_normalizes
    root := root
    root_mem := hroot
    root_action := ?_ }⟩
  · intro x v
    change representation hn (inclusion (second_le H T) x) (n.embedding (e v)) = _
    rw [n.embedding_equivariant]
    change n.embedding (action (a₀ x) (Model.rebase b c hc v)) =
      n.embedding (Model.rebase b c hc (action (b⁻¹ * a₀ x * b⁻¹⁻¹) v))
    rw [inv_inv, Model.rebase_equivariant]
  · apply Subgroup.eq_of_le_of_card_ge
    · rintro w ⟨v, hv, hvw⟩
      change f v = Additive.ofMul w at hvw
      change Additive.ofMul w ∈ binarySpace (tilde U V₂)
      rw [← hvw]
      rcases (Model.point_mem_iff v).mp hv with rfl | rfl
      · rw [map_zero]
        exact Submodule.zero_mem _
      · change n.embedding (Model.rebase b c hc Model.e1) ∈ binarySpace (tilde U V₂)
        rw [hb, hpq]
        exact hq
    · rw [hpoint, binarySubgroup_card,
        ← Nat.card_congr (Submodule.equivMapOfInjective f hfi PointCommutator.point).toEquiv,
        PointCommutator.point_card]
  · have hfr : f.range = n.embedding.range := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨e v, rfl⟩
      · rintro ⟨v, rfl⟩
        refine ⟨e.symm v, ?_⟩
        change n.embedding (e (e.symm v)) = n.embedding v
        rw [e.apply_symm_apply]
    rw [hfr, n.image]
  · intro v
    change representation hn root (n.embedding (e v)) = _
    rw [n.embedding_equivariant root hrootK]
    change n.embedding (action r (Model.rebase b c hc v)) =
      n.embedding (Model.rebase b c hc (action (upper 1) v))
    rw [Model.rebase_equivariant]
    have hconj : b⁻¹ * r * b = upper 1 := by rw [← hbr]; group
    rw [hconj]

/-- The two genuine actor isomorphisms give index twelve or six over the
actual component. The natural constituent supplies its SL₂(4) identification. -/
theorem component_index_of_model [Finite G]
    (e : star H (component H) ≃* SL)
    (hmodel : Nonempty (coreQuotient H ≃* Theory.SpecificGroups.TensorThreeFive.S3 ×
        Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* Theory.SpecificGroups.TensorThreeFive.S3 ×
        alternatingGroup (Fin 5))) :
    (star H (component H)).index = 6 ∨ (star H (component H)).index = 12 := by
  have hK : Nat.card (star H (component H)) = 60 := by
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two,
      Nat.card_eq_fintype_card, card_field]
    norm_num
  have hh := (star H (component H)).card_mul_index
  rw [hK] at hh
  rcases hmodel with hm | hm
  · obtain ⟨eH⟩ := hm
    right
    rw [Nat.card_congr eH.toEquiv, Nat.card_prod] at hh
    norm_num [Theory.SpecificGroups.TensorThreeFive.S3,
      Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh
    omega
  · obtain ⟨eH⟩ := hm
    left
    rw [Nat.card_congr eH.toEquiv, Nat.card_prod, nat_card_alternatingGroup] at hh
    norm_num [Theory.SpecificGroups.TensorThreeFive.S3,
      Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hh
    omega

/-- Coordinate construction using the actual actor alternatives in 14.4.2(5).
The common constituent and earlier fixed-point statements remain explicit;
no moved-space, Borel-coordinate or root-coordinate conclusion is assumed. -/
theorem exists_coordinates_of_model [Finite G]
    (hn : H ≤ normalizer (U : Set G)) (n : Constituent H U D hn)
    (placements : Placements H T)
    (hmodel : Nonempty (coreQuotient H ≃* Theory.SpecificGroups.TensorThreeFive.S3 ×
        Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* Theory.SpecificGroups.TensorThreeFive.S3 ×
        alternatingGroup (Fin 5)))
    (hpoint : Nat.card (tilde U V₂) = 2) (hVD : tilde U V₂ ≤ tilde U D)
    (hfixed : ∀ h : H, (h : G) ∈ T ∨ (h : G) ∈ Wg →
      ∀ q ∈ tilde U V₂, representation hn h (Additive.ofMul q) = Additive.ofMul q)
    (hWcard : Nat.card (star H Wg) = 8) :
    Nonempty (Coordinates H T U V₂ D Wg hn) :=
  exists_coordinates hn n placements hpoint hVD hfixed hWcard
    (component_index_of_model n.componentEquiv hmodel)

/-- Consumer for the literal X₂ in Lemma 14.4.10. The selected constituent
is supplied by the common-family branch as [Ũ,A] with A≤Wᵍ. The earlier
12.8.11(1) bound [Wᵍ,W]≤E and the actual index-two hyperplane give X₂∈Y.
The coordinate marks are now constructed, rather than an input here. -/
theorem second_mem_Y_of_source [Finite G] [IsExtraspecial 2 U]
    (hn : H ≤ normalizer (U : Set G)) (n : Constituent H U D hn)
    (placements : Placements H T)
    (hmodel : Nonempty (coreQuotient H ≃* Theory.SpecificGroups.TensorThreeFive.S3 ×
        Equiv.Perm (Fin 5)) ∨
      Nonempty (coreQuotient H ≃* Theory.SpecificGroups.TensorThreeFive.S3 ×
        alternatingGroup (Fin 5)))
    (hpoint : Nat.card (tilde U V₂) = 2) (hVD : tilde U V₂ ≤ tilde U D)
    (hfixed : ∀ h : H, (h : G) ∈ T ∨ (h : G) ∈ Wg →
      ∀ q ∈ tilde U V₂, representation hn h (Additive.ofMul q) = Additive.ofMul q)
    (hWcard : Nat.card (star H Wg) = 8) {E W A : Subgroup G}
    (hX : second H T ∈ XFamily H T) (hUT : U ≤ T) (hVU : V₂ ≤ U)
    (hZV : center U ≤ V₂.subgroupOf U) (hZE : center U ≤ E.subgroupOf U)
    (hDU : D ≤ U) (hWgH : Wg ≤ H) (hEW : E ≤ W)
    (hD : tilde U D = tilde U ⁅U, A⁆) (hA : A ≤ Wg)
    (hindex : W.relIndex U = 2) (hsource : ⁅Wg, W⁆ ≤ E) :
    second H T ∈ YFamily H T V₂ E := by
  obtain ⟨c⟩ := exists_coordinates_of_model hn n placements hmodel hpoint hVD hfixed hWcard
  exact c.second_mem_Y_of_source hX hUT hVU hZV hZE hDU hWgH hEW hD hA hindex hsource

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Natural.Geometry
