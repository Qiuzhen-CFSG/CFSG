module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.MultiplicitySimple

/-!
# The source point image of the three-space radical

For the original pair centralizer quotient H/Q, this module identifies the
image RQ_z/Q_z of the special radical R. It proves that this is the literal
elementary group of order 16, transports the original opposite pair section
onto it equivariantly for the same S/R action, and identifies S/R with the
actual quotient of H/Q by its E32 core, including the representative map.

This is the source module in Aschbacher--Segev (4.4), printed pp.597--598,
where the irreducible S/R-submodules on R/Z are identified through RQ/Q.
The native quintet comparison and final J4 recognition are developed above
this module.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : CubicAutomorphismQuotient (centralizer z ⧸ core z)}
  {X : Sylow 3 (LocalGeometry.CubicLift.subgroup e)}
variable (d : ThreeSpaceData z e X)
attribute [local instance] R_normal_in_S_intrinsic R_normal_in_normalizer

/-- The original radical maps to the original pair image in H/Q. -/
def radicalPairProjection : d.R →* d.pairImage :=
  d.pairProjection.comp (inclusion (inf_le_right.trans d.S_le_pairCentralizer))

theorem radicalPairProjection_ker :
    d.radicalPairProjection.ker = (ambientCore z).subgroupOf d.R := by
  change d.pairProjection.ker.comap _ = _
  rw [d.pairProjection_ker]
  rfl

/-- The literal section RQ_z/Q_z, with the original quotient map. -/
def pointImage : Subgroup d.pairImage := d.radicalPairProjection.range

theorem pointImage_normal (h : IsTypeJ4 z) : d.pointImage.Normal := by
  have hn : (d.R.subgroupOf d.pairCentralizer).Normal :=
    (normal_subgroupOf_iff_le_normalizer
      (inf_le_right.trans d.S_le_pairCentralizer)).mpr
      ((d.pairCentralizer_le_normalizer h).trans d.R_normalized)
  have he : d.pointImage = (d.R.subgroupOf d.pairCentralizer).map d.pairProjection := by
    rw [pointImage, radicalPairProjection, MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨r, rfl⟩
      exact r.property
    · intro hx
      exact ⟨⟨x.val,hx⟩,rfl⟩
  rw [he]
  exact hn.map _ d.pairProjection_surjective

private theorem center_le_radicalPairProjection_ker (h : IsTypeJ4 z) :
    center d.R ≤ d.radicalPairProjection.ker := by
  rw [d.radicalPairProjection_ker]
  intro r hr
  apply d.contained_in_cores z (d.markedPoint 0).property (by
    intro he; have hi := h.involution; simp [he] at hi)
  change (r : G) ∈ d.space
  rw [← d.R_center_eq_space h]
  exact mem_map_of_mem _ hr

/-- The actual quotient map R/Z(R) onto RQ_z/Q_z. -/
def pointProjection (h : IsTypeJ4 z) : (d.R ⧸ center d.R) →* d.pointImage :=
  QuotientGroup.lift _ d.radicalPairProjection.rangeRestrict (by
    intro r hr
    apply Subtype.ext
    exact d.center_le_radicalPairProjection_ker h hr)

@[simp] theorem pointProjection_mk (h : IsTypeJ4 z) (r : d.R) :
    (d.pointProjection h (QuotientGroup.mk' (center d.R) r) : d.pairImage) =
      d.radicalPairProjection r := rfl

theorem pointProjection_surjective (h : IsTypeJ4 z) :
    Function.Surjective (d.pointProjection h) := by
  rintro ⟨_,r,rfl⟩
  exact ⟨QuotientGroup.mk' _ r,rfl⟩

theorem pointProjection_ker (h : IsTypeJ4 z) :
    (d.pointProjection h).ker = d.coreSection z := by
  apply comap_injective (QuotientGroup.mk'_surjective (center d.R))
  rw [d.coreSection_comap h (t := z) (d.markedPoint 0).property (by
    intro he; have hi := h.involution; simp [he] at hi)]
  rw [← d.radicalPairProjection_ker]
  ext r
  exact Subtype.ext_iff

theorem pointImage_card (h : IsTypeJ4 z) : Nat.card d.pointImage = 16 := by
  have hc := (d.pointProjection h).ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr (d.pointProjection_surjective h),card_top,
    d.pointProjection_ker h,d.coreSection_card h (t := z) (d.markedPoint 0).property (by
      intro he; have hi := h.involution; simp [he] at hi),d.R_center_quotient_card h] at hc
  omega

theorem pointImage_elementary (h : IsTypeJ4 z) : IsElementaryAbelian 2 d.pointImage := by
  let := d.R_center_quotient_elementary h
  exact IsElementaryAbelian.of_surjective (d.pointProjection h) (d.pointProjection_surjective h)

theorem pointImage_le_twoCore (h : IsTypeJ4 z) : d.pointImage ≤ pCore 2 d.pairImage := by
  let := d.pointImage_normal h
  let := d.pointImage_elementary h
  exact le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 d.pointImage⟩

/-- The opposite pair section has zero intersection with the kernel Q_z/Z. -/
theorem oppositeSection_projection_injective (h : IsTypeJ4 z) :
    Function.Injective ((d.pointProjection h).comp
      (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : v.val ∈ d.coreSection z := by
    rw [←d.pointProjection_ker h]
    exact hv
  apply mem_bot.mpr
  apply Subtype.ext
  exact mem_bot.mp (d.coreSection_triple_inf h ▸
    (show v.val ∈ d.coreSection z ⊓ d.coreSection d.r ⊓ d.coreSection d.s from
      ⟨⟨hz,v.property.1⟩,v.property.2⟩))

/-- Projection of the opposite pair section is exactly the source sixteen-group. -/
noncomputable def oppositeSectionPointEquiv (h : IsTypeJ4 z) :
    (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) ≃* d.pointImage :=
  MulEquiv.ofBijective ((d.pointProjection h).comp
    (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)).subtype)
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨d.oppositeSection_projection_injective h,by
        have hz1 : z ≠ 1 := by intro he; have hi := h.involution; simp [he] at hi
        have hr1 : d.r ≠ 1 := by intro he; exact hz1 (isConj_one_left.mp (he ▸ d.r_conj))
        have hs1 : d.s ≠ 1 := by intro he; exact hz1 (isConj_one_left.mp (he ▸ d.s_conj))
        rw [d.coreSection_inf_card h (t := d.r) (u := d.s)
          (d.markedPoint 1).property (d.markedPoint 2).property hr1 hs1 d.distinct,d.pointImage_card h]⟩)

@[simp] theorem oppositeSectionPointEquiv_apply (h : IsTypeJ4 z)
    (v : (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R))) :
    d.oppositeSectionPointEquiv h v = d.pointProjection h v := rfl

/-- Literal conjugation on the normal image RQ_z/Q_z. -/
def pointImageAction (h : IsTypeJ4 z) : d.pairImage →* MulAut d.pointImage := by
  let := d.pointImage_normal h
  exact MulAut.conjNormal

@[simp] theorem pointImageAction_apply (h : IsTypeJ4 z) (p : d.pairImage) (u : d.pointImage) :
    (d.pointImageAction h p u : d.pairImage) = p * u.val * p⁻¹ := rfl

/-- Projection intertwines the original S action and its literal image in H/Q. -/
theorem pointProjection_intertwines (h : IsTypeJ4 z) (s : d.S)
    (v : d.R ⧸ center d.R) :
    d.pointProjection h (d.SRadicalAction h (QuotientGroup.mk' _ s) v) =
      d.pointImageAction h (d.pairProjection (inclusion d.S_le_pairCentralizer s))
        (d.pointProjection h v) := by
  obtain ⟨r,rfl⟩ := QuotientGroup.mk'_surjective (center d.R) v
  apply Subtype.ext
  apply Subtype.ext
  rw [d.SRadicalAction_mk,d.radicalAction_mk,d.pointProjection_mk,
    d.pointImageAction_apply,d.pointProjection_mk]
  change QuotientGroup.mk' (core z)
    ((⟨s.val, (d.S_le_pairCentralizer s.property).1⟩ : centralizer z) *
      ⟨r.val, (d.S_le_pairCentralizer r.property.2).1⟩ *
      (⟨s.val, (d.S_le_pairCentralizer s.property).1⟩ : centralizer z)⁻¹) = _
  simp only [map_mul,map_inv]
  rfl

def pointSAction (h : IsTypeJ4 z) : d.S →* MulAut d.pointImage :=
  (d.pointImageAction h).comp (d.pairProjection.comp (inclusion d.S_le_pairCentralizer))

theorem R_le_pointSAction_ker (h : IsTypeJ4 z) :
    d.R.subgroupOf d.S ≤ (d.pointSAction h).ker := by
  intro s hs
  apply MulEquiv.ext
  intro u
  obtain ⟨v,rfl⟩ := d.pointProjection_surjective h u
  change d.pointImageAction h (d.pairProjection (inclusion d.S_le_pairCentralizer s))
    (d.pointProjection h v) = d.pointProjection h v
  rw [←d.pointProjection_intertwines h]
  have he : (QuotientGroup.mk' (d.R.subgroupOf d.S) s) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hs
  rw [he,map_one,MulAut.one_apply]

/-- The SAME S/R acts on the actual point image. -/
def pointQuotientAction (h : IsTypeJ4 z) :
    (d.S ⧸ d.R.subgroupOf d.S) →* MulAut d.pointImage :=
  QuotientGroup.lift _ (d.pointSAction h) (d.R_le_pointSAction_ker h)

@[simp] theorem pointQuotientAction_mk (h : IsTypeJ4 z) (s : d.S) :
    d.pointQuotientAction h (QuotientGroup.mk' _ s) =
      d.pointImageAction h (d.pairProjection (inclusion d.S_le_pairCentralizer s)) := rfl

theorem pointProjection_quotient_intertwines (h : IsTypeJ4 z)
    (a : d.S ⧸ d.R.subgroupOf d.S) (v : d.R ⧸ center d.R) :
    d.pointProjection h (d.SRadicalAction h a v) =
      d.pointQuotientAction h a (d.pointProjection h v) := by
  obtain ⟨s,rfl⟩ := QuotientGroup.mk'_surjective (d.R.subgroupOf d.S) a
  exact d.pointProjection_intertwines h s v

set_option backward.isDefEq.respectTransparency false in
/-- The original four-space, not a new irreducible, is the source RQ_z/Q_z module. -/
theorem exists_multiplicity_pointImage_equiv (h : IsTypeJ4 z) :
    ∃ F : d.multiplicitySpace ≃* d.pointImage,
      ∀ a : d.S ⧸ d.R.subgroupOf d.S, ∀ w : d.multiplicitySpace,
        F (d.multiplicityAction h a w) = d.pointQuotientAction h a (F w) := by
  classical
  obtain ⟨l,hl⟩ := d.exists_K_marked_permutation h ((Equiv.swap 0 1)*(Equiv.swap 1 2))
  have hlz : (l : G)*z*(l : G)⁻¹=d.r := by
    simpa [markedPoint,Equiv.swap_apply_def] using hl 0
  have hlr : (l : G)*d.r*(l : G)⁻¹=d.s := by
    simpa [markedPoint,Equiv.swap_apply_def] using hl 1
  let c : d.multiplicitySpace ≃*
      (d.coreSection d.r ⊓ d.coreSection d.s : Subgroup (d.R ⧸ center d.R)) :=
    d.pairSectionTransport h l z d.r d.r d.s hlz hlr
  refine ⟨c.trans (d.oppositeSectionPointEquiv h),?_⟩
  intro a w
  change d.pointProjection h (c (d.multiplicityAction h a w)) =
    d.pointQuotientAction h a (d.pointProjection h (c w))
  exact (congrArg (d.pointProjection h)
    (d.pairSectionTransport_intertwines h l d.r d.s hlz hlr a w)).trans
      (d.pointProjection_quotient_intertwines h a (c w))

/-- The original S maps to the two-core quotient of the original pair image. -/
def pointFactorMap : d.S →* (d.pairImage ⧸ pCore 2 d.pairImage) :=
  (QuotientGroup.mk' _).comp (d.pairProjection.comp (inclusion d.S_le_pairCentralizer))

/-- The kernel is the literal R, rather than an abstract subgroup of the same order. -/
theorem pointFactorMap_ker (h : IsTypeJ4 z) :
    d.pointFactorMap.ker = d.R.subgroupOf d.S := by
  have hpre := d.pairProjection.comap_pCore_of_ker_isPGroup
    d.pairProjection_surjective (d.pairProjection_kernel_isTwoGroup h)
  ext s
  change QuotientGroup.mk' (pCore 2 d.pairImage)
    (d.pairProjection (inclusion d.S_le_pairCentralizer s)) = 1 ↔ _
  rw [show (QuotientGroup.mk' (pCore 2 d.pairImage)
    (d.pairProjection (inclusion d.S_le_pairCentralizer s)) = 1) ↔
    d.pairProjection (inclusion d.S_le_pairCentralizer s) ∈ pCore 2 d.pairImage from
    QuotientGroup.eq_one_iff _]
  change inclusion d.S_le_pairCentralizer s ∈
    (pCore 2 d.pairImage).comap d.pairProjection ↔ _
  rw [hpre]
  have hs : inclusion d.S_le_pairCentralizer s ∈ pCore 2 d.pairCentralizer ↔
      (s : G) ∈ d.pairCentralizer.pCoreIn 2 := by
    exact (mem_map_iff_mem d.pairCentralizer.subtype_injective).symm
  rw [hs,d.pair_twoCore_eq_K_inf h]
  change ((s : G) ∈ d.K ∧ (s : G) ∈ d.pairCentralizer) ↔
    ((s : G) ∈ d.K ∧ (s : G) ∈ d.S)
  exact ⟨fun hs => ⟨hs.1,s.property⟩,fun hs => ⟨hs.1,d.S_le_pairCentralizer s.property⟩⟩

/-- The original S/R is the actual quotient of the pair image by its E32 core. -/
noncomputable def pointFactorEquiv (h : IsTypeJ4 z) :
    (d.S ⧸ d.R.subgroupOf d.S) ≃* (d.pairImage ⧸ pCore 2 d.pairImage) := by
  let f := QuotientGroup.lift (d.R.subgroupOf d.S) d.pointFactorMap
    (d.pointFactorMap_ker h).symm.le
  apply MulEquiv.ofBijective f
  apply (Nat.bijective_iff_injective_and_card f).mpr
  refine ⟨(QuotientGroup.injective_lift_iff _ _ _).mpr (d.pointFactorMap_ker h).symm,?_⟩
  rw [Nat.card_congr (d.SQuotientEquiv h).toEquiv,
    Nat.card_congr (d.pairImage_structure h).2.2.some.toEquiv]

@[simp] theorem pointFactorEquiv_mk (h : IsTypeJ4 z) (s : d.S) :
    d.pointFactorEquiv h (QuotientGroup.mk' _ s) =
      QuotientGroup.mk' (pCore 2 d.pairImage)
        (d.pairProjection (inclusion d.S_le_pairCentralizer s)) := rfl

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpaceData
end
