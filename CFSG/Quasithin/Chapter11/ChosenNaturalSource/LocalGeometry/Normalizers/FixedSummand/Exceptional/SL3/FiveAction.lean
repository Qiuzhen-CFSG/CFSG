module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.SL3.SecondLayer
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCoordinates
public import Theory.GroupTheory.PrimeOrderLift

/-!
# A fixed-free five-action on the two literal SL₃ sections

The marked point projection L₁ → F² ⋊ SL₂(F) induces the original lower
matrix block on V/V₁. An order-five element has nonidentity order-five
image in this block, since the kernel is O₂(L₁). The natural SL₂ fixed-vector
theorem makes its action fixed-free both on the seed image and on the
second factor. Equivariance of the literal section projection then makes
its action fixed-free on all of O₂(L₁)/Z(L₁).

At q=4 the actual PSL₂(4) quotient supplies an element of order five.
Its inner section action generates the required subgroup of order five.
The companion `Complete` module applies this subgroup to the Frattini
normalizer bound and the original exceptional GO contradiction.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766, the two natural chief factors in the SL₃(4) branch.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
open Matrix.PSL3.LinearThree Matrix.PSL3.PointRadicalGeneration
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (Coordinates.sl3 m))
    (a : SL(3,S.field.Carrier)) (ha : conjugatePoint standardPoint a = f.space 0)

def pointLinearProjection : f.Li 0 →* SL(2,S.field.Carrier) :=
  (SemidirectProduct.rightHom : Matrix.SL2.Affine S.field.Carrier →* _).comp
    ((pointLocalAffineEquiv S.field.Carrier).toMonoidHom.comp
      (pointProjection D S m f a ha))

theorem pointLinearProjection_kernel :
    (pointLinearProjection D S m f a ha).ker = pCore 2 (f.Li 0) := by
  change ((pointRadicalSL S.field.Carrier).comap (pointProjection D S m f a ha)) = _
  rw [←pointLocalSL_twoCore_eq]
  exact (pointProjection D S m f a ha).comap_pCore_of_ker_isPGroup
    (pointProjection_surjective D S m f a ha) (pointProjection_kernel_pgroup D S m f a ha)

def markedSeedEquiv : V ≃* Multiplicative (Fin 3 → S.field.Carrier) :=
  (LocalGeometry.SL3.naturalEquiv D S m).trans
    (SpecialLinearGroup.toLin' a).toAddEquiv.toMultiplicative

def seedPlaneMap : V →* Multiplicative (Fin 2 → S.field.Carrier) where
  toFun v := Multiplicative.ofAdd (fun i => (markedSeedEquiv D S m a v).toAdd i.succ)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext i
    simp [markedSeedEquiv]
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    ext i
    change (markedSeedEquiv D S m a (v*w)).toAdd i.succ = _
    rw [map_mul]
    rfl

include ha in
theorem seedPlaneMap_kernel :
    (seedPlaneMap D S m a).ker = (f.Vi 0).subgroupOf V := by
  ext v
  change (fun i : Fin 2 => (markedSeedEquiv D S m a v).toAdd i.succ) = 0 ↔ (v : G) ∈ (Coordinates.sl3 m).preimage (f.space 0)
  rw [(Coordinates.sl3 m).mem_preimage (f.space 0) v, ←ha,mem_conjugatePoint,mem_standardPoint]
  change (fun i : Fin 2 => (markedSeedEquiv D S m a v).toAdd i.succ) = 0 ↔
    (markedSeedEquiv D S m a v).toAdd 1 = 0 ∧ (markedSeedEquiv D S m a v).toAdd 2 = 0
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1⟩
  · rintro ⟨h1,h2⟩
    funext i
    fin_cases i <;> assumption

theorem markedSeedEquiv_conjugation (l : f.Li 0) (v : V) :
    (markedSeedEquiv D S m a (V.normalizerMonoidHom
      (inclusion (((localResidual_le _).trans inf_le_left).trans D.normalizes) l) v)).toAdd =
      (pointProjection D S m f a ha l).val.val *ᵥ (markedSeedEquiv D S m a v).toAdd := by
  let ρ := specialLinearNatural (k := S.field.Carrier) 3
  change ρ a ((LocalGeometry.SL3.naturalEquiv D S m
    (V.normalizerMonoidHom (inclusion D.normalizes
      (⟨l,((localResidual_le _).trans inf_le_left) l.property⟩ : L)) v)).toAdd) =
    ρ (a * PointCohomology.PointGeometry.SL3Core.componentMap D S m
      ⟨l,((localResidual_le _).trans inf_le_left) l.property⟩ * a⁻¹)
      (ρ a (LocalGeometry.SL3.naturalEquiv D S m v).toAdd)
  rw [LocalGeometry.SL3.naturalEquiv_conjugation]
  simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  rfl

theorem seedPlaneMap_conjugation (l : f.Li 0) (v : V) :
    (seedPlaneMap D S m a (V.normalizerMonoidHom
      (inclusion (((localResidual_le _).trans inf_le_left).trans D.normalizes) l) v)).toAdd =
      (pointLinearProjection D S m f a ha l).val *ᵥ (seedPlaneMap D S m a v).toAdd := by
  have he := markedSeedEquiv_conjugation D S m f a ha l v
  have hc := (mem_pointLocalSL_iff _ _).mp (pointProjection D S m f a ha l).property
  change (fun i : Fin 2 => (markedSeedEquiv D S m a _).toAdd i.succ) = _
  rw [he]
  change _ = (pointLocalAffineEquiv S.field.Carrier (pointProjection D S m f a ha l)).right.val *ᵥ _
  rw [pointLocalAffineEquiv_right_val]
  ext i
  fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two,
    seedPlaneMap, hc.2.1, hc.2.2]


theorem pointLinearProjection_order_five (b : f.Li 0) (hb : orderOf b = 5) :
    orderOf (pointLinearProjection D S m f a ha b) = 5 := by
  have hk : IsPGroup 2 (pointLinearProjection D S m f a ha).ker := by
    rw [pointLinearProjection_kernel]
    exact pCore_isPGroup
  exact ((pointLinearProjection D S m f a ha).orderOf_map_eq_of_coprime_of_isPGroup_ker
    hk b (by rw [hb]; decide)).trans hb

include ha in
private theorem seedPlane_eq_of_section_eq (v w : V)
    (h : seedSectionMap D S m f v = seedSectionMap D S m f w) :
    seedPlaneMap D S m a v = seedPlaneMap D S m a w := by
  have hd : v / w ∈ (seedSectionMap D S m f).ker := by
    change seedSectionMap D S m f (v / w) = 1
    rw [map_div,h,div_self']
  rw [seedSectionMap_ker, ←seedPlaneMap_kernel D S m f a ha] at hd
  change seedPlaneMap D S m a (v / w) = 1 at hd
  rwa [map_div,div_eq_one] at hd

include ha in
theorem seedSection_five_fixed (b : f.Li 0) (hb : orderOf b = 5) (v : V)
    (hfix : ChiefSection.innerAction (f.Li 0) b (seedSectionMap D S m f v) =
      seedSectionMap D S m f v) : seedSectionMap D S m f v = 1 := by
  rw [seedSectionMap_conjugation] at hfix
  have hp := congrArg Multiplicative.toAdd (seedPlane_eq_of_section_eq D S m f a ha _ _ hfix)
  rw [seedPlaneMap_conjugation D S m f a ha] at hp
  have hb5 := pointLinearProjection_order_five D S m f a ha b hb
  have hz := Matrix.SL2.odd_power_fixed_eq_zero (pointLinearProjection D S m f a ha b)
    5 (by decide) (hb5 ▸ pow_orderOf_eq_one _) (by intro h; simp [h] at hb5)
    (seedPlaneMap D S m a v).toAdd hp
  have hv : v ∈ (seedPlaneMap D S m a).ker := hz
  rw [seedPlaneMap_kernel D S m f a ha, ←seedSectionMap_ker D S m f] at hv
  exact hv

private theorem modelCore_five_fixed {F : Type*} [Field F] [Finite F] [CharP F 2]
    (t : pointLocalSL F) (ht : orderOf (pointLocalAffineEquiv F t).right = 5)
    (u : pCore 2 (pointLocalSL F))
    (hu : MulAut.characteristic (pCore 2 (pointLocalSL F)) (MulAut.conj t) u = u) :
    u = 1 := by
  let e := pointLocalAffineEquiv F
  have huR : (e u.val).right = 1 := by
    exact (pointLocalSL_twoCore_eq F).le u.property
  have huE : e u.val = SemidirectProduct.inl (e u.val).left := by
    apply SemidirectProduct.ext
    · rfl
    · exact huR
  have hc := congrArg e (congrArg Subtype.val hu)
  change e (t * u.val * t⁻¹) = e u.val at hc
  rw [map_mul,map_mul,map_inv,huE,Matrix.SL2.conjugate_inl] at hc
  have hf := SemidirectProduct.inl_injective hc
  have hz := Matrix.SL2.odd_power_fixed_eq_zero (e t).right 5 (by decide)
    (ht ▸ pow_orderOf_eq_one _) (by intro h; simp [e,h] at ht)
    (e u.val).left.toAdd (congrArg Multiplicative.toAdd hf)
  apply Subtype.ext
  apply e.injective
  change e u.val = e 1
  rw [map_one,huE]
  simpa only [map_one] using congrArg SemidirectProduct.inl (show (e u.val).left = 1 from hz)

include ha in
theorem coreCentralSection_five_fixed (hbshort : ChapterC.IsShort L)
    (b : f.Li 0) (hb : orderOf b = 5) (x : CoreCentralSection (f.Li 0))
    (hfix : ChiefSection.innerAction (f.Li 0) b x = x) : x = 1 := by
  have hf := congrArg (sectionPointProjection D S m f a ha) hfix
  rw [sectionPointProjection_conjugation] at hf
  have hz := modelCore_five_fixed (pointProjection D S m f a ha b)
    (pointLinearProjection_order_five D S m f a ha b hb)
    (sectionPointProjection D S m f a ha x) hf
  have hx : x ∈ (sectionPointProjection D S m f a ha).ker := hz
  rw [sectionPointProjection_kernel D S m f a ha hbshort] at hx
  obtain ⟨v,rfl⟩ := hx
  exact seedSection_five_fixed D S m f a ha b hb v hfix


theorem exists_first_order_five (hq : 2 ^ S.field.degree = 4) :
    ∃ b : f.Li 0, orderOf b = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hm := first_isPSL D S m f
  rw [hq] at hm
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨j⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hc : Nat.card (f.Li 0 ⧸ pCore 2 (f.Li 0)) = 60 := by
    rw [Nat.card_congr (e.trans j).toEquiv, nat_card_alternatingGroup]
    norm_num
  apply exists_prime_orderOf_dvd_card' 5
  apply dvd_trans (show 5 ∣ Nat.card (f.Li 0 ⧸ pCore 2 (f.Li 0)) by rw [hc]; decide)
  exact card_dvd_of_surjective (QuotientGroup.mk' (pCore 2 (f.Li 0)))
    (QuotientGroup.mk'_surjective _)

theorem exists_fixed_free_five (hbshort : ChapterC.IsShort L)
    (hq : 2 ^ S.field.degree = 4) :
    ∃ B : Subgroup (MulAut (CoreCentralSection (f.Li 0))),
      B ≤ (ChiefSection.innerAction (f.Li 0)).range ∧ Nat.card B = 5 ∧
      FixedPoints.subgroup B (CoreCentralSection (f.Li 0)) = ⊥ := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_standardPoint_conjugator (f.space 0) (f.dimension 0)
  obtain ⟨b,hb⟩ := exists_first_order_five D S m f hq
  let α := ChiefSection.innerAction (f.Li 0) b
  have hα : α ≠ 1 := by
    intro he
    have hr : (seedSectionMap D S m f).range = ⊥ := by
      apply bot_unique
      rintro _ ⟨v,rfl⟩
      apply mem_bot.mpr
      exact seedSection_five_fixed D S m f a ha b hb v (by
        change α _ = _
        rw [he]
        rfl)
    have hc := seedSectionMap_range_card D S m f
    rw [hr,card_bot,hq] at hc
    norm_num at hc
  have hα5 : orderOf α = 5 := by
    apply orderOf_eq_prime
    · change ChiefSection.innerAction (f.Li 0) b ^ 5 = 1
      rw [←map_pow, ←hb, pow_orderOf_eq_one, map_one]
    · exact hα
  refine ⟨zpowers α, zpowers_le.mpr ⟨b,rfl⟩, (Nat.card_zpowers α).trans hα5, ?_⟩
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  exact coreCentralSection_five_fixed D S m f a ha hbshort b hb x
    (hx ⟨α,mem_zpowers α⟩)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.SL3
