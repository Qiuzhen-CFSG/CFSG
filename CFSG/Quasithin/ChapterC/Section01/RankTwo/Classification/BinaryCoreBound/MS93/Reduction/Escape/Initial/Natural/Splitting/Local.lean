module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Actions

/-!
# The actual local radius head and a small involution

The carrier is V_a / (Z_a[V_a,Q_a]), formed inside the finite vertex
stabilizer. The action descends through its genuine surjective projection
onto SL₃(2), with kernel Q_a. Elementary abelianness follows from the
already proved elementary quotient V_a/Z_a.

The critical endpoint's entire displacement image has order at most two.
A nonidentity element of its projected elementary subgroup therefore gives
an involution with that bound on this particular carrier. This does not
assert that the action is faithful: excluding trivial action on the head
remains a geometric obligation. The authorized triple-commutator premise
is separately transported to the local stabilizer.

Source: Meierfrankenfeld--Stellmacher (1993), notation p.881,
(4.3.1)(iii) and its proof on pp.882--883.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] {R : Subgroup M}

noncomputable abbrev localRadius (a : Vertex R) := (V R a).subgroupOf (stabilizer R a)
noncomputable abbrev localZ (a : Vertex R) := (Z R a).subgroupOf (stabilizer R a)
abbrev localKernel (a : Vertex R) := (Q R a).subgroupOf (stabilizer R a)
noncomputable abbrev localRadical (a : Vertex R) := radicalPreimage (localKernel a) (localRadius a) (localZ a)

instance localRadius_normal (a : Vertex R) : (localRadius a).Normal := radius_normal a
instance localKernel_normal (a : Vertex R) : (localKernel a).Normal := Q_normal R a

theorem localRadical_normal (geometry : Geometry R) (a : Vertex R) :
    (localRadical a).Normal := by
  let := geometry.Z_normal a
  exact radical_normal _ _ _

def RadiusHead (_geometry : Geometry R) (a : Vertex R) : Type _ :=
  localRadius a ⧸ (localRadical a).subgroupOf (localRadius a)

noncomputable instance radiusHead_group (geometry : Geometry R) (a : Vertex R) :
    Group (RadiusHead geometry a) := by
  let := localRadical_normal geometry a
  unfold RadiusHead
  infer_instance

noncomputable def radiusHeadProjection (geometry : Geometry R) (a : Vertex R) :
    localRadius a →* RadiusHead geometry a := by
  let := localRadical_normal geometry a
  exact QuotientGroup.mk' _

variable [Finite M] {L : Subgroup M}

noncomputable def localProjection (source : LocalSource L R) (a : Vertex R)
    (ha : color R a = false) : stabilizer R a →* SL :=
  (exists_localProjection source a ha).choose

theorem localProjection_surjective (source : LocalSource L R) (a : Vertex R)
    (ha : color R a = false) : Function.Surjective (localProjection source a ha) :=
  (exists_localProjection source a ha).choose_spec.1

theorem localProjection_kernel (source : LocalSource L R) (a : Vertex R)
    (ha : color R a = false) : (localProjection source a ha).ker = localKernel a :=
  (exists_localProjection source a ha).choose_spec.2

noncomputable def radiusHeadAction (source : LocalSource L R) (geometry : Geometry R)
    (a : Vertex R) (ha : color R a = false) : SL →* MulAut (RadiusHead geometry a) := by
  let := geometry.Z_normal a
  exact headAction (localRadius a) (localZ a) (localKernel a)
    (localProjection source a ha) (localProjection_surjective source a ha)
    (localProjection_kernel source a ha)

theorem radiusHeadAction_apply (source : LocalSource L R) (geometry : Geometry R)
    (a : Vertex R) (ha : color R a = false) (g : stabilizer R a) (v : localRadius a) :
    radiusHeadAction source geometry a ha (localProjection source a ha g)
      (radiusHeadProjection geometry a v) =
    radiusHeadProjection geometry a
      ⟨g * (v : stabilizer R a) * g⁻¹,
        (inferInstance : (localRadius a).Normal).conj_mem v v.property g⟩ := by
  let := geometry.Z_normal a
  exact headAction_apply (localRadius a) (localZ a) (localKernel a)
    (localProjection source a ha) (localProjection_surjective source a ha)
    (localProjection_kernel source a ha) g v

instance radiusHead_finite (geometry : Geometry R) (a : Vertex R) :
    Finite (RadiusHead geometry a) := by
  let := finite_stabilizer R a
  unfold RadiusHead
  infer_instance

theorem radiusHead_elementary (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    IsElementaryAbelian 2 (RadiusHead geometry a) := by
  let := geometry.Z_normal a
  let : IsElementaryAbelian 2 (localRadius a ⧸ (localZ a).subgroupOf (localRadius a)) :=
    elementary_radius_quotient source geometry hb modules a ha
  exact radical_elementary (localRadius a) (localZ a) (localKernel a)

/-- The endpoint acts on the actual head through the specified projection.
The whole endpoint displacement, not merely one selected vector, has order
at most two. -/
theorem endpoint_small_displacement (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) :
    Nat.card (commutatorAction
      (((Z R p.a').subgroupOf (stabilizer R p.a)).map
        ((radiusHeadAction source geometry p.a p.color_a).comp
          (localProjection source p.a p.color_a)))
      (RadiusHead geometry p.a)) ≤ 2 := by
  let S := stabilizer R p.a
  let H := localRadius p.a
  let N := localZ p.a
  let Q₀ := localKernel p.a
  let T := (Z R p.a').subgroupOf S
  let := geometry.Z_normal p.a
  let := finite_stabilizer R p.a
  change Nat.card (commutatorAction (T.map
    ((headAction H N Q₀ (localProjection source p.a p.color_a)
      (localProjection_surjective source p.a p.color_a)
      (localProjection_kernel source p.a p.color_a)).comp
        (localProjection source p.a p.color_a)))
      (H ⧸ (radicalPreimage Q₀ H N).subgroupOf H)) ≤ 2
  rw [headAction_comp, quotientAction_displacement_card]
  have hV : V R p.a ≤ S :=
    (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hT : Z R p.a' ≤ S :=
    (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).2
  have hmap : ⁅H, T⁆.map S.subtype = radiusCommutator p.a p.a' := by
    rw [map_commutator, map_subgroupOf_eq_of_le hV, map_subgroupOf_eq_of_le hT]
    rfl
  have hi := relIndex_map_map_of_injective N ⁅H, T⁆ S.subtype_injective
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R p.a), hmap] at hi
  have hsmall : N.relIndex ⁅H, T⁆ ≤ 2 := by
    rw [← hi]
    exact radius_quotient_image_le_two p source hb modules
  exact (relIndex_le_of_le_left (show N ≤ radicalPreimage Q₀ H N from le_sup_left)
    (by exact index_ne_zero_of_finite)).trans hsmall

/-- Criticality supplies an actual nonidentity involution of the marked SL₃
quotient. Its displacement on the head inherits the endpoint bound. -/
theorem radiusHead_small_involution (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) :
    HasSmallInvolution (radiusHeadAction source geometry p.a p.color_a) := by
  let S := stabilizer R p.a
  let π := localProjection source p.a p.color_a
  let ρ := radiusHeadAction source geometry p.a p.color_a
  have hrev := source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hrev.2
  have hzS := (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).2 hz
  let g : S := ⟨z, hzS⟩
  have hne : π g ≠ 1 := by
    intro he
    have hk : g ∈ π.ker := he
    rw [localProjection_kernel] at hk
    exact hzQ hk
  have htwo : (π g) ^ 2 = 1 := by
    let := geometry.Z_elementary (by omega) p.a' p.end_color
    have he : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz
    rw [← map_pow, show g ^ 2 = 1 from Subtype.ext he, map_one]
  refine ⟨π g, hne, htwo, ?_⟩
  have hmem : ρ (π g) ∈ ((Z R p.a').subgroupOf S).map (ρ.comp π) :=
    mem_map_of_mem (ρ.comp π) hz
  have hle := displacement_mono (zpowers_le.mpr hmem)
  exact (card_le_of_le hle).trans (endpoint_small_displacement source geometry hb modules p)

/-- Transport the authorized ambient triple bound into the local stabilizer. -/
theorem local_triple (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false)
    (htriple : ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a) :
    ⁅⁅localRadius a, localKernel a⁆, pResidual 2 (stabilizer R a)⁆ ≤ localZ a := by
  apply map_le_iff_le_comap.mp
  rw [map_commutator, map_commutator,
    map_subgroupOf_eq_of_le ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)),
    map_subgroupOf_eq_of_le (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)]
  exact htriple

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
