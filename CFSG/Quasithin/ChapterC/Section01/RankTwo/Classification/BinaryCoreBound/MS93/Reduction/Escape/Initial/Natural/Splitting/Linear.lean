module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Natural.Splitting.Local

/-!
# The literal dual radius module

Conjugation on V_a/Z_a is linearized over GF(2), using the proved elementary
abelian quotient. Its contragredient is the actual module mentioned in the
source. The endpoint displacement bound is proved on this quotient before
passing to its dual or to V_a/(Z_a[V_a,Q_a]). The latter has its own specified
SL₃(2) action and linearization.

No constituent recognition, extension splitting or faithfulness is assumed
or asserted by these definitions.

Source: Meierfrankenfeld--Stellmacher (1993), (4.3.1)(iii), p.883,
citing (1.4)--(1.5), pp.842--843.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] {R : Subgroup M}

def RadiusQuotient (_geometry : Geometry R) (a : Vertex R) : Type _ :=
  localRadius a ⧸ (localZ a).subgroupOf (localRadius a)

noncomputable instance radiusQuotient_group (geometry : Geometry R) (a : Vertex R) :
    Group (RadiusQuotient geometry a) := by
  let := geometry.Z_normal a
  unfold RadiusQuotient
  infer_instance

noncomputable def radiusQuotientProjection (geometry : Geometry R) (a : Vertex R) :
    localRadius a →* RadiusQuotient geometry a := by
  let := geometry.Z_normal a
  exact QuotientGroup.mk' _

noncomputable def radiusQuotientAction (geometry : Geometry R) (a : Vertex R) :
    stabilizer R a →* MulAut (RadiusQuotient geometry a) := by
  let := geometry.Z_normal a
  exact quotientAction (localRadius a) (localZ a)

theorem radiusQuotientAction_apply (geometry : Geometry R) (a : Vertex R)
    (g : stabilizer R a) (v : localRadius a) :
    radiusQuotientAction geometry a g (radiusQuotientProjection geometry a v) =
      radiusQuotientProjection geometry a
        ⟨g * (v : stabilizer R a) * g⁻¹,
          (inferInstance : (localRadius a).Normal).conj_mem v v.property g⟩ := by
  let := geometry.Z_normal a
  exact quotientAction_apply (localRadius a) (localZ a) g v

variable [Finite M] {L : Subgroup M}

instance radiusQuotient_finite (geometry : Geometry R) (a : Vertex R) :
    Finite (RadiusQuotient geometry a) := by
  let := finite_stabilizer R a
  unfold RadiusQuotient
  infer_instance

theorem radiusQuotient_elementary (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    IsElementaryAbelian 2 (RadiusQuotient geometry a) :=
  elementary_radius_quotient source geometry hb modules a ha

/-- The small displacement bound on V_a/Z_a itself, before quotienting
by the Q-action or passing to the contragredient. -/
theorem radiusQuotient_small_displacement (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry) :
    Nat.card (commutatorAction
      (((Z R p.a').subgroupOf (stabilizer R p.a)).map
        (radiusQuotientAction geometry p.a)) (RadiusQuotient geometry p.a)) ≤ 2 := by
  let S := stabilizer R p.a
  let := geometry.Z_normal p.a
  let := finite_stabilizer R p.a
  change Nat.card (commutatorAction
    (((Z R p.a').subgroupOf S).map (quotientAction (localRadius p.a) (localZ p.a)))
      (localRadius p.a ⧸ (localZ p.a).subgroupOf (localRadius p.a))) ≤ 2
  rw [quotientAction_displacement_card]
  have hV : V R p.a ≤ S :=
    (geometry.V_le_Q hb p.a p.color_a).trans (fun _ hx => hx.1)
  have hT : Z R p.a' ≤ S :=
    (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).2
  have hi := relIndex_map_map_of_injective (localZ p.a)
    ⁅localRadius p.a, (Z R p.a').subgroupOf S⁆ S.subtype_injective
  rw [map_subgroupOf_eq_of_le (Z_le_stabilizer R p.a), map_commutator,
    map_subgroupOf_eq_of_le hV, map_subgroupOf_eq_of_le hT] at hi
  rw [← hi]
  exact radius_quotient_image_le_two p source hb modules

/-- The actual binary linear action on V_a/Z_a, before killing [V_a,Q_a]. -/
noncomputable def radiusLinear (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    letI := radiusQuotient_elementary source geometry hb modules a ha
    Representation (ZMod 2) (stabilizer R a) (Additive (RadiusQuotient geometry a)) := by
  letI := radiusQuotient_elementary source geometry hb modules a ha
  exact Offenders.linearize (radiusQuotientAction geometry a)

/-- The literal contragredient used by the source's (1.4)--(1.5) argument. -/
noncomputable def radiusDual (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    letI := radiusQuotient_elementary source geometry hb modules a ha
    Representation (ZMod 2) (stabilizer R a)
      (Module.Dual (ZMod 2) (Additive (RadiusQuotient geometry a))) := by
  letI := radiusQuotient_elementary source geometry hb modules a ha
  exact (radiusLinear source geometry hb modules a ha).dual

/-- Linearization of the actual SL₃(2) action after killing the Q-action. -/
noncomputable def radiusHeadLinear (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (a : Vertex R) (ha : color R a = false) :
    letI := radiusHead_elementary source geometry hb modules a ha
    Representation (ZMod 2) SL (Additive (RadiusHead geometry a)) := by
  letI := radiusHead_elementary source geometry hb modules a ha
  exact Offenders.linearize (radiusHeadAction source geometry a ha)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Natural.Splitting
