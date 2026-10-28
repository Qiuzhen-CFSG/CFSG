module

public import Theory.GroupTheory.Recognition.JankoFour.LocalHypotheses
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Index

/-!
# The marked core and the retained cubic extension

For a group of type J₄, the image of the center of Q = F*(C_G(z)) is
exactly ⟨z⟩. Characteristicity of this center gives N_G(Q) = C_G(z).
This identifies the plane subgroup by an intrinsic normalizer, without
assuming simplicity or a global order.

The preimage of the specified cubic kernel in C_G(z) is kept as an actual
normal subgroup. Its quotient by Q is identified with that same kernel,
and its order is 3 · 2¹³. The remaining quotient is the actual Aut(M₂₂).
We do not identify this preimage with an iterated core without proving the
necessary Mathieu quotient facts.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), 589–607, and the
exposition *The study of J₄ via the theory of uniqueness systems*, p.12.
These are intrinsic inputs to the still outstanding local subgroup
construction in (3.1), pp.16–17 of the exposition.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {z : G}

noncomputable def coreEquivAmbient (z : G) : core z ≃* ambientCore z :=
  (core z).equivMapOfInjective (centralizer z).subtype (centralizer z).subtype_injective

omit [Finite G] in
theorem ambientCore_le (z : G) : ambientCore z ≤ centralizer z :=
  map_subtype_le _

omit [Finite G] in
theorem ambientCore_subgroupOf (z : G) :
    (ambientCore z).subgroupOf (centralizer z) = core z := by
  exact comap_map_eq_self (by simp)

theorem core_center_image (h : IsTypeJ4 z) :
    ((center (core z)).map (core z).subtype).map (centralizer z).subtype = zpowers z := by
  let := h.extraspecial
  obtain ⟨q, hq, hqz⟩ := mem_map.mp (marker_mem_ambientCore z)
  change (q : G) = z at hqz
  have hqcenter : (⟨q, hq⟩ : core z) ∈ center (core z) := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    apply Subtype.ext
    change (a : centralizer z).val * q.val = q.val * (a : centralizer z).val
    rw [hqz]
    exact mem_centralizer_singleton_iff.mp (a : centralizer z).property
  have hzmem : z ∈ ((center (core z)).map (core z).subtype).map
      (centralizer z).subtype := by
    exact mem_map.mpr ⟨q, mem_map.mpr ⟨⟨q, hq⟩, hqcenter, rfl⟩, hqz⟩
  apply (eq_of_le_of_card_ge (zpowers_le.mpr hzmem) ?_).symm
  rw [card_map_of_injective (centralizer z).subtype_injective,
    card_map_of_injective (core z).subtype_injective,
    IsExtraspecial.center_order_p 2 (core z), Nat.card_zpowers, h.involution]

theorem ambientCore_center_image (h : IsTypeJ4 z) :
    (center (ambientCore z)).map (ambientCore z).subtype = zpowers z := by
  unfold ambientCore
  rw [← map_subgroup_center_eq (centralizer z).subtype
    (centralizer z).subtype_injective (core z)]
  exact core_center_image h

theorem normalizer_ambientCore (h : IsTypeJ4 z) :
    normalizer (ambientCore z : Set G) = centralizer z := by
  apply le_antisymm
  · exact normalizer_le_centralizer_of_characteristic_involution
      (ambientCore z) (center (ambientCore z)) z h.involution (ambientCore_center_image h)
  · apply (normal_subgroupOf_iff_le_normalizer (ambientCore_le z)).mp
    rw [ambientCore_subgroupOf]
    infer_instance

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry

open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.CubicLift
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))

noncomputable def projection : centralizer z →* MulAut Sporadic.Mathieu.M22 :=
  e.projection.comp (QuotientGroup.mk' (core z))

noncomputable def subgroup : Subgroup (centralizer z) := (projection e).ker

instance normal : (subgroup e).Normal := inferInstanceAs (projection e).ker.Normal

theorem projection_surjective : Function.Surjective (projection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective (core z))

theorem core_le : core z ≤ subgroup e := by
  intro q hq
  change e.projection (QuotientGroup.mk' (core z) q) = 1
  have he : QuotientGroup.mk' (core z) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
  rw [he, map_one]

noncomputable def toCubicKernel : subgroup e →* e.projection.ker where
  toFun q := ⟨QuotientGroup.mk' (core z) q.val, q.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a.val b.val)

theorem toCubicKernel_surjective : Function.Surjective (toCubicKernel e) := by
  intro q
  obtain ⟨c, hc⟩ := QuotientGroup.mk'_surjective (core z) q.val
  have hm : c ∈ subgroup e := by
    change e.projection (QuotientGroup.mk' (core z) c) = 1
    rw [hc]
    exact q.property
  exact ⟨⟨c, hm⟩, Subtype.ext hc⟩

theorem toCubicKernel_ker : (toCubicKernel e).ker = (core z).subgroupOf (subgroup e) := by
  ext q
  change (⟨QuotientGroup.mk' (core z) q.val, q.property⟩ : e.projection.ker) = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

noncomputable def quotientEquiv :
    (subgroup e ⧸ (core z).subgroupOf (subgroup e)) ≃* e.projection.ker :=
  (QuotientGroup.quotientMulEquivOfEq (toCubicKernel_ker e).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (toCubicKernel e) (toCubicKernel_surjective e))

theorem quotient_card : Nat.card (subgroup e ⧸ (core z).subgroupOf (subgroup e)) = 3 :=
  (Nat.card_congr (quotientEquiv e).toEquiv).trans e.kernel_card

theorem subgroup_card (h : IsTypeJ4 z) : Nat.card (subgroup e) = 3 * 2 ^ 13 := by
  rw [card_eq_card_quotient_mul_card_subgroup ((core z).subgroupOf (subgroup e)), quotient_card]
  have he : Nat.card ((core z).subgroupOf (subgroup e)) = Nat.card (core z) := by
    rw [← card_map_of_injective (subgroup e).subtype_injective,
      map_subgroupOf_eq_of_le (core_le e)]
  rw [he, h.core_card]

noncomputable def automorphismQuotientEquiv :
    (centralizer z ⧸ subgroup e) ≃* MulAut Sporadic.Mathieu.M22 :=
  QuotientGroup.quotientKerEquivOfSurjective (projection e) (projection_surjective e)

end Theory.GroupTheory.Recognition.JankoFour.LocalGeometry.CubicLift
