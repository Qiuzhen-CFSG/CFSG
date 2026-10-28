module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.PSL3Two.SmallModules
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The original natural marking for the local endgame

The original L/O₂(L) natural marking gives a fixed surjection qL onto the
actual matrix SL₃(2), with exactly O₂(L) as kernel. Its original coordinates
on V intertwine that map. The Ru1 natural section uses these same coordinates;
the later Steinberg action must use this same qL.

No inclusion of an actor-normalized module into its actor is inferred.
The natural coordinates require only normalization; the natural section
requires the explicitly supplied containment V ≤ L.

Source: Aschbacher–Smith, Hypothesis 12.8.1 and 14.7.72–75,
printed pp.849 and 1076–1078, manuscript of 1 March 2004.
-/

public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] (d : Data T L V F W)

noncomputable def qL : L →* BinaryLinearThree.Group := by
  let := d.natural.chosen.elementary
  exact (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.toMonoidHom.comp
    (d.natural.naturalMarking.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

/-- Changing auxiliary H-module coordinates preserves the original L quotient
whenever the chosen natural L-action is unchanged. The implementation of qL
remains private; clients use this equality to transport actual sections. -/
theorem qL_eq_of_natural_eq (e : Data T L V F W) (h : d.natural = e.natural) :
    d.qL = e.qL := by
  unfold qL
  rw [h]

theorem qL_surjective : Function.Surjective d.qL := by
  let := d.natural.chosen.elementary
  exact (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.surjective.comp
    (d.natural.naturalMarking.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))

theorem qL_ker : d.qL.ker = (L.pCoreIn 2).subgroupOf L := by
  let := d.natural.chosen.elementary
  ext l
  change (BinaryLinear.OuterCyclic.slEquivLinear 3).symm
    (d.natural.naturalMarking.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) = 1 ↔ _
  rw [← (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.map_one,
    (BinaryLinear.OuterCyclic.slEquivLinear 3).symm.injective.eq_iff,
    ← d.natural.naturalMarking.quotientEquiv.map_one,
    d.natural.naturalMarking.quotientEquiv.injective.eq_iff,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact (mem_map_iff_mem L.subtype_injective).symm

/-- The original natural coordinates, without a containment assumption on V. -/
noncomputable def naturalCoordinates : V →* Multiplicative BinaryLinearThree.Vector := by
  let := d.natural.chosen.elementary
  let c := d.natural.naturalMarking.coordinates
  exact {
    toFun := fun v => Multiplicative.ofAdd (c (Additive.ofMul v))
    map_one' := c.map_zero
    map_mul' x y := c.map_add (Additive.ofMul x) (Additive.ofMul y) }

theorem naturalCoordinates_bijective : Function.Bijective d.naturalCoordinates := by
  let := d.natural.chosen.elementary
  exact d.natural.naturalMarking.coordinates.bijective

theorem naturalCoordinates_equivariant (l : L) (v : V) :
    (d.naturalCoordinates ⟨l * v * (l : G)⁻¹,
      (mem_normalizer_iff.mp (d.natural.chosen.normalizes l.property) v).mp v.property⟩).toAdd =
      BinaryLinearThree.W (d.qL l) (d.naturalCoordinates v).toAdd := by
  let := d.natural.chosen.elementary
  let c := d.natural.naturalMarking.coordinates
  have h := d.natural.naturalMarking.equivariant l (Additive.ofMul v)
  change c _ = BinaryLinearThree.W (d.qL l) (c (Additive.ofMul v))
  change c _ = _ at h
  exact h.trans (by
    change _ = ((d.qL l).val.mulVec (c (Additive.ofMul v)))
    rw [← BinaryLinear.OuterCyclic.slEquivLinear_apply]
    simp only [qL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
    rfl)

/-- Natural part of Ru1, with the same quotient marking used in the endgame. -/
noncomputable def natural_section (hVL : V ≤ L) :
    BinaryConjugationSection L V ⊥ (BinaryLinearThree.W.comp d.qL) where
  section_le := hVL
  kernel_le := bot_le
  normalized := d.natural.chosen.normalizes
  coordinates := d.naturalCoordinates
  onto := d.naturalCoordinates_bijective.2
  kernel_eq := by
    rw [d.naturalCoordinates.ker_eq_bot d.naturalCoordinates_bijective.1, bot_subgroupOf]
  equivariant := d.naturalCoordinates_equivariant

/-- The image of the original T ∩ L is a Sylow subgroup of the marked quotient. -/
theorem source_sylow_image (hTL : (T : Subgroup G) ≤ normalizer L) :
    ∃ P : Sylow 2 BinaryLinearThree.Group,
      (d.qL.comp (Subgroup.inclusion
        (inf_le_right : (T : Subgroup G) ⊓ L ≤ L))).range = (P : Subgroup _) := by
  let N := normalizer (L : Set G)
  let LN := L.subgroupOf N
  let : LN.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨S,hS⟩ := (T.subtype hTL).exists_subgroupOf_eq_of_normal LN
  let e : LN ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let S' : Sylow 2 L := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup L) = (T : Subgroup G).subgroupOf L := by
    ext l
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hS] at hx
      exact hx
    · intro hl
      refine ⟨e.symm l,?_,e.apply_symm_apply l⟩
      rw [hS]
      exact hl
  refine ⟨S'.mapSurjective d.qL_surjective, ?_⟩
  rw [Sylow.coe_mapSurjective, hS']
  ext g
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨⟨x,x.property.2⟩,x.property.1,hx⟩
  · rintro ⟨l,hl,he⟩
    exact ⟨⟨l,hl,l.property⟩,he⟩


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
