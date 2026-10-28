module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.TwoCentralSubspace.Action
public import Theory.SpecificGroups.BinaryLinear.SixSylowActors.Defs

/-!
# The intrinsic binary-linear action configuration

The embedded subgroup is the original X inside Y, with its given A₆
isomorphism. Every induced V-actor preserves it and fixes the transported
Sylow subgroup pointwise. Its pointwise fixer on X is exactly the image
of A, hence has order two and is genuinely outer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory MulAction
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G}

omit [Finite G] in
/-- The pointwise fixer of the embedded A₆ is exactly the given outer action of A. -/
theorem EscapeConfiguration.six_fixer [IsElementaryAbelian 2 V]
    {g : G} (c : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    actionImage V Y ⊓ fixingSubgroup (MulAut Y) (X.subgroupOf Y : Set Y) =
      actionImage A Y := by
  have hn := hY.normalized_by_V c.subspace_mem.1
  ext a
  constructor
  · rintro ⟨ha, hf⟩
    rw [actionImage_eq_range hn] at ha
    obtain ⟨v, rfl⟩ := ha
    have hvA : (v : G) ∈ A := by
      rw [← c.six.fixed]
      refine ⟨v.property, mem_centralizer_iff.mpr ?_⟩
      intro x hx
      have he := congrArg Subtype.val ((mem_fixingSubgroup_iff (MulAut Y)).mp hf
        (⟨x, hY.proper.le hx⟩ : Y) hx)
      change (v : G) * x * (v : G)⁻¹ = x at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    exact ⟨inclusion hn v, hvA, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨⟨a, c.subspace_mem.1 ha, rfl⟩, ?_⟩
    apply (mem_fixingSubgroup_iff (MulAut Y)).mpr
    intro x hx
    apply Subtype.ext
    change (a : G) * (x : G) * (a : G)⁻¹ = x
    exact mul_inv_eq_iff_eq_mul.mpr (c.six.component.1 hx a ha)

/-- All premises of the remaining intrinsic model calculation come from the source setup. -/
theorem EscapeConfiguration.model_configuration [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {g : G} (c : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) (hm : LinearModelAction A Y) :
    BinaryLinear.SixSylowActors.Configuration (actionImage V Y) (X.subgroupOf Y) := by
  have hn := hY.normalized_by_V c.subspace_mem.1
  obtain ⟨hNX, R, hR⟩ := c.six_sylow_action h
  let e : X.subgroupOf Y ≃* X := subgroupOfEquivOfLe hY.proper.le
  refine ⟨elementary_actionImage hn, c.card_actionImage_V hY hm, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨f⟩ := c.six.model
    exact ⟨e.trans f⟩
  · intro a ha
    rw [actionImage_eq_range hn] at ha
    obtain ⟨v, rfl⟩ := ha
    have hstable (w : V) (x : Y) (hx : x ∈ X.subgroupOf Y) :
        Y.normalizerMonoidHom (inclusion hn w) x ∈ X.subgroupOf Y := by
      have he := mem_normalizer_iff_map_conj_eq.mp (hNX w.property)
      change (MulAut.conj (w : G)) (x : G) ∈ X
      rw [← he]
      exact mem_map_of_mem (MulAut.conj (w : G)).toMonoidHom hx
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hstable v y hy
    · intro hx
      refine ⟨Y.normalizerMonoidHom (inclusion hn (v⁻¹)) x, hstable (v⁻¹) x hx, ?_⟩
      change (Y.normalizerMonoidHom.comp (inclusion hn)) v
        ((Y.normalizerMonoidHom.comp (inclusion hn)) (v⁻¹) x) = x
      rw [map_inv]
      exact MulEquiv.apply_symm_apply _ _
  · rw [c.six_fixer hY]
    exact hm.order_two
  · rw [c.six_fixer hY]
    exact hm.outer
  · refine ⟨R.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_⟩
    intro a ha x hx
    rw [actionImage_eq_range hn] at ha
    obtain ⟨v, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hx
    apply Subtype.ext
    change (v : G) * (y : G) * (v : G)⁻¹ = y
    exact mul_inv_eq_iff_eq_mul.mpr (hR (mem_map_of_mem X.subtype hy) v v.property)

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms
