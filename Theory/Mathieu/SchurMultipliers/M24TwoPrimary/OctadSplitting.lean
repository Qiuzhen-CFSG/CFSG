module

public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.Reduction
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.OctadSplitting.Alternating
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.OctadSplitting.InvariantComplement

/-!
# Splitting native octad double extensions

A normal subgroup mapping isomorphically onto the pointwise octad kernel can
be factored out of the extension. The resulting projection is onto the actual
eight-point alternating group, retains the original central kernel, and retains
the involutory root lift. The alternating splitting test then gives a section.
Its range pulls back to a subgroup mapping isomorphically onto the native octad
stabilizer, so the original projection has a literal homomorphic section.

For an elementary preimage of the pointwise kernel, the dual natural-module
calculation of I.1.6(6) constructs this normal complement. Thus an involutory
root lift splits the original central double extension, without assuming a
section of the native octad stabilizer itself.

Source: Aschbacher–Smith I.1.3 and I.1.6(6), printed pp.407–408; GLS3 §6.1
and the native E₁₆.A₈ subgroup in Table 5.3e.
-/

public section
open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore
namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
noncomputable section

/-- The alternating quotient has exactly the specified pointwise kernel. -/
theorem octad_alternating_kernel : alternatingAction.ker = octadKernel := by
  ext g
  change alternatingAction g = 1 ↔ action seedOctad g = 1
  simp only [Subtype.ext_iff, alternatingAction_coe, Subgroup.coe_one]

variable {L : Type*} [Group L] (q : L →* OctadGroup)

/-- Quotient by a normal lift of the pointwise octad kernel. -/
def octadQuotientProjection (T : Subgroup L) [T.Normal]
    (hT : T.map q = octadKernel) : (L ⧸ T) →* alternatingGroup seedOctad.val :=
  QuotientGroup.lift T (alternatingAction.comp q) (by
    intro t ht
    have hm : q t ∈ octadKernel := hT ▸ (show q t ∈ T.map q from ⟨t, ht, rfl⟩)
    rw [← octad_alternating_kernel] at hm
    exact hm)

@[simp] theorem octadQuotientProjection_mk (T : Subgroup L) [T.Normal]
    (hT : T.map q = octadKernel) (x : L) :
    octadQuotientProjection q T hT (QuotientGroup.mk' T x) = alternatingAction (q x) := by
  rfl

theorem octadQuotientProjection_surjective (hq : Function.Surjective q)
    (T : Subgroup L) [T.Normal] (hT : T.map q = octadKernel) :
    Function.Surjective (octadQuotientProjection q T hT) :=
  QuotientGroup.lift_surjective_of_surjective T _
    (alternatingAction_surjective.comp hq) _

/-- The quotient kernel is the image of the original central kernel. -/
theorem octadQuotientProjection_kernel (T : Subgroup L) [T.Normal]
    (hT : T.map q = octadKernel) :
    (octadQuotientProjection q T hT).ker = q.ker.map (QuotientGroup.mk' T) := by
  let π := QuotientGroup.mk' T
  ext y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T y
  constructor
  · intro hx
    have hxK : q x ∈ octadKernel := by
      rw [← octad_alternating_kernel]
      exact hx
    rw [← hT] at hxK
    obtain ⟨t, ht, htx⟩ := hxK
    refine ⟨x * t⁻¹, ?_, ?_⟩
    · change q (x * t⁻¹) = 1
      rw [map_mul, map_inv, htx, mul_inv_cancel]
    · have ht1 : π t = 1 := (QuotientGroup.eq_one_iff t).mpr ht
      change π (x * t⁻¹) = π x
      rw [map_mul, map_inv, ht1, inv_one, mul_one]
  · rintro ⟨z, hz, he⟩
    rw [← he]
    change alternatingAction (q z) = 1
    rw [show q z = 1 from hz, map_one]

/-- Disjointness retains the original kernel order after quotienting. -/
theorem octadQuotientProjection_kernel_card (T : Subgroup L) [T.Normal]
    (hT : T.map q = octadKernel) (hd : Disjoint q.ker T) :
    Nat.card (octadQuotientProjection q T hT).ker = Nat.card q.ker := by
  rw [octadQuotientProjection_kernel]
  let π := QuotientGroup.mk' T
  let k := π.subgroupMap q.ker
  have hi : Function.Injective k := by
    apply k.ker_eq_bot_iff.mp
    apply bot_unique
    intro z hz
    apply Subtype.ext
    have hzT : z.val ∈ T := (QuotientGroup.eq_one_iff z.val).mp
      (congrArg Subtype.val hz)
    exact disjoint_def.mp hd z.property hzT
  exact (Nat.card_congr (MulEquiv.ofBijective k
    ⟨hi, π.subgroupMap_surjective q.ker⟩).toEquiv).symm

/-- Centrality is retained by the same literal quotient projection. -/
theorem octadQuotientProjection_kernel_central (hc : q.ker ≤ center L)
    (T : Subgroup L) [T.Normal] (hT : T.map q = octadKernel) :
    (octadQuotientProjection q T hT).ker ≤ center (L ⧸ T) := by
  rw [octadQuotientProjection_kernel]
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_center_iff]
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective T y
  simpa only [map_mul] using congrArg (QuotientGroup.mk' T)
    (mem_center_iff.mp (hc hz) x)

/-- A section after quotienting by a normal kernel lift gives a section of the
original octad projection. No section of the native octad stabilizer is assumed. -/
theorem octad_section_of_quotient_section (hq : Function.Surjective q)
    (T : Subgroup L) [T.Normal] (hT : T.map q = octadKernel)
    (hd : Disjoint q.ker T)
    (s : alternatingGroup seedOctad.val →* (L ⧸ T))
    (hs : (octadQuotientProjection q T hT).comp s = MonoidHom.id _) :
    ∃ r : OctadGroup →* L, q.comp r = MonoidHom.id _ := by
  let π := QuotientGroup.mk' T
  let p := octadQuotientProjection q T hT
  have hps (a : alternatingGroup seedOctad.val) : p (s a) = a :=
    DFunLike.congr_fun hs a
  let H := s.range.comap π
  let qH := q.comp H.subtype
  have hi : Function.Injective qH := by
    apply qH.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hxq : q x.val = 1 := hx
    obtain ⟨a, ha⟩ := x.property
    have ha1 : a = 1 := by
      rw [← hps a, ha]
      change alternatingAction (q x.val) = 1
      rw [hxq, map_one]
    have hπx : π x.val = 1 := by rw [← ha, ha1, map_one]
    have hxT : x.val ∈ T := (QuotientGroup.eq_one_iff x.val).mp hπx
    exact Subtype.ext (disjoint_def.mp hd hx hxT)
  have hsur : Function.Surjective qH := by
    intro g
    obtain ⟨x, hx⟩ := hq g
    have hw : π x * (s (alternatingAction g))⁻¹ ∈ p.ker := by
      change p (π x * (s (alternatingAction g))⁻¹) = 1
      rw [map_mul, map_inv, hps]
      change alternatingAction (q x) * (alternatingAction g)⁻¹ = 1
      rw [hx, mul_inv_cancel]
    rw [octadQuotientProjection_kernel] at hw
    obtain ⟨z, hz, he⟩ := hw
    refine ⟨⟨z⁻¹ * x, ?_⟩, ?_⟩
    · change π (z⁻¹ * x) ∈ s.range
      refine ⟨alternatingAction g, ?_⟩
      rw [map_mul, map_inv, he]
      group
    · change q (z⁻¹ * x) = g
      rw [map_mul, map_inv, show q z = 1 from hz, inv_one, one_mul, hx]
  let e : H ≃* OctadGroup := MulEquiv.ofBijective qH ⟨hi, hsur⟩
  refine ⟨H.subtype.comp e.symm.toMonoidHom, ?_⟩
  exact MonoidHom.ext (fun g => e.apply_symm_apply g)

/-- The alternating double-cover calculation completes splitting once the
invariant translation complement has been constructed. -/
theorem octad_double_extension_section_of_normal_complement [Finite L]
    (hq : Function.Surjective q) (hc : q.ker ≤ center L)
    (hcard : Nat.card q.ker = 2) (hroot : HasInvolutoryRoot q)
    (T : Subgroup L) [T.Normal] (hT : T.map q = octadKernel)
    (hd : Disjoint q.ker T) :
    ∃ s : OctadGroup →* L, q.comp s = MonoidHom.id OctadGroup := by
  let p := octadQuotientProjection q T hT
  obtain ⟨x, hx, hrootx⟩ := hroot
  have hxroot : (p (QuotientGroup.mk' T x)).val.cycleType = {2, 2} := by
    rw [octadQuotientProjection_mk, alternatingAction_coe]
    exact hrootx
  obtain ⟨s, hs⟩ := alternating_octad_section
    (by simpa only [Nat.card_eq_fintype_card] using seed_card) p
    (octadQuotientProjection_surjective q hq T hT)
    (octadQuotientProjection_kernel_central q hc T hT)
    ((octadQuotientProjection_kernel_card q T hT hd).trans hcard)
    (QuotientGroup.mk' T x) (by rw [← map_pow, hx, map_one]) hxroot
  exact octad_section_of_quotient_section q hq T hT hd s hs

/-- An elementary preimage of the pointwise octad kernel and an involutory
double-transposition lift split a central double extension of the native
octad stabilizer. -/
theorem octad_double_extension_section [Finite L]
    (hq : Function.Surjective q) (hc : q.ker ≤ center L)
    (hcard : Nat.card q.ker = 2) (helem : ElementaryKernelPreimage q)
    (hroot : HasInvolutoryRoot q) :
    ∃ s : OctadGroup →* L, q.comp s = MonoidHom.id OctadGroup := by
  obtain ⟨T, hnormal, hd, hT⟩ := octad_invariant_kernel_complement q hq hc hcard helem
  let : T.Normal := hnormal
  exact octad_double_extension_section_of_normal_complement q hq hc hcard hroot T hT hd

end
end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
